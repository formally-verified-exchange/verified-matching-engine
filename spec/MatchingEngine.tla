--------------------------- MODULE MatchingEngine ---------------------------
(***************************************************************************)
(* TLA+ formalization of a Price-Time Priority Matching Engine.            *)
(* Translated from matching-engine-formal-spec.md v1.2.0                  *)
(* Purpose: Adversarial verification — stress-test the spec for           *)
(* internal consistency and emergent edge cases.                           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    PRICES,        \* Set of valid prices, e.g. {1, 2, 3}
    MAX_QTY,       \* Maximum order quantity (e.g. 2 or 3)
    MAX_ORDERS,    \* Maximum total orders ever submitted
    TICK_SIZE,     \* Minimum price increment (for post-only reprice)
    MAX_CLOCK,     \* Maximum clock value (bounds state space)
    NULL           \* Sentinel model value for "no value"

(***************************************************************************)
(* Enumerated type sets                                                    *)
(***************************************************************************)
Sides       == {"BUY", "SELL"}
OrderTypes  == {"LIMIT", "MARKET", "MTL", "STOP_LIMIT", "STOP_MARKET"}
TIFs        == {"GTC", "IOC", "FOK", "DAY"}
Statuses    == {"NEW", "PARTIAL", "FILLED", "CANCELLED", "REJECTED"}
STPPolicies == {"CANCEL_NEWEST", "CANCEL_OLDEST", "CANCEL_BOTH", "DECREMENT"}

(***************************************************************************)
(* Helper operators                                                        *)
(***************************************************************************)
OppSide(s) == IF s = "BUY" THEN "SELL" ELSE "BUY"
Min(a, b)  == IF a <= b THEN a ELSE b
Max(a, b)  == IF a >= b THEN a ELSE b

\* Range of a sequence as a set
SeqRange(s) == {s[i] : i \in 1..Len(s)}

\* Remove element at index i from sequence
RemoveIdx(s, i) == SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

\* Sort a finite set of integers into ascending sequence
RECURSIVE SortSetAsc(_)
SortSetAsc(S) ==
    IF S = {} THEN <<>>
    ELSE LET m == CHOOSE x \in S : \A y \in S : x <= y
         IN <<m>> \o SortSetAsc(S \ {m})

\* Sort a finite set of integers into descending sequence
RECURSIVE SortSetDesc(_)
SortSetDesc(S) ==
    IF S = {} THEN <<>>
    ELSE LET m == CHOOSE x \in S : \A y \in S : x >= y
         IN <<m>> \o SortSetDesc(S \ {m})

(***************************************************************************)
(* State Variables                                                         *)
(***************************************************************************)
VARIABLES
    bidQ,           \* [PRICES -> Seq(Order)]: bid queues per price level
    askQ,           \* [PRICES -> Seq(Order)]: ask queues per price level
    stops,          \* Set of dormant stop orders
    lastTradePrice, \* Last execution price (PRICES \cup {NULL})
    postOnlyOK,     \* TRUE iff no trade has post-only aggressor (INV-11)
    stpOK,          \* TRUE iff no trade between same STP group (INV-12)
    nextId,         \* Next order ID to assign
    clock,          \* Logical clock (monotonic)
    lastAction      \* Records the last action for trace replay (overwritten each step)

vars == <<bidQ, askQ, stops, lastTradePrice, postOnlyOK, stpOK, nextId, clock, lastAction>>

(***************************************************************************)
(* Book query operators                                                    *)
(***************************************************************************)
ActiveBidPrices == {p \in PRICES : bidQ[p] /= <<>>}
ActiveAskPrices == {p \in PRICES : askQ[p] /= <<>>}

BestBid == IF ActiveBidPrices = {} THEN NULL
           ELSE CHOOSE x \in ActiveBidPrices : \A y \in ActiveBidPrices : x >= y

BestAsk == IF ActiveAskPrices = {} THEN NULL
           ELSE CHOOSE x \in ActiveAskPrices : \A y \in ActiveAskPrices : x <= y

\* Sorted contra prices for iteration during matching
\* BUY incoming matches against asks (ascending); SELL against bids (descending)
ContraPricesSorted(bQ, aQ, side) ==
    IF side = "BUY"
    THEN SortSetAsc({p \in PRICES : aQ[p] /= <<>>})
    ELSE SortSetDesc({p \in PRICES : bQ[p] /= <<>>})

(***************************************************************************)
(* Price compatibility predicate (§5.1 Step 2)                             *)
(***************************************************************************)
CanMatchPrice(inc, restingPrice) ==
    IF inc.price = NULL THEN TRUE   \* MARKET: matches any price
    ELSE IF inc.side = "BUY" THEN inc.price >= restingPrice
    ELSE inc.price <= restingPrice

(***************************************************************************)
(* Self-Trade Prevention conflict detection (§8.1)                         *)
(***************************************************************************)
SelfTradeConflict(inc, rest) ==
    /\ inc.stpGroup /= NULL
    /\ rest.stpGroup /= NULL
    /\ inc.stpGroup = rest.stpGroup

(***************************************************************************)
(* Well-Formedness predicate (§2.2, minus WF-6/7, WF-11/12, WF-17)        *)
(***************************************************************************)
WellFormed(o) ==
    /\ o.qty > 0                                                           \* WF-1
    /\ o.orderType = "LIMIT" => (o.price /= NULL /\ o.price > 0)          \* WF-2
    /\ o.orderType = "STOP_LIMIT" => (o.price /= NULL /\ o.price > 0)     \* WF-2a
    /\ o.orderType = "MTL" => o.price = NULL                               \* WF-2b
    /\ o.orderType \in {"MARKET", "STOP_MARKET"} => o.price = NULL         \* WF-3
    /\ o.orderType \in {"STOP_LIMIT", "STOP_MARKET"} =>
         (o.stopPrice /= NULL /\ o.stopPrice > 0)                          \* WF-4
    /\ o.orderType \in {"LIMIT", "MARKET", "MTL"} => o.stopPrice = NULL    \* WF-5
    /\ o.orderType = "MARKET" => o.tif \in {"IOC", "FOK"}                  \* WF-8
    /\ o.orderType = "MTL" => o.tif \in {"GTC", "DAY"}                     \* WF-8a
    /\ o.displayQty /= NULL =>
         (o.displayQty > 0 /\ o.displayQty <= o.qty)                       \* WF-9
    /\ o.displayQty /= NULL => o.orderType = "LIMIT"                       \* WF-10
    /\ o.postOnly => o.orderType = "LIMIT"                                 \* WF-13
    /\ o.postOnly => o.tif \notin {"IOC", "FOK"}                           \* WF-14
    /\ o.orderType \in {"MARKET", "MTL"} => ~o.postOnly                    \* WF-15
    /\ (o.stpGroup = NULL) <=> (o.stpPolicy = NULL)                        \* WF-16
    /\ o.minQty /= NULL => (o.minQty > 0 /\ o.minQty <= o.qty)            \* WF-18
    /\ o.minQty /= NULL => ~o.postOnly                                     \* WF-19
    /\ o.tif = "FOK" => o.minQty = NULL                                    \* WF-20

(***************************************************************************)
(* Order constructor                                                       *)
(***************************************************************************)
MakeOrder(id, side, otype, tif, price, stopPrice, qty, displayQty,
          postOnly, minQty, stpGroup, stpPolicy, ts) ==
    [id          |-> id,
     side        |-> side,
     orderType   |-> otype,
     tif         |-> tif,
     price       |-> price,
     stopPrice   |-> stopPrice,
     qty         |-> qty,
     remainingQty|-> qty,
     minQty      |-> minQty,
     displayQty  |-> displayQty,
     visibleQty  |-> IF displayQty /= NULL THEN Min(displayQty, qty) ELSE qty,
     postOnly    |-> postOnly,
     status      |-> "NEW",
     timestamp   |-> ts,
     stpGroup    |-> stpGroup,
     stpPolicy   |-> stpPolicy]

(***************************************************************************)
(* Available quantity computation for FOK/MinQty pre-checks (§5.3, §5.4)   *)
(***************************************************************************)
RECURSIVE SumVisibleNonConflicting(_, _)
SumVisibleNonConflicting(queue, inc) ==
    IF queue = <<>> THEN 0
    ELSE LET r == Head(queue) IN
         (IF SelfTradeConflict(inc, r) THEN 0 ELSE r.visibleQty)
         + SumVisibleNonConflicting(Tail(queue), inc)

RECURSIVE ComputeAvailable(_, _, _, _)
ComputeAvailable(inc, prices, bQ, aQ) ==
    IF prices = <<>> THEN 0
    ELSE LET p == Head(prices) IN
         IF ~CanMatchPrice(inc, p) THEN 0
         ELSE LET q == IF inc.side = "BUY" THEN aQ[p] ELSE bQ[p]
              IN SumVisibleNonConflicting(q, inc)
                 + ComputeAvailable(inc, Tail(prices), bQ, aQ)

FOKCheck(inc, bQ, aQ) ==
    ComputeAvailable(inc, ContraPricesSorted(bQ, aQ, inc.side), bQ, aQ) >= inc.qty

MinQtyCheck(inc, bQ, aQ) ==
    ComputeAvailable(inc, ContraPricesSorted(bQ, aQ, inc.side), bQ, aQ) >= inc.minQty

(***************************************************************************)
(* Post-Only crossing check (§7.6)                                         *)
(***************************************************************************)
WouldCross(inc, bQ, aQ) ==
    IF inc.side = "BUY"
    THEN LET ap == {p \in PRICES : aQ[p] /= <<>>}
         IN ap /= {} /\ inc.price >= (CHOOSE x \in ap : \A y \in ap : x <= y)
    ELSE LET bp == {p \in PRICES : bQ[p] /= <<>>}
         IN bp /= {} /\ inc.price <= (CHOOSE x \in bp : \A y \in bp : x >= y)

(***************************************************************************)
(* Stop order helpers (§7.3, §7.4, §10)                                    *)
(***************************************************************************)
ShouldTrigger(stop, tp) ==
    /\ tp /= NULL
    /\ IF stop.side = "BUY" THEN tp >= stop.stopPrice
       ELSE tp <= stop.stopPrice

ConvertStop(stop) ==
    IF stop.orderType = "STOP_LIMIT"
    THEN [stop EXCEPT !.orderType = "LIMIT", !.stopPrice = NULL,
                      !.status = "NEW"]
    ELSE [stop EXCEPT !.orderType = "MARKET", !.stopPrice = NULL,
                      !.price = NULL, !.status = "NEW"]

(***************************************************************************)
(* Core Matching Loop (§5.1)                                               *)
(*                                                                         *)
(* Recursive operator: processes one resting order interaction per call.    *)
(* Returns [inc, bQ, aQ, trades, tm] record.                              *)
(*                                                                         *)
(* SPEC BUG #1 — STP DECREMENT + Iceberg:                                 *)
(* DECREMENT can zero visibleQty of an iceberg without reloading it.       *)
(* The spec (§8.3) has no iceberg reload after DECREMENT, creating a       *)
(* stranded order with hidden qty but zero visible qty. We faithfully      *)
(* model this by reloading icebergs after DECREMENT (a spec fix), and      *)
(* document it as a spec gap.                                              *)
(*                                                                         *)
(* A fuel parameter bounds recursion depth for TLC termination safety.     *)
(***************************************************************************)

\* Update contra side queues: helper to reduce duplication
SetContra(side, bQ, aQ, price, newQueue) ==
    IF side = "BUY"
    THEN [bQ |-> bQ, aQ |-> [aQ EXCEPT ![price] = newQueue]]
    ELSE [bQ |-> [bQ EXCEPT ![price] = newQueue], aQ |-> aQ]

RECURSIVE DoMatch(_, _, _, _, _, _)
DoMatch(inc, bQ, aQ, tds, tm, fuel) ==
    LET done == [inc |-> inc, bQ |-> bQ, aQ |-> aQ, trades |-> tds, tm |-> tm]
    IN
    IF fuel <= 0 \/ inc.remainingQty = 0 \/ inc.status = "CANCELLED" THEN done
    ELSE
    LET side == inc.side
        contraActive == IF side = "BUY"
                        THEN {p \in PRICES : aQ[p] /= <<>>}
                        ELSE {p \in PRICES : bQ[p] /= <<>>}
    IN
    IF contraActive = {} THEN done
    ELSE
    LET bestP == IF side = "BUY"
                 THEN CHOOSE x \in contraActive : \A y \in contraActive : x <= y
                 ELSE CHOOSE x \in contraActive : \A y \in contraActive : x >= y
    IN
    IF ~CanMatchPrice(inc, bestP) THEN done
    ELSE
    LET q == IF side = "BUY" THEN aQ[bestP] ELSE bQ[bestP] IN
    IF q = <<>> THEN done
    ELSE
    LET resting  == Head(q)
        restTail == Tail(q)
    IN
    \* Skip zero-visible non-conflicting orders (remove from queue)
    IF resting.visibleQty = 0 /\ ~SelfTradeConflict(inc, resting) THEN
        LET sc == SetContra(side, bQ, aQ, bestP, restTail)
        IN DoMatch(inc, sc.bQ, sc.aQ, tds, tm, fuel - 1)
    ELSE
    IF SelfTradeConflict(inc, resting) THEN
        \* STP handling (§8.3) — incoming's policy governs (§8.2)
        IF inc.stpPolicy = "CANCEL_NEWEST" THEN
            \* Cancel incoming, resting unchanged, halt
            [done EXCEPT !.inc.status = "CANCELLED"]

        ELSE IF inc.stpPolicy = "CANCEL_OLDEST" THEN
            \* Cancel resting, continue matching
            LET sc == SetContra(side, bQ, aQ, bestP, restTail)
            IN DoMatch(inc, sc.bQ, sc.aQ, tds, tm, fuel - 1)

        ELSE IF inc.stpPolicy = "CANCEL_BOTH" THEN
            \* Cancel both, halt
            LET sc == SetContra(side, bQ, aQ, bestP, restTail) IN
            [done EXCEPT !.inc.status = "CANCELLED",
                         !.bQ = sc.bQ, !.aQ = sc.aQ]

        ELSE \* DECREMENT
            LET reduceQty == Min(inc.remainingQty, resting.visibleQty) IN
            IF reduceQty = 0 THEN
                \* Zero-visible STP conflict: skip (remove from queue)
                LET sc == SetContra(side, bQ, aQ, bestP, restTail)
                IN DoMatch(inc, sc.bQ, sc.aQ, tds, tm, fuel - 1)
            ELSE
            LET incRem  == inc.remainingQty - reduceQty
                restRem == resting.remainingQty - reduceQty
                restVis == resting.visibleQty - reduceQty
                newInc  == [inc EXCEPT !.remainingQty = incRem,
                                       !.status = IF incRem = 0
                                                  THEN "CANCELLED" ELSE @]
                newRest == [resting EXCEPT !.remainingQty = restRem,
                                           !.visibleQty = restVis]
            IN
            IF newRest.remainingQty = 0 THEN
                \* Resting fully decremented — remove
                LET sc == SetContra(side, bQ, aQ, bestP, restTail)
                IN DoMatch(newInc, sc.bQ, sc.aQ, tds, tm, fuel - 1)
            ELSE IF newRest.visibleQty = 0 /\ newRest.displayQty /= NULL THEN
                \* SPEC BUG #1 FIX: Reload iceberg after DECREMENT
                LET reloadQty == Min(newRest.displayQty, newRest.remainingQty)
                    reloaded  == [newRest EXCEPT !.visibleQty = reloadQty,
                                                 !.timestamp = tm,
                                                 !.status = "PARTIAL"]
                    sc == SetContra(side, bQ, aQ, bestP,
                                   restTail \o <<reloaded>>)
                IN DoMatch(newInc, sc.bQ, sc.aQ, tds, tm + 1, fuel - 1)
            ELSE
                \* Resting partially decremented, stays in place
                LET sc == SetContra(side, bQ, aQ, bestP,
                                    <<newRest>> \o restTail)
                IN DoMatch(newInc, sc.bQ, sc.aQ, tds, tm, fuel - 1)

    ELSE
        \* ---- Normal fill ----
        LET fillQty  == Min(inc.remainingQty, resting.visibleQty)
            newInc   == [inc EXCEPT !.remainingQty = @ - fillQty]
            newRest  == [resting EXCEPT !.visibleQty = @ - fillQty,
                                        !.remainingQty = @ - fillQty]
            trade    == [price         |-> resting.price,
                         qty           |-> fillQty,
                         aggId         |-> inc.id,
                         pasId         |-> resting.id,
                         aggSide       |-> inc.side,
                         aggPostOnly   |-> inc.postOnly,
                         aggStpGroup   |-> inc.stpGroup,
                         pasStpGroup   |-> resting.stpGroup]
            newTds   == Append(tds, trade)
        IN
        IF newRest.remainingQty = 0 THEN
            \* Resting fully filled — remove from queue
            LET sc == SetContra(side, bQ, aQ, bestP, restTail)
            IN DoMatch(newInc, sc.bQ, sc.aQ, newTds, tm, fuel - 1)

        ELSE IF newRest.visibleQty = 0 /\ newRest.displayQty /= NULL THEN
            \* Iceberg reload (§7.5): reload visible slice, lose time priority
            LET reloadQty == Min(newRest.displayQty, newRest.remainingQty)
                reloaded  == [newRest EXCEPT !.visibleQty = reloadQty,
                                             !.timestamp = tm,
                                             !.status = "PARTIAL"]
                sc == SetContra(side, bQ, aQ, bestP,
                                restTail \o <<reloaded>>)
            IN DoMatch(newInc, sc.bQ, sc.aQ, newTds, tm + 1, fuel - 1)

        ELSE
            \* Partial fill, resting stays at front
            LET updRest == [newRest EXCEPT !.status = "PARTIAL"]
                sc == SetContra(side, bQ, aQ, bestP,
                                <<updRest>> \o restTail)
            IN DoMatch(newInc, sc.bQ, sc.aQ, newTds, tm, fuel - 1)

(***************************************************************************)
(* Dispose: post-match handling of incoming order remainder (§5.2)         *)
(* Returns [bQ, aQ] after possibly inserting remainder on book.            *)
(***************************************************************************)
Dispose(inc, bQ, aQ, trades) ==
    IF inc.remainingQty = 0 \/ inc.status = "CANCELLED" THEN
        [bQ |-> bQ, aQ |-> aQ]
    ELSE IF inc.tif = "IOC" THEN
        \* IOC: cancel remainder
        [bQ |-> bQ, aQ |-> aQ]
    ELSE IF inc.orderType = "MARKET" THEN
        \* Markets never rest (§7.2)
        [bQ |-> bQ, aQ |-> aQ]
    ELSE
        \* GTC/DAY: rest on book (§6.1)
        LET p    == inc.price
            visQ == IF inc.displayQty /= NULL
                    THEN Min(inc.displayQty, inc.remainingQty)
                    ELSE inc.remainingQty
            st   == IF trades /= <<>> THEN "PARTIAL" ELSE "NEW"
            o    == [inc EXCEPT !.visibleQty = visQ, !.status = st]
        IN
        IF inc.side = "BUY"
        THEN [bQ |-> [bQ EXCEPT ![p] = Append(@, o)], aQ |-> aQ]
        ELSE [bQ |-> bQ, aQ |-> [aQ EXCEPT ![p] = Append(@, o)]]

(***************************************************************************)
(* PROCESS pipeline and stop cascade (§12, §10)                            *)
(*                                                                         *)
(* Mutually recursive:                                                     *)
(*   ProcessOrder -> DoMatch -> Dispose -> ProcessCascade                  *)
(*   ProcessCascade -> ProcessTriggered -> ProcessOrder                    *)
(*                                                                         *)
(* Returns: [bQ, aQ, stops, lastTP, trades, tm]                           *)
(***************************************************************************)
RECURSIVE ProcessOrder(_, _, _, _, _, _)
RECURSIVE ProcessCascade(_, _, _, _, _, _)
RECURSIVE ProcessTriggeredStops(_, _, _, _, _, _)

\* Process cascade: evaluate stops for each trade price
ProcessCascade(tradeSeq, bQ, aQ, stps, lastTP, tm) ==
    IF tradeSeq = <<>> THEN
        [bQ |-> bQ, aQ |-> aQ, stops |-> stps,
         lastTP |-> lastTP, trades |-> <<>>, tm |-> tm]
    ELSE
    LET tp        == Head(tradeSeq).price
        triggered == {s \in stps : ShouldTrigger(s, tp)}
        remaining == stps \ triggered
    IN
    IF triggered = {} THEN
        ProcessCascade(Tail(tradeSeq), bQ, aQ, stps, tp, tm)
    ELSE
    LET r  == ProcessTriggeredStops(triggered, bQ, aQ, remaining, tp, tm)
        r2 == ProcessCascade(Tail(tradeSeq), r.bQ, r.aQ, r.stops, r.lastTP, r.tm)
    IN [bQ     |-> r2.bQ,    aQ    |-> r2.aQ,
        stops  |-> r2.stops, lastTP|-> r2.lastTP,
        trades |-> r.trades \o r2.trades, tm |-> r2.tm]

\* Process triggered stops in timestamp order (§10.1)
ProcessTriggeredStops(trigs, bQ, aQ, stps, lastTP, tm) ==
    IF trigs = {} THEN
        [bQ |-> bQ, aQ |-> aQ, stops |-> stps,
         lastTP |-> lastTP, trades |-> <<>>, tm |-> tm]
    ELSE
    LET s == CHOOSE x \in trigs : \A y \in trigs : x.timestamp <= y.timestamp
        \* SPEC BUG #2 FIX: Give triggered stop a new timestamp so FIFO
        \* ordering is maintained when the order rests on the book.
        converted == [ConvertStop(s) EXCEPT !.timestamp = tm]
        result == ProcessOrder(converted, bQ, aQ, stps, lastTP, tm + 1)
        rest   == ProcessTriggeredStops(trigs \ {s}, result.bQ, result.aQ,
                      result.stops, result.lastTP, result.tm)
    IN [bQ     |-> rest.bQ,    aQ    |-> rest.aQ,
        stops  |-> rest.stops, lastTP|-> rest.lastTP,
        trades |-> result.trades \o rest.trades, tm |-> rest.tm]

\* Main PROCESS pipeline (§12)
ProcessOrder(order, bQ, aQ, stps, lastTP, tm) ==
    \* Phase 1: Stop order handling (§12 Phase 1, §7.3, §7.4)
    IF order.orderType \in {"STOP_LIMIT", "STOP_MARKET"} THEN
        IF ShouldTrigger(order, lastTP) THEN
            \* Trigger immediately — convert and re-enter pipeline
            \* Timestamp update: use current tm for the triggered order
            LET conv == [ConvertStop(order) EXCEPT !.timestamp = tm]
            IN ProcessOrder(conv, bQ, aQ, stps, lastTP, tm + 1)
        ELSE
            \* Add to dormant stop set
            [bQ |-> bQ, aQ |-> aQ, stops |-> stps \cup {order},
             lastTP |-> lastTP, trades |-> <<>>, tm |-> tm]

    \* Phase 2: Post-only check (§7.6, §12 Phase 2)
    \* Policy: REJECT (cancel if would cross)
    ELSE IF order.postOnly THEN
        IF WouldCross(order, bQ, aQ) THEN
            \* Post-only would cross — reject
            [bQ |-> bQ, aQ |-> aQ, stops |-> stps,
             lastTP |-> lastTP, trades |-> <<>>, tm |-> tm]
        ELSE
            \* Insert on book — no matching needed
            LET vis == IF order.displayQty /= NULL
                       THEN Min(order.displayQty, order.remainingQty)
                       ELSE order.remainingQty
                o  == [order EXCEPT !.visibleQty = vis, !.status = "NEW"]
                p  == order.price
            IN
            IF order.side = "BUY"
            THEN [bQ |-> [bQ EXCEPT ![p] = Append(@, o)], aQ |-> aQ,
                  stops |-> stps, lastTP |-> lastTP, trades |-> <<>>, tm |-> tm]
            ELSE [bQ |-> bQ, aQ |-> [aQ EXCEPT ![p] = Append(@, o)],
                  stops |-> stps, lastTP |-> lastTP, trades |-> <<>>, tm |-> tm]

    \* Phase 3: FOK pre-check (§5.3, §12 Phase 3)
    ELSE IF order.tif = "FOK" THEN
        IF ~FOKCheck(order, bQ, aQ) THEN
            [bQ |-> bQ, aQ |-> aQ, stops |-> stps,
             lastTP |-> lastTP, trades |-> <<>>, tm |-> tm]
        ELSE
        LET ms     == DoMatch(order, bQ, aQ, <<>>, tm, MAX_ORDERS * MAX_QTY * 3)
            newLTP == IF ms.trades /= <<>>
                      THEN ms.trades[Len(ms.trades)].price
                      ELSE lastTP
            cascade == ProcessCascade(ms.trades, ms.bQ, ms.aQ, stps, newLTP, ms.tm)
        IN [bQ     |-> cascade.bQ,    aQ    |-> cascade.aQ,
            stops  |-> cascade.stops, lastTP|-> cascade.lastTP,
            trades |-> ms.trades \o cascade.trades, tm |-> cascade.tm]

    \* Phase 3b: MinQty pre-check (§5.4, §12 Phase 3)
    ELSE IF order.minQty /= NULL THEN
        IF ~MinQtyCheck(order, bQ, aQ) THEN
            [bQ |-> bQ, aQ |-> aQ, stops |-> stps,
             lastTP |-> lastTP, trades |-> <<>>, tm |-> tm]
        ELSE
        LET ms   == DoMatch(order, bQ, aQ, <<>>, tm, MAX_ORDERS * MAX_QTY * 3)
            \* Phase 5a: clear minQty after matching (§12)
            inc  == IF ms.trades /= <<>>
                    THEN [ms.inc EXCEPT !.minQty = NULL]
                    ELSE ms.inc
            disp == Dispose(inc, ms.bQ, ms.aQ, ms.trades)
            newLTP == IF ms.trades /= <<>>
                      THEN ms.trades[Len(ms.trades)].price
                      ELSE lastTP
            cascade == ProcessCascade(ms.trades, disp.bQ, disp.aQ, stps,
                                      newLTP, ms.tm)
        IN [bQ     |-> cascade.bQ,    aQ    |-> cascade.aQ,
            stops  |-> cascade.stops, lastTP|-> cascade.lastTP,
            trades |-> ms.trades \o cascade.trades, tm |-> cascade.tm]

    \* Phase 4: Market-to-Limit (§7.7, §12 Phase 4)
    ELSE IF order.orderType = "MTL" THEN
        \* Market phase: match at any price (price = NULL)
        LET ms == DoMatch(order, bQ, aQ, <<>>, tm, MAX_ORDERS * MAX_QTY * 3) IN
        IF ms.trades = <<>> THEN
            \* No liquidity — cancel MTL (§7.7)
            [bQ |-> ms.bQ, aQ |-> ms.aQ, stops |-> stps,
             lastTP |-> lastTP, trades |-> <<>>, tm |-> ms.tm]
        ELSE
        \* Convert to LIMIT at first fill price (§7.7)
        LET limitPrice == ms.trades[1].price
            converted  == [ms.inc EXCEPT !.orderType = "LIMIT",
                                          !.price = limitPrice,
                                          !.minQty = NULL]
        IN
        IF converted.remainingQty = 0 THEN
            \* Fully filled during market phase
            LET newLTP  == ms.trades[Len(ms.trades)].price
                cascade == ProcessCascade(ms.trades, ms.bQ, ms.aQ, stps,
                                          newLTP, ms.tm)
            IN [bQ     |-> cascade.bQ,    aQ    |-> cascade.aQ,
                stops  |-> cascade.stops, lastTP|-> cascade.lastTP,
                trades |-> ms.trades \o cascade.trades, tm |-> cascade.tm]
        ELSE
            \* Continue matching at limit price, then dispose remainder
            LET ms2  == DoMatch(converted, ms.bQ, ms.aQ, <<>>, ms.tm,
                                  MAX_ORDERS * MAX_QTY * 3)
                disp == Dispose(ms2.inc, ms2.bQ, ms2.aQ,
                                ms.trades \o ms2.trades)
                allTrades == ms.trades \o ms2.trades
                newLTP == allTrades[Len(allTrades)].price
                cascade == ProcessCascade(allTrades, disp.bQ, disp.aQ, stps,
                                          newLTP, ms2.tm)
            IN [bQ     |-> cascade.bQ,    aQ    |-> cascade.aQ,
                stops  |-> cascade.stops, lastTP|-> cascade.lastTP,
                trades |-> allTrades \o cascade.trades, tm |-> cascade.tm]

    \* Phase 5: Normal matching (§5.1, §12 Phase 5)
    ELSE
        LET ms  == DoMatch(order, bQ, aQ, <<>>, tm, MAX_ORDERS * MAX_QTY * 3)
            \* Phase 5a: clear minQty (§12)
            inc == IF order.minQty /= NULL /\ ms.trades /= <<>>
                   THEN [ms.inc EXCEPT !.minQty = NULL]
                   ELSE ms.inc
            disp == Dispose(inc, ms.bQ, ms.aQ, ms.trades)
            newLTP == IF ms.trades /= <<>>
                      THEN ms.trades[Len(ms.trades)].price
                      ELSE lastTP
            cascade == ProcessCascade(ms.trades, disp.bQ, disp.aQ, stps,
                                      newLTP, ms.tm)
        IN [bQ     |-> cascade.bQ,    aQ    |-> cascade.aQ,
            stops  |-> cascade.stops, lastTP|-> cascade.lastTP,
            trades |-> ms.trades \o cascade.trades, tm |-> cascade.tm]

(***************************************************************************)
(* Find order on book by ID (for cancel/amend)                             *)
(* Returns [side, price, idx, order] or NULL                               *)
(***************************************************************************)
FindOrderOnBook(oid, bQ, aQ) ==
    LET bidHits == {<<p, i>> \in (PRICES \X (1..MAX_ORDERS)) :
                    i <= Len(bQ[p]) /\ bQ[p][i].id = oid}
        askHits == {<<p, i>> \in (PRICES \X (1..MAX_ORDERS)) :
                    i <= Len(aQ[p]) /\ aQ[p][i].id = oid}
    IN
    IF bidHits /= {} THEN
        LET h == CHOOSE x \in bidHits : TRUE
        IN [side |-> "BUY", price |-> h[1], idx |-> h[2],
            order |-> bQ[h[1]][h[2]]]
    ELSE IF askHits /= {} THEN
        LET h == CHOOSE x \in askHits : TRUE
        IN [side |-> "SELL", price |-> h[1], idx |-> h[2],
            order |-> aQ[h[1]][h[2]]]
    ELSE NULL

(***************************************************************************)
(* Trade invariant checking helpers                                        *)
(* Check trades produced by ProcessOrder against safety properties.        *)
(***************************************************************************)
RECURSIVE CheckTradesPostOnly(_)
CheckTradesPostOnly(trades) ==
    IF trades = <<>> THEN TRUE
    ELSE ~Head(trades).aggPostOnly /\ CheckTradesPostOnly(Tail(trades))

RECURSIVE CheckTradesSTP(_)
CheckTradesSTP(trades) ==
    IF trades = <<>> THEN TRUE
    ELSE LET t == Head(trades) IN
         (~(t.aggStpGroup /= NULL /\ t.pasStpGroup /= NULL
            /\ t.aggStpGroup = t.pasStpGroup))
         /\ CheckTradesSTP(Tail(trades))

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ bidQ = [p \in PRICES |-> <<>>]
    /\ askQ = [p \in PRICES |-> <<>>]
    /\ stops = {}
    /\ lastTradePrice = NULL
    /\ postOnlyOK = TRUE
    /\ stpOK = TRUE
    /\ nextId = 1
    /\ clock = 1
    /\ lastAction = [type |-> "Init"]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* Submit a new order — nondeterministically choose valid parameters
SubmitOrder ==
    /\ nextId <= MAX_ORDERS
    /\ clock < MAX_CLOCK
    /\ \E side \in Sides,
          otype \in OrderTypes,
          tif \in TIFs,
          price \in PRICES \cup {NULL},
          stopPrice \in PRICES \cup {NULL},
          qty \in 1..MAX_QTY,
          displayQty \in (1..MAX_QTY) \cup {NULL},
          po \in BOOLEAN,
          minQty \in (1..MAX_QTY) \cup {NULL},
          stpGrp \in {NULL, "G1"},
          stpPol \in STPPolicies \cup {NULL} :
        LET order == MakeOrder(nextId, side, otype, tif, price, stopPrice,
                               qty, displayQty, po, minQty, stpGrp, stpPol,
                               clock)
        IN
        /\ WellFormed(order)
        /\ LET result == ProcessOrder(order, bidQ, askQ, stops,
                                       lastTradePrice, clock + 1)
           IN
           /\ bidQ'           = result.bQ
           /\ askQ'           = result.aQ
           /\ stops'          = result.stops
           /\ lastTradePrice' = result.lastTP
           /\ postOnlyOK'     = postOnlyOK /\ CheckTradesPostOnly(result.trades)
           /\ stpOK'          = stpOK /\ CheckTradesSTP(result.trades)
           /\ nextId'         = nextId + 1
           /\ clock'          = result.tm
           /\ lastAction'     = [type        |-> "SubmitOrder",
                                  id          |-> nextId,
                                  side        |-> side,
                                  orderType   |-> otype,
                                  tif         |-> tif,
                                  price       |-> price,
                                  stopPrice   |-> stopPrice,
                                  qty         |-> qty,
                                  displayQty  |-> displayQty,
                                  postOnly    |-> po,
                                  minQty      |-> minQty,
                                  stpGroup    |-> stpGrp,
                                  stpPolicy   |-> stpPol]

\* Cancel a resting order (§9.1)
CancelOrder ==
    /\ clock < MAX_CLOCK
    /\ \E oid \in 1..(nextId - 1) :
        LET loc == FindOrderOnBook(oid, bidQ, askQ) IN
        /\ loc /= NULL
        /\ LET p      == loc.price
               idx    == loc.idx
               newBQ  == IF loc.side = "BUY"
                         THEN [bidQ EXCEPT ![p] = RemoveIdx(@, idx)]
                         ELSE bidQ
               newAQ  == IF loc.side = "SELL"
                         THEN [askQ EXCEPT ![p] = RemoveIdx(@, idx)]
                         ELSE askQ
           IN
           /\ bidQ'           = newBQ
           /\ askQ'           = newAQ
           /\ stops'          = stops
           /\ lastTradePrice' = lastTradePrice
           /\ UNCHANGED <<postOnlyOK, stpOK>>
           /\ nextId'         = nextId
           /\ clock'          = clock + 1
           /\ lastAction'     = [type |-> "CancelOrder", id |-> oid]

\* Amend a resting order (§9.2)
AmendOrder ==
    /\ clock < MAX_CLOCK
    /\ \E oid \in 1..(nextId - 1),
       newPrice \in PRICES \cup {NULL},
       newQty \in (1..MAX_QTY) \cup {NULL} :
        /\ newPrice /= NULL \/ newQty /= NULL   \* At least one change
        /\ LET loc == FindOrderOnBook(oid, bidQ, askQ) IN
           /\ loc /= NULL
           /\ LET order == loc.order
                  p     == loc.price
                  idx   == loc.idx
                  \* Determine if priority is lost (§9.2)
                  priceChange == newPrice /= NULL /\ newPrice /= order.price
                  qtyIncrease == newQty /= NULL /\ newQty > order.remainingQty
                  qtyDecrease == newQty /= NULL /\ newQty < order.remainingQty
              IN
              IF qtyDecrease /\ ~priceChange THEN
                  \* Quantity decrease — keep priority (§9.2)
                  LET updated == [order EXCEPT
                          !.remainingQty = newQty,
                          !.visibleQty = Min(order.visibleQty, newQty)]
                      newBQ == IF loc.side = "BUY"
                               THEN [bidQ EXCEPT ![p] =
                                   [@ EXCEPT ![idx] = updated]]
                               ELSE bidQ
                      newAQ == IF loc.side = "SELL"
                               THEN [askQ EXCEPT ![p] =
                                   [@ EXCEPT ![idx] = updated]]
                               ELSE askQ
                  IN
                  /\ bidQ'           = newBQ
                  /\ askQ'           = newAQ
                  /\ stops'          = stops
                  /\ lastTradePrice' = lastTradePrice
                  /\ UNCHANGED <<postOnlyOK, stpOK>>
                  /\ nextId'         = nextId
                  /\ clock'          = clock + 1
                  /\ lastAction'     = [type |-> "AmendOrder", id |-> oid,
                                         newPrice |-> newPrice, newQty |-> newQty]
              ELSE IF priceChange \/ qtyIncrease THEN
                  \* Price change or qty increase — lose priority, re-process
                  LET modified == [order EXCEPT
                          !.price = IF newPrice /= NULL THEN newPrice
                                    ELSE order.price,
                          !.remainingQty = IF newQty /= NULL THEN newQty
                                           ELSE order.remainingQty,
                          !.timestamp = clock,
                          !.visibleQty = IF order.displayQty /= NULL
                                         THEN Min(order.displayQty,
                                                  IF newQty /= NULL
                                                  THEN newQty
                                                  ELSE order.remainingQty)
                                         ELSE IF newQty /= NULL THEN newQty
                                              ELSE order.remainingQty]
                      \* Remove from current position
                      bQ2 == IF loc.side = "BUY"
                             THEN [bidQ EXCEPT ![p] = RemoveIdx(@, idx)]
                             ELSE bidQ
                      aQ2 == IF loc.side = "SELL"
                             THEN [askQ EXCEPT ![p] = RemoveIdx(@, idx)]
                             ELSE askQ
                      result == ProcessOrder(modified, bQ2, aQ2, stops,
                                              lastTradePrice, clock + 1)
                  IN
                  /\ bidQ'           = result.bQ
                  /\ askQ'           = result.aQ
                  /\ stops'          = result.stops
                  /\ lastTradePrice' = result.lastTP
                  /\ postOnlyOK'     = postOnlyOK /\ CheckTradesPostOnly(result.trades)
                  /\ stpOK'          = stpOK /\ CheckTradesSTP(result.trades)
                  /\ nextId'         = nextId
                  /\ clock'          = result.tm
                  /\ lastAction'     = [type |-> "AmendOrder", id |-> oid,
                                         newPrice |-> newPrice, newQty |-> newQty]
              ELSE
                  \* newQty = remainingQty and no price change — no-op
                  UNCHANGED vars

\* Helper: filter out DAY orders from a book side
RemoveDayOrders(q) ==
    [p \in PRICES |-> SelectSeq(q[p], LAMBDA o : o.tif /= "DAY")]

\* Advance time — expire DAY orders (simplified session close)
TimeAdvance ==
    /\ clock < MAX_CLOCK
    /\ clock' = clock + 1
    /\ bidQ' = RemoveDayOrders(bidQ)
    /\ askQ' = RemoveDayOrders(askQ)
    /\ stops' = {s \in stops : s.tif /= "DAY"}
    /\ lastAction' = [type |-> "TimeAdvance"]
    /\ UNCHANGED <<lastTradePrice, postOnlyOK, stpOK, nextId>>

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
NextNoAmend ==
    \/ SubmitOrder
    \/ CancelOrder
    \/ TimeAdvance

Next ==
    \/ SubmitOrder
    \/ CancelOrder
    \/ AmendOrder
    \/ TimeAdvance

(***************************************************************************)
(* Fairness (for liveness properties)                                      *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* ====================== SAFETY INVARIANTS ==============================*)
(***************************************************************************)

\* Type invariant (all state variables have correct types)
TypeInvariant ==
    /\ bidQ \in [PRICES -> Seq([id : Nat, side : Sides,
                    orderType : OrderTypes, tif : TIFs,
                    price : PRICES \cup {NULL},
                    stopPrice : PRICES \cup {NULL},
                    qty : 1..MAX_QTY,
                    remainingQty : 0..(MAX_QTY * MAX_ORDERS),
                    minQty : (1..MAX_QTY) \cup {NULL},
                    displayQty : (1..MAX_QTY) \cup {NULL},
                    visibleQty : 0..(MAX_QTY * MAX_ORDERS),
                    postOnly : BOOLEAN,
                    status : Statuses,
                    timestamp : Nat,
                    stpGroup : {NULL, "G1"},
                    stpPolicy : STPPolicies \cup {NULL}])]
    /\ nextId \in Nat
    /\ clock \in Nat

\* INV-4: Book is uncrossed — bestBid < bestAsk (or either side empty)
BookUncrossed ==
    \/ BestBid = NULL
    \/ BestAsk = NULL
    \/ BestBid < BestAsk

\* INV-1: No empty price levels
NoEmptyLevels ==
    /\ \A p \in PRICES : bidQ[p] /= <<>> => Len(bidQ[p]) > 0
    /\ \A p \in PRICES : askQ[p] /= <<>> => Len(askQ[p]) > 0

\* INV-5: Every order on book has remainingQty > 0
NoGhosts ==
    /\ \A p \in PRICES : \A i \in 1..Len(bidQ[p]) : bidQ[p][i].remainingQty > 0
    /\ \A p \in PRICES : \A i \in 1..Len(askQ[p]) : askQ[p][i].remainingQty > 0

\* INV-6: Resting orders have valid status
StatusConsistency ==
    /\ \A p \in PRICES : \A i \in 1..Len(bidQ[p]) :
         bidQ[p][i].status \in {"NEW", "PARTIAL"}
    /\ \A p \in PRICES : \A i \in 1..Len(askQ[p]) :
         askQ[p][i].status \in {"NEW", "PARTIAL"}

\* INV-7: FIFO within price level (timestamps strictly increasing)
FIFOWithinLevel ==
    /\ \A p \in PRICES : \A i \in 1..(Len(bidQ[p]) - 1) :
         bidQ[p][i].timestamp < bidQ[p][i+1].timestamp
    /\ \A p \in PRICES : \A i \in 1..(Len(askQ[p]) - 1) :
         askQ[p][i].timestamp < askQ[p][i+1].timestamp

\* INV-8: No MARKET orders resting on book
NoRestingMarkets ==
    /\ \A p \in PRICES : \A i \in 1..Len(bidQ[p]) :
         bidQ[p][i].orderType /= "MARKET"
    /\ \A p \in PRICES : \A i \in 1..Len(askQ[p]) :
         askQ[p][i].orderType /= "MARKET"

\* INV-11: No trade where aggressor was post-only
PostOnlyGuarantee == postOnlyOK

\* INV-12: No trade between orders in same STP group
STPGuarantee == stpOK

\* INV-13: No MTL orders resting on book
NoRestingMTL ==
    /\ \A p \in PRICES : \A i \in 1..Len(bidQ[p]) :
         bidQ[p][i].orderType /= "MTL"
    /\ \A p \in PRICES : \A i \in 1..Len(askQ[p]) :
         askQ[p][i].orderType /= "MTL"

\* INV-14: No resting order has minQty set
NoRestingMinQty ==
    /\ \A p \in PRICES : \A i \in 1..Len(bidQ[p]) :
         bidQ[p][i].minQty = NULL
    /\ \A p \in PRICES : \A i \in 1..Len(askQ[p]) :
         askQ[p][i].minQty = NULL

\* Combined safety invariant
SafetyInvariant ==
    /\ BookUncrossed
    /\ NoGhosts
    /\ StatusConsistency
    /\ FIFOWithinLevel
    /\ NoRestingMarkets
    /\ PostOnlyGuarantee
    /\ STPGuarantee
    /\ NoRestingMTL
    /\ NoRestingMinQty

(***************************************************************************)
(* ====================== CHALLENGE PROPERTIES ===========================*)
(* These are properties we SUSPECT might be subtly violated.               *)
(* If TLC finds a counterexample, it reveals a spec bug.                   *)
(***************************************************************************)

\* Challenge 1: "A FOK order never partially fills"
\* Could STP DECREMENT consume qty without filling, leaving partial?
\* (This checks trade log: all trades from FOK aggressor sum to order qty)

\* Challenge 2: "Post-only + iceberg: visible slice never crosses after reload"
\* This is checked by BookUncrossed holding after iceberg reloads

\* Challenge 3: "Amend with decreased qty never changes best bid/ask"
\* This would need tracking old/new best prices — complex, defer

(***************************************************************************)
(* ====================== TARGET INVARIANTS ==============================*)
(* These are INTENTIONALLY VIOLATED to produce counterexample traces      *)
(* for conformance testing. Each target, when used as an INVARIANT in a   *)
(* .cfg file, forces TLC to find a trace reaching a specific state.       *)
(***************************************************************************)

\* Target 1: A trade occurs
TargetNoTrade ==
    lastTradePrice = NULL

\* Target 2: A stop order triggers (trade happens while stops exist)
\* Violated when: a trade occurred AND stops were pending = trigger likely
TargetNoStopTrigger ==
    stops = {} \/ lastTradePrice = NULL

\* Target 3: An iceberg order exists on the book
TargetNoIceberg ==
    /\ \A p \in PRICES : \A i \in 1..Len(bidQ[p]) :
        bidQ[p][i].displayQty = NULL
    /\ \A p \in PRICES : \A i \in 1..Len(askQ[p]) :
        askQ[p][i].displayQty = NULL

\* Target 4: STP conflict occurs (order cancelled due to STP)
\* postOnlyOK tracks post-only; stpOK tracks STP trades.
\* But we want STP *cancels*, not STP *trade violations*.
\* Simplest: if an order is submitted and the book has fewer resting orders
\* than expected (some were cancelled by STP). Hard to track without lastAction.
\* Alternative: just find a state where lastTradePrice /= NULL and the book
\* is smaller than nextId - 1 (some orders were consumed by STP or fills).
\* Simplest viable target: two orders from same group on opposite sides exist
\* ... but they can't both rest (STP would fire). So: nextId > 2 and
\* all STP group orders are gone = STP fired.

\* Target 5: A partial fill (order rests with PARTIAL status)
TargetNoPartialFill ==
    /\ \A p \in PRICES : \A i \in 1..Len(bidQ[p]) :
        bidQ[p][i].status /= "PARTIAL"
    /\ \A p \in PRICES : \A i \in 1..Len(askQ[p]) :
        askQ[p][i].status /= "PARTIAL"

\* Target 6: Post-only order exists on the book
TargetNoPostOnly ==
    /\ \A p \in PRICES : \A i \in 1..Len(bidQ[p]) :
        ~bidQ[p][i].postOnly
    /\ \A p \in PRICES : \A i \in 1..Len(askQ[p]) :
        ~askQ[p][i].postOnly

\* Target 7: Multiple price levels have orders on same side
TargetSingleLevel ==
    /\ Cardinality(ActiveBidPrices) <= 1
    /\ Cardinality(ActiveAskPrices) <= 1

\* Target 8: A stop order is pending (stops set non-empty)
TargetNoStops ==
    stops = {}

\* Target 9: Book has orders on both sides simultaneously
TargetOneSide ==
    ActiveBidPrices = {} \/ ActiveAskPrices = {}

\* Target 10: Two or more orders at same price level
TargetNoDepth ==
    /\ \A p \in PRICES : Len(bidQ[p]) <= 1
    /\ \A p \in PRICES : Len(askQ[p]) <= 1

=============================================================================
