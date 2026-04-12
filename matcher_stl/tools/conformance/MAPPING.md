# TLA+ to C++ Conformance Mapping — Matching Engine

This document is the contract between the TLC trace format and the C++ replay
harness. Every comparison in the conformance pipeline is derived from this file.

**TLA+ spec:** `~/matcher_tla/MatchingEngine.tla` (~867 lines)
**C++ engine:** `~/matcher_stl/src/engine.h` (template `Engine<Listener>`)
**Formal spec:** `~/matcher_stl/matching-engine-formal-spec.md` v1.2.0

---

## Section 1: Supported Actions (Initial Scope — 4)

### 1. SubmitOrder

```
TLA+ signature:  SubmitOrder (line 598)
                 Nondeterministically chooses: side, otype, tif, price, stopPrice,
                 qty, displayQty, postOnly, minQty, stpGrp, stpPol.
                 Preconditions: nextId <= MAX_ORDERS, clock < MAX_CLOCK,
                 WellFormed(order).
                 Calls ProcessOrder(order, bidQ, askQ, stops, lastTradePrice, clock+1)
                 which handles matching, stops, post-only, FOK, minQty, MTL atomically.
                 Result updates: bidQ', askQ', stops', lastTradePrice', clock',
                 nextId' = nextId + 1, postOnlyOK', stpOK'.

C++ call:        engine.submitOrder(input)
                 where input is an OrderInput struct.
                 Matching, stop cascade, dispose are all atomic within submitOrder().

Param mapping:
  id            -> input.id            = nextId from trace (OrderId = uint64_t)
  side          -> input.side          = Side::BUY or Side::SELL
  otype         -> input.orderType     = OrderType enum mapping:
                                         "LIMIT" -> LIMIT, "MARKET" -> MARKET,
                                         "MTL" -> MARKET_TO_LIMIT,
                                         "STOP_LIMIT" -> STOP_LIMIT,
                                         "STOP_MARKET" -> STOP_MARKET
  tif           -> input.timeInForce   = TimeInForce enum mapping:
                                         "GTC" -> GTC, "IOC" -> IOC, "FOK" -> FOK,
                                         "DAY" -> DAY
                                         Note: TLA+ has no "GTD" (not modeled)
  price         -> input.price         = Price (int64_t), NULL -> 0
  stopPrice     -> input.stopPrice     = Price, NULL -> 0
  qty           -> input.quantity       = Quantity (int64_t)
  displayQty    -> input.displayQty    = Quantity, NULL -> 0
  postOnly      -> input.postOnly      = bool
  minQty        -> input.minQty        = Quantity, NULL -> 0
  stpGrp        -> input.selfTradeGroup = SelfTradeGroup (uint64_t),
                                         NULL -> 0, "G1" -> 1
  stpPol        -> input.stpPolicy     = STPPolicy enum mapping:
                                         NULL -> NONE, "CANCEL_NEWEST" -> CANCEL_NEWEST,
                                         "CANCEL_OLDEST" -> CANCEL_OLDEST,
                                         "CANCEL_BOTH" -> CANCEL_BOTH,
                                         "DECREMENT" -> DECREMENT

Decision:        TLA+ only fires SubmitOrder when WellFormed(order) is true.
                 C++ rejects via onOrderRejected if validation fails.
                 Since TLA+ always submits well-formed orders, C++ must ACCEPT
                 (get onOrderAccepted callback). Rejection = BUG.

Post-action:     submitOrder() is fully atomic: validates, accepts, matches, disposes,
                 triggers stops, all in one call. No separate post-action needed.

Fills:           Fills are emitted via listener.onTrade(trade) during submitOrder().
                 TLA+ returns result.trades as a sequence. These must match exactly.

Notes:           TLA+ models ProcessOrder as a pure function returning new state.
                 C++ mutates engine state in place. Both are atomic w.r.t. the action.
                 TLA+ uses NULL model value; C++ uses 0 for "no value" on price,
                 stopPrice, displayQty, minQty, selfTradeGroup.
                 TLA+ clock starts at 1; C++ timestamp starts at 0 and increments
                 via tick() -> ++now_. Timestamps are not directly comparable
                 (different starting points), but FIFO ordering must match.
```

### 2. CancelOrder

```
TLA+ signature:  CancelOrder (line 630)
                 \E oid \in 1..(nextId-1): FindOrderOnBook(oid, bidQ, askQ) /= NULL
                 Removes the order from its price level queue.
                 Updates: bidQ' or askQ', clock' = clock + 1.
                 UNCHANGED: stops, lastTradePrice, postOnlyOK, stpOK, nextId.

C++ call:        bool ok = engine.cancelOrder(id)
                 Returns true if order was found and cancelled, false otherwise.
                 Calls listener.onOrderCancelled(order, "USER_REQUESTED").

Param mapping:
  oid           -> id                  = OrderId (uint64_t)

Decision:        TLA+ CancelOrder only fires when FindOrderOnBook succeeds.
                 C++ cancelOrder returns false if order not found.
                 If TLA+ says cancel happened, C++ must return true. False = BUG.

Notes:           TLA+ CancelOrder only cancels orders on the book (bidQ/askQ).
                 TLA+ does NOT cancel stop orders via CancelOrder.
                 C++ cancelOrder CAN cancel stop orders (checks both book and stops_).
                 This is a scope difference: TLA+ FindOrderOnBook only searches
                 bidQ and askQ, not the stops set.
                 For conformance: only compare cancels of book-resting orders.

                 TLA+ does not model cancel of filled/expired orders (they're not
                 on the book). C++ returns false for those. No conflict.
```

### 3. AmendOrder

```
TLA+ signature:  AmendOrder (line 653)
                 \E oid, newPrice, newQty: FindOrderOnBook(oid) /= NULL
                 /\ (newPrice /= NULL \/ newQty /= NULL)
                 Three cases:
                   a) qtyDecrease && !priceChange: in-place update, keep priority
                   b) priceChange || qtyIncrease: remove, re-process (loses priority)
                   c) no effective change: UNCHANGED vars (no-op)
                 Updates: bidQ', askQ', and if re-process: stops', lastTradePrice',
                 postOnlyOK', stpOK', clock' = result.tm.

C++ call:        bool ok = engine.amendOrder(id, newPx, newQty)
                 newPx=0 means no price change; newQty=0 means no qty change.

Param mapping:
  oid           -> id                  = OrderId
  newPrice      -> newPx               = Price, NULL -> 0 (no change)
  newQty        -> newQty              = Quantity, NULL -> 0 (no change)

Decision:        TLA+ only fires when FindOrderOnBook succeeds.
                 C++ returns false if not found. False when TLA+ fires = BUG.

Notes:           TLA+ AmendOrder handles the re-process case by calling
                 ProcessOrder(modified, ...), which may produce trades and
                 trigger stops. C++ amendOrder does the same via processActive().

                 TLA+ uses PRICES set for newPrice; C++ accepts any positive price.
                 TLA+ assigns timestamp = clock for priority-losing amends;
                 C++ assigns timestamp = tick() (++now_). Ordering is consistent.

                 AmendOrder is only in Next (not NextNoAmend). The main cfg uses
                 NextNoAmend; MatchingEngine_amend.cfg uses Next.
```

### 4. TimeAdvance

```
TLA+ signature:  TimeAdvance (line 732)
                 clock' = clock + 1
                 bidQ' = RemoveDayOrders(bidQ)
                 askQ' = RemoveDayOrders(askQ)
                 stops' = {s \in stops : s.tif /= "DAY"}
                 UNCHANGED: lastTradePrice, postOnlyOK, stpOK, nextId

C++ call:        engine.expireOrders(t)
                 Scans all resting orders. Expires GTD orders past their time
                 and ALL DAY orders unconditionally.

Param mapping:
  (none)        -> t = any timestamp (triggers DAY expiry)

Decision:        Always succeeds in both. No decision to compare.

Notes:           TLA+ TimeAdvance is a simplified session close: it removes all
                 DAY orders from both sides and from stops.
                 C++ expireOrders(t) also expires GTD orders with expireTime <= t.
                 GTD is not modeled in TLA+ (TIFs = {"GTC","IOC","FOK","DAY"}).
                 For conformance: only DAY expiry is comparable.

                 TLA+ TimeAdvance does NOT call RemoveIdx or emit events.
                 C++ expireOrders calls listener.onOrderExpired for each.

                 C++ also expires DAY orders on any expireOrders() call regardless
                 of timestamp value. This matches TLA+ behavior (unconditional).
```

### Actions NOT in scope

```
MarketDataUpdate:  Not modeled as a separate TLA+ action.
                   lastTradePrice is updated atomically within ProcessOrder
                   as part of SubmitOrder. No external price feed exists in the model.
                   Classification: NOT APPLICABLE — internal to SubmitOrder.

Fill:              Not a separate TLA+ action.
                   Fills are produced atomically within ProcessOrder during SubmitOrder.
                   The trade sequence is returned as result.trades.
                   Classification: INTERNAL to SubmitOrder — compared as output, not action.

Iceberg reload:    Internal to DoMatch (line 326-334).
                   Classification: INTERNAL — verified via book state comparison.

STP resolution:    Internal to DoMatch (line 253-303).
                   Classification: INTERNAL — verified via book state and fill comparison.

Stop trigger:      Internal to ProcessCascade/ProcessTriggeredStops (line 383-416).
                   Classification: INTERNAL — verified via book state and fill comparison.
```

---

## Section 2: Comparable State Projections

### Book State (bidQ, askQ)

```
TLA+ field:      bidQ : [PRICES -> Seq(Order)]
                 askQ : [PRICES -> Seq(Order)]
                 Queues are TLA+ sequences (1-indexed). Only non-empty queues
                 represent active price levels.

C++ access:      bids_ : std::map<Price, PriceLevel*, std::greater<Price>>
                 asks_ : std::map<Price, PriceLevel*, std::less<Price>>
                 Each PriceLevel has a doubly-linked list (head/tail) of Order*.
                 Traverse: for each map entry, walk head->next->...->nullptr.

Comparable form: Per side, a list of (price, [orders]) where orders is a list
                 of (id, remainingQty, visibleQty) in FIFO order.
                 Only non-empty levels are included.

                 struct OrderEntry { int id; int remainingQty; int visibleQty; };
                 struct LevelEntry { int price; std::vector<OrderEntry> orders; };
                 Bids: sorted descending by price.
                 Asks: sorted ascending by price.

Type:            Structural (ordered list of ordered lists)
Comparison:      EXACT
                 - Same number of active price levels per side
                 - Same price at each level
                 - Same orders at each level in SAME FIFO order
                 - Same id, remainingQty, visibleQty for each order
                 Any difference = BUG

Notes:           TLA+ bidQ has keys for ALL PRICES (even inactive ones with <<>>).
                 C++ bids_ only contains active levels. The projection normalizes
                 both to only active levels.

                 TLA+ orders have many fields. For comparison, only id,
                 remainingQty, and visibleQty are compared. Other fields
                 (side, price, orderType, tif, etc.) are fixed after insertion
                 and don't change — comparing id is sufficient to verify identity.
```

### Fill Output (trades)

```
TLA+ field:      result.trades : Seq(Trade)
                 Each trade: [price, qty, aggId, pasId, aggSide,
                              aggPostOnly, aggStpGroup, pasStpGroup]
                 Produced by ProcessOrder, returned atomically.

C++ access:      Captured via Listener.onTrade(trade) callbacks during submitOrder().
                 Each Trade: { tradeId, price, quantity, aggressorId, passiveId,
                              aggressorSide, timestamp }

Comparable form: Per SubmitOrder action, a sequence of:
                 (aggressorId, passiveId, price, quantity)

Type:            Ordered sequence
Comparison:      EXACT — both price and quantity must match exactly.
                 Sequence order must match (FIFO: passive orders filled in
                 time-priority order within each price level).

Notes:           TLA+ trades include aggPostOnly and aggStpGroup/pasStpGroup
                 for invariant checking. C++ trades don't include these.
                 Only compare the 4 core fields: aggId, pasId, price, qty.

                 Fill order matters: if the sequence differs, it indicates a
                 FIFO violation or price-priority violation = BUG.
                 This is the exact property that caught Bug #2 (stale stop timestamps).
```

### Stop Orders

```
TLA+ field:      stops : Set(Order)
                 Unordered set of dormant stop orders.

C++ access:      stops_ : std::vector<Order*>
                 Unordered vector of pending stop orders.

Comparable form: Set of (id, side, stopPrice, price, remainingQty)
                 Compared as sets (order doesn't matter).

Type:            Set
Comparison:      EXACT — same set of stop order IDs with same parameters.

Notes:           TLA+ stops is a mathematical set.
                 C++ stops_ is a vector (swap-and-pop for removal).
                 Compare as unordered sets by sorting by id before comparison.
```

### Last Trade Price

```
TLA+ field:      lastTradePrice : PRICES \cup {NULL}
                 Updated within ProcessCascade to each trade's price.
                 After ProcessOrder, it equals the last trade's price (or NULL).

C++ access:      engine.lastTradePrice() -> Price (int64_t)
                 Updated in emitAndTrigger: lastPx_ = trades_[i].price.
                 Returns 0 if no trades have occurred.

Comparable form: Scalar integer.
Type:            Numeric
Comparison:      EXACT — NULL maps to 0 in C++.

Notes:           Both update lastTradePrice to the LAST trade's price after
                 each SubmitOrder action (including cascade trades).
```

### Order Count

```
TLA+ field:      Derived: sum of Len(bidQ[p]) + Len(askQ[p]) for all p in PRICES.

C++ access:      engine.orderCount() -> size_t
                 This counts all orders in idx_ (including stops).
                 For book-only count: engine.orderCount() - engine.stopCount().

Comparable form: Scalar integer.
Type:            Numeric
Comparison:      EXACT

Notes:           TLA+ count excludes stop orders (they're in a separate set).
                 C++ orderCount() includes stop orders in idx_.
                 Comparable value = engine.orderCount() - engine.stopCount()
                 for book orders, plus engine.stopCount() compared separately.
```

### Clock / nextId

```
TLA+ field:      nextId : Nat (next order ID to assign)
                 clock  : Nat (logical timestamp counter)

C++ access:      No direct accessor for nextId (managed by OrderIndex).
                 engine.time() for current timestamp.

Comparable form: Not directly compared.
Type:            N/A
Comparison:      SKIP — internal bookkeeping.

Notes:           nextId is implicitly matched by verifying order IDs in the book.
                 clock is abstracted — TLA+ and C++ use different clock domains.
                 FIFO ordering is verified structurally via book state comparison.
```

### Fields that CANNOT be compared

```
Field:           order.timestamp
Classification:  SKIP
Reason:          TLA+ uses a logical clock starting at 1, incrementing per action.
                 C++ uses tick() (++now_) which starts at 0.
                 The absolute values differ. FIFO ordering is verified structurally
                 by comparing the order sequence within each price level.

Field:           postOnlyOK, stpOK (accumulated invariant flags)
Classification:  SKIP
Reason:          These are TLA+ model-checking artifacts for invariant verification.
                 They accumulate across all actions. C++ has no equivalent state.
                 The properties they check are verified by fill comparison:
                 no trade should have a post-only aggressor, no trade should have
                 matching STP groups.

Field:           Internal matching loop state (DoMatch recursion)
Classification:  SKIP
Reason:          Model artifact. Not observable after action completes.

Field:           Memory allocation state (oA_, oF_, oP_, pools)
Classification:  SKIP
Reason:          Implementation detail not modeled in TLA+.
```

---

## Section 3: Engine Configuration from TLC Scope

### TLC Constants

```
PRICES = {1, 2, 3}   (or {1, 2} in smaller configs)
C++ setup:       No setup needed. C++ accepts any Price (int64_t > 0).
Gap:             TLA+ explores a discrete finite set of prices.
                 C++ accepts any positive integer.
                 Conformance tests use only TLA+ price values.

MAX_QTY = 2
C++ setup:       No setup needed. C++ accepts any Quantity (int64_t > 0).
Gap:             TLA+ quantities range 1..MAX_QTY.
                 C++ accepts any positive quantity.
                 Conformance tests use only TLA+ quantity values.

MAX_ORDERS = 2   (or 3 in noamend config)
C++ setup:       No setup needed. OrderIndex grows dynamically.
Gap:             TLA+ limits total orders ever submitted (bounds state space).
                 C++ has no inherent limit.
                 Conformance traces will have at most MAX_ORDERS submissions.

MAX_CLOCK = 4    (or 6 in noamend config)
C++ setup:       No setup needed.
Gap:             TLA+ bounds logical clock (bounds state space).
                 C++ has no clock limit.

TICK_SIZE = 1
C++ setup:       Engine constructor tickSz parameter (default 1).
                 Must match: Engine(listener, PostOnlyPolicy::REJECT, 1).

NULL = NULL      (TLC model value)
C++ setup:       Mapped to 0 for price, stopPrice, displayQty, minQty, selfTradeGroup.
                 Mapped to STPPolicy::NONE for stpPolicy.
                 No C++ setup needed — 0 is the default for OrderInput fields.

STP Groups:      TLA+ uses {NULL, "G1"} — only one STP group.
C++ setup:       "G1" maps to selfTradeGroup = 1.
                 NULL maps to selfTradeGroup = 0.
```

### Engine Initialization

```cpp
Rec listener;
Engine<Rec> engine(listener, PostOnlyPolicy::REJECT, /*tickSz=*/1);
// No further configuration needed.
// The engine starts with empty book, no stops, lastPx_ = 0, now_ = 0.
// TLA+ Init sets bidQ/askQ to empty sequences, stops={}, lastTradePrice=NULL,
// nextId=1, clock=1.
```

### Identity Mapping

```
TLA+ order ID:   nextId (starts at 1, increments by 1 per SubmitOrder)
C++ order ID:    OrderInput.id = same integer value from trace

TLA+ STP group:  "G1" -> 1, NULL -> 0
C++ STP group:   input.selfTradeGroup = uint64_t

TLA+ STP policy: "CANCEL_NEWEST" -> STPPolicy::CANCEL_NEWEST
                 "CANCEL_OLDEST" -> STPPolicy::CANCEL_OLDEST
                 "CANCEL_BOTH"   -> STPPolicy::CANCEL_BOTH
                 "DECREMENT"     -> STPPolicy::DECREMENT
                 NULL            -> STPPolicy::NONE
```

---

## Section 4: Abstraction Differences

### Difference 1: Atomic Processing

```
TLA+ behavior:   ProcessOrder is a pure function: takes (order, bidQ, askQ, stops,
                 lastTP, tm) and returns (bQ', aQ', stops', lastTP', trades, tm').
                 All matching, dispose, and stop cascade happen atomically.

C++ behavior:    submitOrder() mutates engine state in place. Matching, dispose,
                 and stop cascade all happen within the single call. Fills are
                 emitted via listener callbacks during execution.

Impact:          Both are atomic from the caller's perspective. No difference in
                 observable state after the action completes.

Classification:  NO DIFFERENCE — both are atomic.
```

### Difference 2: Integer Arithmetic

```
TLA+ behavior:   All prices and quantities are integers from bounded sets.
                 Arithmetic is exact integer arithmetic (Integers module).

C++ behavior:    Price = int64_t, Quantity = int64_t.
                 Arithmetic is exact integer arithmetic.

Impact:          No difference. Both use exact integer arithmetic.

Classification:  NO DIFFERENCE — matching is deterministic with exact integers.
                 Any fill price or quantity mismatch = BUG.
```

### Difference 3: FIFO Ordering

```
TLA+ behavior:   Orders within a price level are a Seq (sequence).
                 New orders are Append'ed to the end.
                 Matching always takes Head (front of queue).
                 FIFOWithinLevel invariant: timestamps strictly increasing.

C++ behavior:    Orders within a PriceLevel are a doubly-linked list.
                 pushBack adds to tail. front() returns head.
                 Matching takes front() first.

Impact:          Both implement FIFO. Order within a level must match exactly.
                 Bug #2 (stale stop timestamps) was found by checking this property.

Classification:  BUG if FIFO order differs.
```

### Difference 4: Clock Domains

```
TLA+ behavior:   clock starts at 1. Incremented in various places:
                 - SubmitOrder: order.timestamp = clock, processing starts at clock+1
                 - CancelOrder: clock' = clock + 1
                 - AmendOrder: modified.timestamp = clock
                 - TimeAdvance: clock' = clock + 1
                 - Iceberg reload: tm + 1
                 - Stop trigger: tm + 1

C++ behavior:    now_ starts at 0. tick() returns ++now_.
                 - submitOrder: o->timestamp = tick() (first tick)
                 - cancelOrder: no timestamp change
                 - amendOrder: o->timestamp = tick() (for priority-losing amends)
                 - Iceberg reload: rest->timestamp = tick()
                 - Stop trigger: (implicit via processActive)

Impact:          Absolute timestamp values differ. But relative ordering is preserved
                 because both use monotonically increasing counters.

Classification:  SKIP — do not compare absolute timestamps.
                 FIFO ordering is verified structurally via book state comparison.
```

### Difference 5: Post-Only Policy

```
TLA+ behavior:   Post-only policy is hardcoded to REJECT in the model.
                 If WouldCross(order, bQ, aQ), order is silently dropped
                 (not added to book, no trades, no error).

C++ behavior:    Post-only policy is configurable (REJECT or REPRICE).
                 REJECT mode: order is cancelled with "POST_ONLY_WOULD_CROSS".
                 Must configure Engine with PostOnlyPolicy::REJECT for conformance.

Impact:          Behavior matches when C++ uses REJECT policy.
                 TLA+ silently drops; C++ cancels with callback.
                 From state perspective: order is not on the book in both cases.

Classification:  NO DIFFERENCE when configured correctly.
                 The cancelled callback is C++ implementation detail (SKIP).
```

### Difference 6: GTD Time-in-Force

```
TLA+ behavior:   GTD is NOT modeled. TIFs = {"GTC", "IOC", "FOK", "DAY"}.
                 No expireTime field on orders.

C++ behavior:    GTD is fully supported. Orders have expireTime field.
                 expireOrders(t) expires GTD orders past their time.

Impact:          TLA+ traces will never contain GTD orders.
                 No conformance gap for modeled features.

Classification:  UNSUPPORTED in TLA+ — not tested by conformance pipeline.
```

### Difference 7: Stop Order Cancel

```
TLA+ behavior:   CancelOrder only searches bidQ and askQ (FindOrderOnBook).
                 Stop orders in the stops set cannot be cancelled via CancelOrder.

C++ behavior:    cancelOrder() searches idx_ which includes both book orders
                 and stop orders. Stop orders can be cancelled.

Impact:          TLA+ traces will never cancel a stop order.
                 C++ supports it but it won't be tested by TLA+ traces.

Classification:  UNSUPPORTED in TLA+ — not tested by conformance pipeline.
                 Not a bug: C++ has strictly more functionality.
```

### Difference 8: FOK/MinQty Pre-check Quantity

```
TLA+ behavior:   FOKCheck and MinQtyCheck use SumVisibleNonConflicting which
                 sums r.visibleQty for non-STP-conflicting resting orders.

C++ behavior:    availQty sums r->remainingQty (not visibleQty) for non-STP-
                 conflicting resting orders (engine.h lines 381-383).

Impact:          For non-iceberg orders, visibleQty == remainingQty, so no
                 difference. For iceberg orders, remainingQty includes hidden
                 reserve. C++ is MORE PERMISSIVE: it may accept FOK/minQty
                 orders that TLA+ would reject (because C++ counts hidden qty).

Classification:  KNOWN DIVERGENCE — documented in the findings analysis.
                 TLA+ follows the spec (use visibleQty); C++ uses remainingQty.
                 For conformance: TLA+ traces only fire SubmitOrder when the
                 pre-check passes, so C++ will also pass (more permissive).
                 No divergence on traces where TLA+ accepts.
                 A trace where TLA+ REJECTS (by not firing) would reveal the
                 difference, but TLA+ traces only contain fired actions.
```

### Difference 9: Instrument Model

```
TLA+ behavior:   Single implicit instrument. No instrumentId field.

C++ behavior:    Single engine instance per instrument. No instrumentId field.

Impact:          No difference for conformance. Both are single-instrument.

Classification:  NO DIFFERENCE.
```

### Summary of Classifications

```
NO DIFFERENCE:    Atomic processing, integer arithmetic, FIFO ordering,
                  post-only (when configured), single instrument.

SKIP:             Timestamps (different clock domains), postOnlyOK/stpOK flags,
                  internal matching state, memory allocation.

UNSUPPORTED:      GTD orders, stop cancel, post-only REPRICE policy.

KNOWN DIVERGENCE: FOK/minQty pre-check uses remainingQty vs visibleQty for
                  icebergs. C++ is more permissive. No trace-level divergence
                  expected (TLA+ only generates actions that pass its own checks).

BUG:              Any difference in fill price, fill quantity, fill order,
                  book state, stop set, or lastTradePrice after any action.
```
