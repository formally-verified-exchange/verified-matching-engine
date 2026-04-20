# C++ Implementation Bug Log

A running record of implementation bugs found in the C++ matching engine
(`matcher_stl/src/engine.h`) that are **not** present in the TLA+
specification or Lean reference implementation. These bugs are discovered
by running the C++ engine against oracles derived from the formal models:

- **Shadow differential (`shadow_test`)** — random-action sequences replayed
  simultaneously against the C++ engine and a simple vector-based reference
  engine that implements the spec literally. Discrepancies in book state,
  trades, cancellations, or last trade price are flagged.
- **TLA+ conformance replay (`conformance_harness`)** — replays JSON
  counterexample/execution traces emitted by TLC against the C++ engine
  and compares projected state at every step.

Each entry below records: discovery context, symptom, root cause,
fix (with diff), verification, and status. Stable IDs (`CPP-NNN`) are
cross-reference targets for the paper and commit messages.

---

## CPP-001 — STP DECREMENT / CANCEL_BOTH leaves empty price level in book index

**Status:** fixed (2026-04-19)
**Discovered by:** `shadow_test 500 42` — first divergence at step 423.
**Severity:** correctness — book query functions return a price for a level
that contains no orders; affects `bestBid()`, `bestAsk()`, and anything
downstream (e.g. stop-trigger evaluation using `lastTradePrice` comparisons
against best price, market-order price-protection checks).

### Symptom

With seed 42, after `SUBMIT id=352 SELL LIMIT GTC px=96 q=2 stg=1` hits a
resting `BUY id=... px=96 q=2 stg=1` via STP DECREMENT, the shadow reports
`bestBid=0, cnt=0` while the real engine reports `bestBid=96, cnt=0`.
The price-level count (`cnt`) agrees that no orders remain, but
`bestBid()` keeps returning the price of the just-emptied level until a
later book-traversing action dislodges it.

```
step 422 [...] shadow: bid=96 ask=0 cnt=1  real: bid=96 ask=0 cnt=1
step 423 [SUBMIT id=352 SELL LIMIT GTC px=96 q=2 stg=1]
         shadow: bid=0  ask=0 cnt=0       real: bid=96 ask=0 cnt=0   <-- phantom
step 424 [SUBMIT id=353 BUY LIMIT FOK px=101 q=5]
         shadow: bid=0  ask=0 cnt=0       real: bid=96 ask=0 cnt=0   <-- still phantom
step 425 [SUBMIT id=354 SELL MARKET IOC px=0 q=1]
         shadow: bid=0  ask=0             real: bid=0  ask=0         <-- cleared
```

### Root cause

`matchAgainst` normally cleans up an empty price level at the end of the
per-level loop body (`if (lv->empty()) { contra.erase(li); freeLvl(lv); }`).
When STP fires and both the incoming and resting order are fully
consumed (DECREMENT zeroing both, or CANCEL_BOTH), the function
early-returns *before* reaching that cleanup statement. The
`PriceLevel*` remains in the `bids_` / `asks_` map with zero orders;
`bestBid()` returns `bids_.begin()->first` and sees the stale price.

### Fix

One-line guard before the early return in `matchAgainst` (`engine.h`):

```diff
                 if (stpConflict(inc, rest)) {
                     handleStp(inc, rest);
-                    if (inc->status == OrderStatus::CANCELLED || inc->remainingQty == 0)
-                        return;
+                    if (inc->status == OrderStatus::CANCELLED || inc->remainingQty == 0) {
+                        if (lv->empty()) { contra.erase(li); freeLvl(lv); }
+                        return;
+                    }
                     continue;
                 }
```

This covers the two STP branches that can remove the resting order without
producing a trade while simultaneously terminating the incoming order:
DECREMENT (both zeroed) and CANCEL_BOTH.

### Verification

- `test_correctness`: 59/59 pass (unchanged).
- `shadow_test 500 42`: previously 2 divergences at steps 423 & 424 → now 0
  divergences, 500/500 pass.
- `shadow_test 1000 1`: previously 2 → 0 divergences.
- `shadow_test 1000 99`: 0 divergences (unchanged; seed did not reach this
  path).
- `conformance_harness` on all 107 TLA+ counterexample replays: 107/107
  pass, 0 divergences (unchanged).

### Why this was not caught earlier

- `test_correctness`'s directed STP tests (`test_stp_decrement_then_match`
  and the `Ported from ~/matcher: STP` block) exercise DECREMENT, but not
  the configuration where the decremented pair was the last order at its
  price level *and* the subsequent action queries `bestBid`/`bestAsk`
  before another book traversal naturally prunes the level.
- TLA+ counterexample replays (`conformance_harness`) use traces produced
  from target-probe violations, which are short (1–3 steps) and rarely
  leave residual state long enough to expose a stale-index bug.
- The `shadow_test` found it in ~423 random steps — exactly the kind of
  compound trajectory (cancel → submit → decrement-to-empty → submit
  without touching the same level) that random differential testing
  exposes and directed tests do not.

### Mapping to formal spec

The TLA+ spec models the book as sequences per price and derives
`bestBid` / `bestAsk` at each read from the non-empty sequences. It has
no separate cached index, so this class of bug is structurally impossible
in the spec. The defect is an **implementation-level omission**:
maintenance of the book's price-indexed map was left incomplete in one
control-flow branch.

---

## CPP-002 — FOK / MinQty feasibility check used `remainingQty` vs spec's `visibleQty`

**Status:** fixed (2026-04-19)
**Discovered by:** `shadow_test 1000 7` — first divergence at step 332.
**Severity:** correctness — FOK-on-stop orders fill where the spec says
they must be cancelled; affects stop-cascade paths against iceberg contra.

### Symptom

With seed 7, an iceberg SELL submission at step 332 triggers a resting
stop with FOK. The shadow cancels the stop (`FOK_NOT_SATISFIABLE`). The
real engine fills it.

```
step 332 [SUBMIT id=277 SELL LIMIT DAY px=100 q=15 dq=3]
  shadow trades:    [{agg=277 pas=271 @106 q=5}]
  real   trades:    [{agg=277 pas=271 @106 q=5},
                     {agg=274 pas=277 @100 q=3},
                     {agg=274 pas=277 @100 q=2}]
  shadow cancelled: [{274:FOK_NOT_SATISFIABLE}]
  real   cancelled: []
```

### Root cause (hypothesis)

`shadow_test.cpp:1307` documents a known divergence:

> The spec says FOK/minQty checks use `visibleQty`; the real engine uses
> `remainingQty`. If the incoming order has FOK or minQty and there is
> an iceberg on the contra side, a divergence where shadow cancels but
> real engine trades is KNOWN.

The harness's `hasIcebergContra` guard (lines 1313–1317) suppresses this
specific pattern **only when the incoming action itself is FOK or
minQty**. At step 332 the incoming action (id=277) is a plain `LIMIT DAY`
iceberg. The FOK order is a resting stop (id=274) that is triggered by
the cascade following id=277's trade at 106. When the triggered FOK
stop enters matching, the engine does its feasibility check against
the contra side — which now includes the just-rested remainder of 277
(an iceberg with `displayQty=3`, `remainingQty=10`, `visibleQty=3`).
The spec says feasibility must be evaluated on `visibleQty`; the
implementation evaluates on `remainingQty` and considers the stop
fillable, so it trades.

### Fix

`engine.h:392-408` — change the inner accumulator to `r->visibleQty`,
matching `MatchingEngine.tla:159` (`AvailableQty` sums `r.visibleQty`
over non-STP-conflicting resting orders). One-line change plus a
comment citing the spec.

```diff
     template<typename M>
     Quantity availQty(const Order* inc, const M& contra, Quantity thresh) const {
         Quantity avail = 0;
         for (auto it = contra.begin(); it != contra.end(); ++it) {
             if (!canMatch(inc, it->first)) break;
             for (Order* r = it->second->head; r; r = r->next) {
                 if (!stpConflict(inc, r)) {
-                    avail += r->remainingQty;
+                    avail += r->visibleQty;
                     if (avail >= thresh) return avail;
                 }
             }
         }
         return avail;
     }
```

### Verification

- `test_correctness`: 65/65 pass (was 59 before CPP-003; +3 for CPP-003;
  +3 for CPP-002):
  - `test_fok_sees_only_visible_of_iceberg` — FOK 5 against iceberg
    (qty=10, displayQty=2) must be cancelled, not traded.
  - `test_fok_matches_visible_slice` — FOK 2 against the same iceberg
    must fill.
  - `test_minqty_sees_only_visible_of_iceberg` — same logic for
    `minQty`.
- `shadow_test 1000 7`: previously 20 BUG divergences at step 332 →
  now **0 divergences, 1000 steps pass**.
- `conformance_harness` on all 107 TLA+ deep CEs + 10 small: 107/107
  pass, 0 divergences (unchanged).

### Why this was not caught earlier

The shadow-test harness had a guard (`shadow_test.cpp:1307-1317`) that
explicitly marked divergences from this pattern as `KNOWN` *only when
the incoming action was FOK or MinQty*. The first seed-7 manifestation
at step 332 arrived via a stop cascade — a resting FOK stop triggered
mid-trace — which the guard did not cover, so the divergence surfaced
as a BUG. The guard papered over the bug rather than fixing it.

---

## CPP-003 — `expireOrders` did not expire DAY/GTD stop orders on time advance

**Status:** fixed (2026-04-19)
**Discovered by:** incremental TLC→C++ pipeline smoke, `empty` scenario,
chunk 0 trace_0_6 step 3 [TimeAdvance].

### Symptom

TLA+ projected state at a `TimeAdvance` step shows `stopCount` dropping
(e.g. 2 → 1), while the C++ harness reports `stopCount` unchanged. The
divergence first appears on the TimeAdvance itself and persists for all
subsequent steps.

Across 20 replayed simulate traces on the `empty` scenario:

```
{"chunks":2, "pass":16, "fail":4, "bug_divergences":13, "steps":120}
```

All reported bug divergences on these traces are of the form
`stopCount: expected=X actual=X+1` at a `TimeAdvance` step or the first
post-TimeAdvance submit.

### Root cause

`MatchingEngine.tla:757` models `TimeAdvance` as removing DAY stops
from the stop set:

```tla
TimeAdvance ==
    /\ clock' = clock + 1
    /\ bidQ' = RemoveDayOrders(bidQ)
    /\ askQ' = RemoveDayOrders(askQ)
    /\ stops' = {s \in stops : s.tif /= "DAY"}
    ...
```

`engine.h:262 expireOrders(Timestamp t)` scanned only `bids_` and
`asks_` (the live book), not the stop table `stops_`. Any pending
`DAY` stop (or expired `GTD` stop) survived every TimeAdvance call the
conformance harness issued, so `stopCount` drifted upward relative to
the spec from the first TimeAdvance onward.

### Fix

`engine.h:262-290`: refactor the expire predicate into a lambda and
apply it to `stops_` in addition to the book sides:

```diff
     void expireOrders(Timestamp t) {
+        auto shouldExpire = [&](Order* o) {
+            if (o->timeInForce == TimeInForce::DAY) return true;
+            if (o->timeInForce == TimeInForce::GTD && o->expireTime > 0 && t >= o->expireTime) return true;
+            return false;
+        };
         std::vector<Order*> exp;
         auto scan = [&](auto& m) {
             for (auto& [px, lv] : m)
                 for (Order* o = lv->head; o; o = o->next)
-                    if (/* DAY or expired GTD */) exp.push_back(o);
+                    if (shouldExpire(o)) exp.push_back(o);
         };
         scan(bids_); scan(asks_);
         ...book cleanup unchanged...
+        for (size_t i = 0; i < stops_.size();) {
+            Order* s = stops_[i];
+            if (shouldExpire(s)) {
+                stops_[i] = stops_.back();
+                stops_.pop_back();
+                s->status = OrderStatus::EXPIRED;
+                L.onOrderExpired(*s);
+                idx_.erase(s->id);
+                freeOrd(s);
+            } else {
+                ++i;
+            }
+        }
     }
```

### Verification

- `test_correctness`: 62/62 pass, including three new directed tests:
  - `test_day_stop_expires_on_time_advance` — submit DAY stop, advance
    time, assert `stopCount == 0`.
  - `test_gtd_stop_expires_on_time_advance` — submit GTD stop past its
    `expireTime`, assert expiry.
  - `test_gtc_stop_survives_time_advance` — negative: GTC stop must
    not expire.
- Incremental pipeline re-run (empty × 2 chunks × 10 traces): pending
  re-execution after CPP-002 fix lands in the same session.

### Why this was not caught earlier

The existing expiry tests (`test_partial_fill_then_expire`,
`test_gtd_partial_fill_then_expire`) only exercise book-side DAY/GTD
expiration. No directed test submitted a DAY stop and advanced time.
The TLA+ conformance replays (`conformance_harness` on the 107 deep
CEs) did not execute `TimeAdvance` because all 13 scenarios use
`NextNoAmend`-style next-state relations that interleave `TimeAdvance`
sparsely and the CEs were short (1–3 steps with no TimeAdvance). The
incremental pipeline's `-simulate -depth MAX_CLOCK-1` runs fully
interleaved walks that routinely hit `TimeAdvance` mid-trace, which
is what surfaced the defect.

### Provenance

- Pipeline artifacts: `/tmp/inc_smoke/empty/chunk_0/json_failed/trace_0_6.json`
  (projection shows `stopCount` dropping on TimeAdvance steps).
- Produced by `matcher_tla/tools/incremental/produce_chunk.sh` running
  `tlc2.TLC -simulate file=...,num=10 -depth 7 -config empty__safety.cfg`.

---

## CPP-004 — Not a bug: shadow-reference modelling error (resolved)

**Status:** resolved — **not an engine defect** (2026-04-19)
**Discovered by:** `shadow_test 3000 42`; re-triggered at high
frequency by the 500-seed × 5 M-step shadow sweep
(`shadow_runs/sweep_20260419-202514/`) — every seed tripped the same
class within the first few thousand ops.
**Resolution:** the real engine is spec-compliant; the shadow's
matching-priority rule diverges from the spec. No engine change
required.

### Minimal repro (seed 443, step 9)

```
step 9 [SUBMIT id=8 BUY LIMIT DAY px=103 q=8]
  shadow trades: [{agg=8 pas=5 @98 q=8}]
  real   trades: [{agg=8 pas=4 @98 q=4},
                  {agg=8 pas=5 @98 q=4}]
```

### Root cause

At the start of step 9 the ask level @98 contains two orders:

| Order | Role | Timestamp | Sequence position |
|---|---|---|---|
| `id=4` | Iceberg (dQ=6, rem=5, vis=4); reloaded during step 8 | **new** (`tick()` at step 8 reload) | front |
| `id=5` | SELL STP_LIM submitted step 5, triggered during step 8 cascade, rested at @98 | **old** (step-5 submit; not refreshed on trigger) | back |

Insertion order ≠ timestamp order. The three parties interpret FIFO
priority differently:

| Oracle | Priority rule | First match at step 9 |
|---|---|---|
| Real engine | `lv->front()` — linked-list insertion order | `id=4` (q=4), then `id=5` (q=4) |
| TLA+ spec  | `Head(restTail)` — sequence position (tla:330–335 reload, tla:348–368 Dispose `Append`) | `id=4` (q=4), then `id=5` (q=4) |
| Shadow     | `sort by (price, earliest m_ts)` (`shadow_test.cpp:443`) | `id=5` (q=8) |

The spec's semantics are **sequence-position FIFO**: reload does
`restTail \o <<reloaded>>` (push to end of queue) and Dispose does
`Append(@, o)` (push to end), and DoMatch reads `Head`. The real
engine's doubly-linked list with `pushBack`-only insertion and
`lv->front()` matching implements exactly that. The shadow's
timestamp-sort treats an order with an older `m_ts` as higher
priority regardless of queue position, which only matches the spec
when timestamps happen to be in insertion order.

Scenarios where shadow diverges from spec+engine:
- A reloading iceberg that gains a newer timestamp than a later-
  arriving, freshly-inserted order (stop trigger, post-only reprice,
  FOK-fail reinstate).
- Any path that updates `m_ts` without re-sorting the book queue.

The TLA+ conformance pipeline (232 k traces this session) produced
**no** divergences of this class after adjusting for converter
artifacts, confirming the engine matches the spec.

### Fix

None for the engine. Shadow should be patched to iterate the book
side in **insertion order** (vector/list append order) and use
timestamp only as a secondary tiebreaker, matching the spec's
sequence-position semantics. Tracked as a test-tooling fix outside
`BUG_LOG.md` scope; does not affect the verified engine.

### Why this survived earlier triage

The original CPP-004 entry proposed a test: "if the TLA+ replay over
millions of traces flags the same class of mismatch, the engine is
at fault; if it does not, the shadow is." The incremental pipeline
ran ~232 k traces across 12 scenarios and surfaced zero trade-
ordering divergences attributable to this class (the `fills[i]`
divergences seen there are downstream of a separate converter
aggregation artifact in `infer_fills`). Per the original criterion,
shadow is at fault.

---

## CPP-005 — MARKET remainder leaked into book on DAY/GTD TIF

**Status:** fixed (2026-04-19)
**Discovered by:** incremental TLC → C++ conformance pipeline,
`amend_playground` chunk 5 `trace_0_625` step 2 (AmendOrder).
Minimal 3-step repro preserved in the experiment artefacts;
reproduced across all `amend_playground` chunks (~79 divergences
before the fix).
**Severity:** correctness — a triggered `STOP_MARKET` with TIF
`DAY`/`GTD` that partially fills leaves its remainder **resting
on the book at price 0**, violating INV-8 `NoRestingMarkets` and
inflating `orderCount` by one for the remainder of the trace.
Downstream effect: subsequent aggressors may trade against the
phantom market, producing extra fills (contributing to the
Class-B `fills.count` divergences seen in the sweep).

### Symptom

TLA+ projected state at step 2 shows `orderCount=1`; the C++ engine
reports `orderCount=2` and the extra count persists for every
subsequent step. Trace walk:

```
seed:
  bids: id=1 @1 q=2,  id=2 @2 q=1
  asks: id=3 @4 q=1,  id=4 @5 q=1
  stops: []

step 1 SubmitOrder id=5 BUY STOP_MARKET DAY sp=4 q=2 minQty=1
  stops: [id=5]   orderCount=4  ✓ agrees with spec

step 2 AmendOrder id=2 newPrice=5
  spec:   bids=[id=1@1 q=2], asks=[], stops=[], orderCount=1, LTP=5
  engine: bids=[id=1@1 q=2, id=5@0 q=1], asks=[],
          orderCount=2  ← phantom MARKET at price 0
```

Amend re-prices `id=2` from @2 to @5 → matches ask `id=3` @4 q=1
→ `lastTradePrice=4` → triggers stop `id=5` (BUY stop, 4 ≥ 4) →
stop converts to MARKET with its original TIF (DAY) preserved
(tla:199) → consumes the remaining ask `id=4` @5 q=1 → leftover
q=1 enters `Dispose`.

### Root cause

`engine.h:541–557` `dispose()` only applies the "MARKET-never-rests"
guard on the `GTC` branch; the `DAY`/`GTD` branches fall through
to `insertOrder(o)` unconditionally. With `price=0`, that inserts
the residual order on the bid side at level 0.

```cpp
// pre-fix
case TimeInForce::GTC:
    if (o->orderType == OrderType::MARKET) {
        o->status = OrderStatus::CANCELLED;
        L.onOrderCancelled(*o, "MARKET_NO_FULL_FILL");
        return;
    }
    insertOrder(o); ...
case TimeInForce::GTD:
case TimeInForce::DAY:
    insertOrder(o);   // ← no MARKET guard
    o->status = hasTr ? PARTIALLY_FILLED : NEW;
    return;
```

The TLA+ spec's `Dispose` (MatchingEngine.tla:348–368) drops MARKET
remainders for every non-IOC TIF unconditionally, and INV-8
`NoRestingMarkets` (tla:833–838) makes a resting MARKET a safety
invariant. WF-8 (tla:117) constrains *user-submitted* MARKETs to
IOC/FOK only, but a triggered `STOP_MARKET` retains its original
TIF (tla:199) — so a MARKET-with-DAY combination is unreachable
from user input yet is the exact state a triggered stop enters.

### Fix

Lift the MARKET-drop guard to apply to all three persistent TIFs
(`engine.h:541–557`):

```diff
 case TimeInForce::GTC:
-    if (o->orderType == OrderType::MARKET) {
-        o->status = OrderStatus::CANCELLED;
-        L.onOrderCancelled(*o, "MARKET_NO_FULL_FILL");
-        return;
-    }
-    insertOrder(o);
-    o->status = hasTr ? OrderStatus::PARTIALLY_FILLED : OrderStatus::NEW;
-    return;
 case TimeInForce::GTD:
 case TimeInForce::DAY:
-    insertOrder(o);
-    o->status = hasTr ? OrderStatus::PARTIALLY_FILLED : OrderStatus::NEW;
-    return;
+    // MatchingEngine.tla:354 drops MARKET remainders for every non-IOC
+    // TIF; INV-8 NoRestingMarkets (tla:833) makes a resting MARKET a
+    // safety violation. A triggered STOP_MARKET keeps its original
+    // TIF (tla:199) so this path must cover DAY/GTD, not GTC alone.
+    if (o->orderType == OrderType::MARKET) {
+        o->status = OrderStatus::CANCELLED;
+        L.onOrderCancelled(*o, "MARKET_NO_FULL_FILL");
+        return;
+    }
+    insertOrder(o);
+    o->status = hasTr ? OrderStatus::PARTIALLY_FILLED : OrderStatus::NEW;
+    return;
```

### Verification

- `test_correctness`: 65/65 pass (unchanged).
- The original `amend_playground/chunk_5/trace_0_625` repro: engine
  state at step 2 matches spec projection (orderCount=1).
- Fix applied source-only during an active pipeline sweep; post-fix
  rebuild verified via `build-verify/` without disturbing the
  in-flight non-instrumented binary.

### Why this wasn't caught earlier

1. **Unit tests** — `test_correctness` covers DAY/GTC orders resting
   on the book and separately covers stop triggering, but has no
   case that *partially fills* a triggered `STOP_MARKET` with a DAY
   TIF. The invariant break only appears when the triggered market
   has leftover qty and is a non-IOC TIF, which no directed test
   exercised.
2. **Shadow differential** — `shadow_test.cpp:511–524` has the exact
   same missing-MARKET-guard on the DAY/GTD branch. Both engines
   insert the phantom MARKET identically, so the differential never
   diverges. A sibling C++ reference cannot expose a bug it shares
   with the system under test; only a separate formal oracle can.
3. **TLA+ conformance replays (small, directed CE traces)** —
   pre-`amend_playground` counterexamples were 1–3 steps long and
   didn't exercise the amend-triggers-stop path.
4. **Incremental pipeline surfaced it** — the random-walk simulator
   routinely produces `AmendOrder` steps that re-price across the
   spread and fire pending stops, which is exactly the shape
   required.

### Mapping to formal spec

`MatchingEngine.tla:348–368 Dispose` — the authoritative definition
that every MARKET remainder is dropped regardless of TIF. Combined
with tla:199 (stop trigger preserves TIF) and tla:833 (INV-8), the
spec makes "resting MARKET" structurally impossible. The fix
imports exactly this discipline into the C++ branch that had
drifted from it.

### Provenance

- Pipeline artefact: `matcher_tla/experiments/incremental/amend_playground/chunk_5/json_failed/trace_0_625.json`
- Produced by `matcher_tla/tools/incremental/produce_chunk.sh` →
  TLC `-simulate -depth 20 -config amend_playground__safety.cfg`.
- Converter: `matcher_stl/tools/conformance/convert_matching_traces.py --simulate`.

---

## Summary table

| ID | Status | Oracle | Found at | Fixed |
|-----|--------|--------|----------|-------|
| CPP-001 | fixed      | shadow_test               | seed 42, step 423                          | 2026-04-19 |
| CPP-002 | fixed      | shadow_test               | seed 7, step 332                           | 2026-04-19 |
| CPP-003 | fixed      | incremental pipeline      | empty chunk_0 trace_0_6 step 3 TimeAdvance | 2026-04-19 |
| CPP-004 | **not a bug** | shadow_test            | resolved: shadow-reference modelling error (sequence-pos vs timestamp FIFO) | 2026-04-19 |
| CPP-005 | fixed      | incremental pipeline      | amend_playground chunk_5 trace_0_625 step 2 AmendOrder | 2026-04-19 |

**Coverage context.** Before the CPP-001 fix, combined line coverage of
`engine.h` from unit tests + shadow + conformance was 75.6%, function
coverage 85.4%, branch coverage 63.1%. Neither the directed unit tests
(47.3% lines) nor the TLA+ conformance replay (29.1% lines) exercised the
specific STP-decrement-to-empty-level path; only the shadow random
differential (42.1% lines, extending to the compound path that triggered
the phantom level) exposed it. See `build-coverage/run_logs/` for the
per-suite gcovr reports.
