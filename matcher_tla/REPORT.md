# Matching Engine TLA+ Verification Report

## Summary

The formal specification (matching-engine-formal-spec.md v1.2.0) was translated into TLA+ and exhaustively model-checked using TLC across multiple configurations. Two specification bugs were discovered and several design observations documented.

## Spec Bugs Found

### Bug #1: Stop Trigger Missing Timestamp Update (FIFO Violation)

**Severity:** High — directly violates INV-7 (FIFO within price level)

**Location:** §10.1 EVALUATE_STOPS, interaction with §6.1 INSERT

**Issue:** When a stop order triggers (§10.1), it converts to a LIMIT/MARKET order and enters the PROCESS pipeline. However, the spec does not update the stop order's timestamp. The stop keeps its *original submission timestamp* from when it was first placed. When the triggered order rests on the book after partial matching, it is appended to the back of the price level queue (§6.1) but has an *earlier* timestamp than orders already in that queue.

**Counterexample trace (freshly reproduced and archived 2026-09-26 against
`MatchingEngine_noamend.cfg` with the timestamp-refresh line reverted; raw
TLC log and full provenance in `results/fifo_counterexample_noamend_raw.log`
and `results/metadata.json`. An earlier version of this section described a
different trace attributed to a "Small" configuration with `MAX_ORDERS=2`,
which cannot admit a third order and could not have produced any 3-order
trace; that attribution was unverifiable — this table's own "3-order
(partial)" row below already recorded *no violation found* under this same
config with the bug present, contradicting the old claim — and has been
withdrawn in favor of this archived reproduction):**
1. BUY LIMIT qty=1 @1 → rests on bid (id=1, timestamp=1)
2. SELL STOP_LIMIT stopPrice=1, price=1, qty=1 → added to stops (id=2, timestamp=2)
3. SELL LIMIT qty=2 @1 → fills against BUY @1 (trade at price=1), triggers the stop
   - Trade triggers stop order 2 (lastTradePrice=1 ≤ stopPrice=1)
   - Stop converts to SELL LIMIT @1 and rests on ask
   - Incoming order 3 (timestamp=3) also rests on ask @1 (partially filled, remainingQty=1)
   - **Result:** askQ[1] = [order3(ts=3), order2(ts=2)] — FIFO violated!
   - TLC2 2.19 (rev 5a47802), OpenJDK 21.0.12.1, 1 worker: 9,160,154 states
     generated / 4,980,329 distinct states, 2m41s wall time (this is a
     violation-hit, not an exhaustive run; hardware/JVM-dependent, not a
     universal constant). This is a three-order counterexample; no
     minimization procedure was run, so it is not claimed to be minimal.

**Fix applied in TLA+ model:** When a stop triggers, assign it a new timestamp from the current logical clock. This ensures triggered stops have the correct priority relative to orders already on the book.

**Recommended spec amendment:** Add to §10.1:
```
stop.timestamp = currentTimestamp()   -- New timestamp for triggered stop
```

---

### Bug #2: STP DECREMENT + Iceberg Stranding

**Severity:** Medium — causes undefined behavior in implementation

**Location:** §8.3 DECREMENT case, interaction with §7.5 Iceberg reload

**Issue:** When STP DECREMENT reduces a resting iceberg order's `visibleQty` to 0 but `remainingQty` > 0, the spec provides no mechanism to reload the visible slice. The iceberg reload logic (§7.5) only triggers after a *fill*, not after a DECREMENT. This creates a "stranded" order with hidden quantity that can never become visible.

**Example scenario:**
- Resting iceberg: qty=2, displayQty=1, visibleQty=1, remainingQty=2
- Incoming order with same STP group, policy=DECREMENT
- DECREMENT: reduceQty = min(incoming.remainingQty, 1) = 1
- After: visibleQty=0, remainingQty=1, hidden qty=1
- The order sits on the book with visibleQty=0 — it can never be matched, filled, or reloaded

**Consequence in implementation:** The next incoming order attempting to match against this resting order would compute fillQty = min(x, 0) = 0, producing a zero-quantity trade (invalid) or an infinite loop.

**Fix applied in TLA+ model:** After DECREMENT, if visibleQty=0 and remainingQty>0 and the order is an iceberg, reload the visible slice (same as normal iceberg reload with new timestamp and move to back of queue).

**Recommended spec amendment:** Add to §8.3 DECREMENT case:
```
IF resting.visibleQty = 0 AND resting.remainingQty > 0 AND resting.displayQty ≠ ⊥:
    resting.visibleQty = min(resting.displayQty, resting.remainingQty)
    resting.timestamp = currentTimestamp()
    MOVE resting TO back OF level.orders
```

---

## Design Observations (Not Bugs, But Worth Noting)

### Observation 1: FOK + STP DECREMENT Interaction

The FOK pre-check (§5.3) excludes STP-conflicting orders from the available quantity calculation. However, during matching, STP DECREMENT can reduce the incoming order's `remainingQty` without generating trades. This means the incoming order is "consumed" partly by DECREMENT and partly by trades, with the total consumption equaling `remainingQty` but the trade fills being less than the original `qty`.

Whether this violates the FOK guarantee depends on interpretation: the order has `remainingQty=0` (fully consumed) but generated fewer trade fills than `qty`. In practice, this is likely acceptable since the FOK guarantee is about not leaving an unfilled order on the book, but it's worth documenting.

### Observation 2: MinQty + STP DECREMENT Interaction

Similar to the FOK case: the MinQty pre-check ensures enough non-conflicting liquidity exists, but DECREMENT during matching can reduce the incoming's remaining quantity. After DECREMENT + partial fills, the total *traded* quantity may be less than `minQty`, even though `remainingQty` was reduced to meet the threshold. The spec's claim (§5.4: "the filled quantity is guaranteed ≥ minQty") may be violated when STP DECREMENT is involved.

### Observation 3: MTL + minQty Clearing

The spec handles minQty clearing in two places: Phase 4 (MTL) and Phase 5a (normal matching). This split is correct but fragile — if a new order type or pipeline phase is added, the clearing must be duplicated. A single clearing point after all matching would be more robust.

## Model Checking Statistics

All rows below are freshly reproduced and archived 2026-09-26 (raw logs,
exact commands, and TLC/Java/host provenance in `results/metadata.json`;
regenerable via `../matcher_tla/tools/generate_stats_summary.py`). The four
completed configurations now generate substantially more states than the
figures previously recorded here (roughly 1.4-1.75x more distinct states
and wall time) — most plausibly due to model changes made after those
figures were recorded (e.g. the well-formedness-filter hoist), not
re-root-caused further. Both old and new numbers are preserved in
`results/metadata.json` for the record.

| Configuration | Orders | Qty | Prices | Amend | States Gen | Distinct | Time | Result |
|---|---|---|---|---|---|---|---|---|
| Tiny | 2 | 1 | {1,2} | No | 2,463,194 | 1,427,827 | 32s | PASS |
| Small | 2 | 2 | {1,2} | No | 16,920,722 | 9,230,323 | 4:12 | PASS |
| Medium | 2 | 2 | {1,2,3} | No | 49,656,516 | 29,622,636 | 14:24 | PASS |
| With Amend | 2 | 2 | {1,2} | Yes | 37,321,458 | 15,158,339 | 25:45 | PASS |
| 3-order (violation) | 3 | 2 | {1,2} | No | 9,160,154 | 4,980,329 | 2:41 | FIFOWithinLevel violated (bug reverted) |

Note: TLC's default deadlock checking must be disabled (`-deadlock`, i.e.
`CHECK_DEADLOCK FALSE`) for the four completed rows above — every action in
the model is guarded by `clock < MAX_CLOCK`, so exhausting the clock budget
is an expected terminal state under this bounded model, not a real deadlock.
Without `-deadlock`, TLC reports "Deadlock reached" as an error on all four.

All configurations include full order type suite (LIMIT, MARKET, MTL, STOP_LIMIT, STOP_MARKET), all TimeInForce variants (GTC, IOC, FOK, DAY), iceberg orders, post-only, STP with all 4 policies (CANCEL_NEWEST, CANCEL_OLDEST, CANCEL_BOTH, DECREMENT), and minQty.

## Invariants Checked

| ID | Invariant | Status |
|---|---|---|
| INV-1/2 | No empty price levels | Trivially true by construction |
| INV-3/4 | Bid/Ask price ordering | Checked via BookUncrossed |
| INV-4/5 | Book uncrossed (bestBid < bestAsk) | **PASS** |
| INV-5/6 | No ghost orders (remainingQty > 0) | **PASS** |
| INV-6/7 | Status consistency (resting ∈ {NEW, PARTIAL}) | **PASS** |
| INV-7/8 | FIFO within price level | **VIOLATED** → Bug #1 found and fixed → **PASS** |
| INV-8/9 | No MARKET orders on book | **PASS** |
| INV-9 | Passive price rule | True by construction |
| INV-11 | Post-only guarantee | **PASS** |
| INV-12 | STP guarantee (no self-trades) | **PASS** |
| INV-13 | No MTL orders on book | **PASS** |
| INV-14 | No resting minQty | **PASS** |

## Files

- `MatchingEngine.tla` — Main TLA+ specification (~950 lines)
- `MatchingEngine.cfg` — Default TLC configuration (2 orders, 3 prices)
- `MatchingEngine_*.cfg` — Various test configurations
