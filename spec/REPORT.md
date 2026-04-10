# Matching Engine TLA+ Verification Report

## Summary

The formal specification (matching-engine-formal-spec.md v1.2.0) was translated into TLA+ and exhaustively model-checked using TLC across multiple configurations. Two specification bugs were discovered and several design observations documented.

## Spec Bugs Found

### Bug #1: STP DECREMENT + Iceberg Stranding

**Severity:** Medium — causes undefined behavior in implementation

**Location:** §8.3 DECREMENT case, interaction with §7.5 Iceberg reload

**Issue:** When STP DECREMENT reduces a resting iceberg order's `visibleQty` to 0 but `remainingQty` > 0, the spec provides no mechanism to reload the visible slice. The iceberg reload logic (§5.1 Step 3) only triggers after a *fill*, not after a DECREMENT. This creates a "stranded" order with hidden quantity that can never become visible.

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

### Bug #2: Stop Trigger Missing Timestamp Update (FIFO Violation)

**Severity:** High — directly violates INV-8 (FIFO within price level)

**Location:** §10.1 EVALUATE_STOPS, interaction with §6.1 INSERT

**Issue:** When a stop order triggers (§10.1), it converts to a LIMIT/MARKET order and enters the PROCESS pipeline. However, the spec does not update the stop order's timestamp. The stop keeps its *original submission timestamp* from when it was first placed. When the triggered order rests on the book after partial matching, it is appended to the back of the price level queue (§6.1) but has an *earlier* timestamp than orders already in that queue.

**Counterexample trace (found by TLC):**
1. SELL LIMIT qty=1 @1 → rests on ask (id=1, timestamp=1)
2. BUY STOP_LIMIT stopPrice=1, price=1, qty=1 → added to stops (id=2, timestamp=2)
3. BUY LIMIT qty=2 @1 → fills against SELL @1 (trade at price=1), triggers the stop
   - Trade triggers stop order 2 (lastTradePrice=1 ≥ stopPrice=1)
   - Stop converts to BUY LIMIT @1 and rests on bid
   - Incoming order 3 (timestamp=3) also rests on bid @1 (partially filled, remainingQty=1)
   - **Result:** bidQ[1] = [order3(ts=3), order2(ts=2)] — FIFO violated!

**Fix applied in TLA+ model:** When a stop triggers, assign it a new timestamp from the current logical clock. This ensures triggered stops have the correct priority relative to orders already on the book.

**Recommended spec amendment:** Add to §10.1:
```
stop.timestamp = currentTimestamp()   -- New timestamp for triggered stop
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

| Configuration | Orders | Qty | Prices | Amend | States Gen | Distinct | Time | Result |
|---|---|---|---|---|---|---|---|---|
| Tiny | 2 | 1 | {1,2} | No | 2,979,719 | 1,123,333 | 20s | PASS |
| Small | 2 | 2 | {1,2} | No | 11,528,343 | 6,037,674 | 1:42 | PASS |
| Medium | 2 | 2 | {1,2,3} | No | 36,700,016 | 21,261,901 | 5:34 | PASS |
| With Amend | 2 | 2 | {1,2} | Yes | 25,209,607 | 9,104,902 | 3:33 | PASS |
| 3-order (partial) | 3 | 2 | {1,2} | No | 45M+ | 26M+ | 10min+ | No violation in explored states |

All configurations include full order type suite (LIMIT, MARKET, MTL, STOP_LIMIT, STOP_MARKET), all TimeInForce variants (GTC, IOC, FOK, DAY), iceberg orders, post-only, STP with all 4 policies (CANCEL_NEWEST, CANCEL_OLDEST, CANCEL_BOTH, DECREMENT), and minQty.

## Invariants Checked

| ID | Invariant | Status |
|---|---|---|
| INV-1/2 | No empty price levels | Trivially true by construction |
| INV-3/4 | Bid/Ask price ordering | Checked via BookUncrossed |
| INV-4/5 | Book uncrossed (bestBid < bestAsk) | **PASS** |
| INV-5/6 | No ghost orders (remainingQty > 0) | **PASS** |
| INV-6/7 | Status consistency (resting ∈ {NEW, PARTIAL}) | **PASS** |
| INV-7/8 | FIFO within price level | **VIOLATED** → Bug #2 found and fixed → **PASS** |
| INV-8/9 | No MARKET orders on book | **PASS** |
| INV-9 | Passive price rule | True by construction |
| INV-11 | Post-only guarantee | **PASS** |
| INV-12 | STP guarantee (no self-trades) | **PASS** |
| INV-13 | No MTL orders on book | **PASS** |
| INV-14 | No resting minQty | **PASS** |

## Files

- `MatchingEngine.tla` — Main TLA+ specification (~850 lines)
- `MatchingEngine.cfg` — Default TLC configuration (3 orders, 3 prices)
- `MatchingEngine_*.cfg` — Various test configurations
