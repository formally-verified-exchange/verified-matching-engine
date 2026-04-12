# Matching Engine Implementation v2 — Claude Code Prompt

Run with: `claude --dangerously-skip-permissions`

---

## Prompt

You are building a **price-time priority (FIFO) matching engine** in C++ from a formal specification. The complete formal spec is in `matching-engine-formal-spec.md` — read it fully before writing any code. It is your single source of truth for every rule, invariant, and edge case.

### Design Philosophy

There exists a known elegant, compact solution to this problem. Your goal is a **production-grade matching engine** — one that is fast, correct, and operationally sound. This means no memory leaks, no silent overwrites, no fixed-capacity limits that crash under load, and proper resource lifecycle management.

The guiding principle: **correct first, fast second, clever never.**

1. **Production correctness over benchmark heroics.** Every order that is cancelled or filled must have its memory returned to the pool. Order IDs must not silently collide. The engine must handle long-running sessions without unbounded memory growth. These properties matter more than squeezing the last nanosecond.

2. **Standard containers with pool allocators.** The STL containers are battle-tested, well-understood, and correct. Their performance problem is `malloc`/`free` — solve that with pool-backed allocators and they become fast. Do not hand-roll data structures that `std::map` or `std::unordered_map` already solve correctly.

3. **Compact codebase.** Fewer lines, fewer files, fewer abstractions. Do not over-engineer. Target the smallest correct solution. But do not sacrifice correctness for brevity — if proper cleanup takes 5 extra lines, write them.

### Mandatory Architecture Decisions

These are not suggestions. Follow them.

**Book structure — `std::map` with pool allocator:**
```
std::map<Price, PriceLevel*, std::greater<Price>, PoolAllocator<...>>  bids;  // descending
std::map<Price, PriceLevel*, std::less<Price>, PoolAllocator<...>>     asks;  // ascending
```
- `begin()` gives best bid/ask in O(1) amortized
- Insert at correct sorted position in O(log P) — no hand-rolled linked list
- `erase()` when a level empties — no ghost levels
- The `std::map` node allocator pulls from a pool, eliminating malloc overhead
- PriceLevel nodes themselves come from a separate pool

**Order lookup — `std::unordered_map` with pool allocator:**
```
std::unordered_map<OrderId, Order*, std::hash<OrderId>, std::equal_to<OrderId>, PoolAllocator<...>>  orderIndex;
```
- Supports any OrderId scheme (sparse, non-sequential, client-assigned)
- Proper `erase()` on cancel/fill — no stale entries, no silent overwrites
- Pool allocator eliminates per-node malloc

**Order queue within a price level — intrusive doubly-linked list:**
- Each Order has `prev`/`next` pointers (intrusive — no separate node allocation)
- O(1) push back (new orders), O(1) pop front (matching), O(1) removal by pointer (cancels)
- FIFO ordering maintained by construction

**Order storage — pool allocator with free list recycling:**
- All Order objects allocated from a slab/pool allocator
- `allocOrder()` returns a slot — either from the free list or by bumping a pointer
- `freeOrder()` returns the slot to the free list for reuse
- No monotonic memory growth. A cancelled order's memory is reused by the next submission
- Same pattern for PriceLevel objects and Trade objects

**PriceLevel storage — pool allocator with free list recycling:**
- PriceLevel objects allocated from their own pool
- When a level's order queue becomes empty, remove it from the `std::map`, return it to the pool

### Pool Allocator Design

There is a directory `src/allocator/` that may contain allocator implementations. Read them first and use them if they fit. If they don't support free-list recycling, build a simple one. A correct pool allocator with recycling is ~30 lines:

```
// Conceptual — adapt to your needs
template<typename T>
struct Pool {
    std::vector<T> slab;        // backing storage
    std::vector<T*> freeList;   // recycled slots
    size_t cursor = 0;          // bump pointer into slab

    T* alloc() {
        if (!freeList.empty()) { auto* p = freeList.back(); freeList.pop_back(); return p; }
        return &slab[cursor++];
    }
    void free(T* p) { freeList.push_back(p); }
};
```

The key property: `alloc()` and `free()` are both O(1). No system allocator calls on the hot path.

### Performance Target

**5,000,000 orders per second** sustained throughput on a single core. This is the hard gate.

What this implies:
- ~200ns per order budget
- No system allocator calls on the hot path — pools handle everything
- Pool allocators for `std::map` and `std::unordered_map` node allocation eliminate their main performance bottleneck
- No virtual dispatch, no exceptions on the hot path
- The design is inherently fast because the containers are correct and the allocator is fast

What this does NOT require:
- No flat arrays indexed by OrderId — use `std::unordered_map`
- No fixed compile-time capacity limits — pools grow dynamically
- No hand-rolled hash tables — use `std::unordered_map` with pool allocator
- No hand-rolled sorted lists — use `std::map` with pool allocator
- No "never free" arena patterns — recycle properly

### What to Implement (from the spec)

Read `matching-engine-formal-spec.md` and implement ALL of:

1. **Order types:** LIMIT, MARKET, MARKET_TO_LIMIT, STOP_LIMIT, STOP_MARKET
2. **Time in force:** GTC, GTD, IOC, FOK, DAY
3. **Modifiers:** Iceberg (displayQty), Post-Only (reject policy), minQty
4. **STP:** All four policies (CANCEL_NEWEST, CANCEL_OLDEST, CANCEL_BOTH, DECREMENT), per-order stpPolicy
5. **Operations:** New order (PROCESS pipeline), Cancel, Amend (cancel-replace)
6. **Matching:** Price-time priority, passive price rule (EP-1)
7. **Stop triggering:** Including cascading triggers with depth safeguard
8. **All well-formedness checks** (WF-1 through WF-20)
9. **All invariants** (INV-1 through INV-14) — these are your correctness criteria

### Resource Lifecycle Rules

These must be followed. They distinguish a production engine from a toy.

1. **Every `allocOrder()` must have a corresponding `freeOrder()`.** When an order reaches terminal state (FILLED, CANCELLED, EXPIRED), remove it from the order index and return it to the pool.

2. **Every PriceLevel allocation must have a corresponding free.** When the last order at a price level is removed, erase the level from the `std::map` and return the PriceLevel to its pool.

3. **The order index must never contain stale entries.** After cancel/fill/expire, `orderIndex.erase(orderId)` must be called. Looking up a cancelled order must return "not found."

4. **No silent OrderId collision.** If a client submits an order with an ID that already exists in the index and is still active, reject it. Do not overwrite.

5. **Stop orders in the stop collection must also be freed** when cancelled or when the engine is destroyed.

### Suggested File Structure

```
src/
  allocator/            ← Pre-existing pool allocators (read these first)
  pool.h                ← Pool allocator with free-list recycling (if needed)
  types.h               ← Core types: Side, OrderType, TimeInForce, Order, Trade, etc.
  order_book.h/.cpp     ← Book structure: std::map-based levels, intrusive order queues
  engine.h/.cpp         ← PROCESS pipeline, MATCH, DISPOSE, cancel, amend, stops
  events.h              ← Event types and minimal callback/sink interface
tests/
  test_correctness.cpp  ← Correctness tests covering every rule in the spec
  test_performance.cpp  ← Throughput benchmark: must prove ≥5M orders/sec
```

Fewer files is fine. More than this needs justification.

### Execution Plan

Do this in order. Do not ask for permission or clarification — the spec has everything you need.

**Step 1 — Read.** Read `matching-engine-formal-spec.md` completely. Read every file in `src/allocator/`. Understand what you have to work with.

**Step 2 — Design.** Think extensively. Decide exact struct layouts, which pool backs which type, how `std::map` and `std::unordered_map` integrate with the pool allocators. Verify the resource lifecycle: trace an order from submission through fill/cancel to memory reclamation. Make sure there are no leaks.

**Step 3 — Implement.** Write all source files. Keep the total line count low while maintaining correctness. Every cancelled/filled order must be freed. Every empty level must be removed. The order index must stay clean.

**Step 4 — Correctness tests.** Write comprehensive tests covering:
- Basic LIMIT order matching (single fill, sweep, partial fill)
- MARKET order (full fill, partial cancel)
- MARKET_TO_LIMIT (fill + convert + rest)
- IOC, FOK, GTC, GTD, DAY semantics
- Iceberg: visible qty, reload, time priority loss
- Post-Only: reject when would cross, accept when would rest
- minQty: reject when insufficient, clear after threshold met
- STP: all four policies with conflict detection
- Stop orders: trigger on trade, cascade, immediate trigger
- Cancel and Amend: priority preservation rules
- **Resource lifecycle:** after cancelling/filling all orders, verify pool free list size equals total allocated (no leaks)
- **OrderId collision:** submitting a duplicate active ID must be rejected
- **Order index cleanliness:** looking up a cancelled/filled order returns not found
- Appendix B walk-through from the spec (exact sequence, exact results)
- All invariants hold after every operation

**Step 5 — Performance tests.** Write a benchmark that:
- Pre-generates a realistic order stream (mix of new orders, cancels, amends)
- Order mix: ~60% LIMIT, ~15% MARKET, ~10% cancel, ~10% amend, ~5% other
- Measures wall-clock time for processing N orders (N ≥ 5,000,000)
- Reports orders/second
- **Must achieve ≥ 5,000,000 orders/sec** or the implementation fails
- Also report memory usage: peak pool sizes, free list utilization
- Run the benchmark. If it fails the throughput target, profile and optimize until it passes.

**Step 6 — Report.** When all tests pass and performance target is met, print a summary:
- Total line count (core engine, excluding tests and pre-existing allocators)
- Orders/second achieved
- Memory profile: peak orders allocated, peak levels allocated, free list reuse rate
- Test results (all pass/fail)
- Confirmation that resource lifecycle is clean (no leaks, no stale index entries)

### Rules

- Do NOT ask questions. The spec is complete.
- Do NOT use flat arrays indexed by OrderId — use `std::unordered_map`.
- Do NOT use hand-rolled hash tables or sorted lists — use `std::unordered_map` and `std::map`.
- DO use pool allocators for all hot-path allocations including map/unordered_map node allocation.
- DO implement proper free-list recycling — cancelled/filled orders return to pool.
- DO erase from the order index on cancel/fill/expire.
- DO erase empty price levels from the map.
- DO reject duplicate active OrderIds.
- DO use intrusive linked lists for the order queue within a price level.
- DO compile with `-O3 -march=native` for benchmarks.
- DO use `static_assert` and `assert` liberally.
- When done, report that you are done.
