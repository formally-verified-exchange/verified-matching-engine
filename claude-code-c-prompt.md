# Matching Engine in C — Claude Code Prompt

Run with: `claude --dangerously-skip-permissions`

---

## Prompt

You are building a **price-time priority (FIFO) matching engine** in **pure C** (C11 or C17). Not C++. Not "C-style C++." Pure C — compiled with `gcc -std=c17` or `clang -std=c17`. The complete formal spec is in `matching-engine-formal-spec.md` — read it fully before writing any code.

### Why C

We already have a C++ implementation. This is a deliberate exercise in minimalism. C forces you to confront every allocation, every data structure choice, every branch — there is no abstraction to hide behind. No templates, no RAII, no `std::map`, no virtual dispatch, no exceptions, no operator overloading. Just structs, functions, pointers, and the machine.

The hypothesis: a carefully written C implementation will be faster than the C++ version because there is less abstraction overhead, more predictable memory layout, and more control over every instruction on the hot path. We want to test that hypothesis.

### Design Philosophy

1. **Everything is a struct. Every struct has a known size.** No opaque types, no void pointer indirection on the hot path. The compiler and the CPU should know the exact memory layout of every object.

2. **Pool allocators for everything.** All Orders, PriceLevels, and Trades come from typed, pre-sized pools with free-list recycling. `alloc()` is a pointer bump or free-list pop. `free()` is a free-list push. Zero calls to `malloc`/`free` on the hot path.

3. **Intrusive data structures.** Orders carry their own `prev`/`next` pointers for the FIFO queue. PriceLevels carry their own `prev`/`next` pointers for the sorted level list. No separate node allocations. No pointer chasing through allocator metadata.

4. **Flat array for order lookup.** `Order* order_index[MAX_ORDERS]` — indexed by OrderId. OrderIds are monotonic, dense, engine-assigned. O(1) lookup, O(1) cancel, zero overhead. If the ID space needs to be sparse or client-assigned, use an open-addressing hash table — but start with the flat array.

5. **Compact hot path.** The common case — incoming LIMIT order, single fill against best contra, update book — should execute in a tight sequence of pointer operations with no branches that aren't predicted. Profile this path. Count the instructions.

6. **Production correctness.** Proper free-list recycling (no arena leak), clean order index (erase on cancel/fill), no silent ID collision, no fixed limits that crash (assert on overflow is acceptable for safety, but document the limits).

### Architecture

```
src/
  types.h             ← All types: enums, Order, Trade, PriceLevel, Event
  pool.h / pool.c     ← Generic typed pool allocator with free-list recycling
  book.h / book.c     ← Order book: sorted intrusive level lists, FIFO order queues
  engine.h / engine.c ← PROCESS pipeline, MATCH, DISPOSE, cancel, amend, stops, STP
  main.c              ← Test runner + benchmark

  -- OR if you prefer fewer files:
  matching_engine.h   ← All types and function declarations
  matching_engine.c   ← All implementation
  main.c              ← Tests + benchmark
```

Fewer files is better. If the entire engine fits in one `.h` and one `.c` plus a `main.c`, do that. The C spirit is: one thing, done well, in one place.

### Data Structure Decisions

**Order struct — keep it tight:**

```c
typedef struct Order {
    uint32_t id;
    uint32_t qty;              // original quantity
    uint32_t remaining_qty;
    uint32_t visible_qty;
    uint32_t min_qty;          // 0 if not set
    uint32_t display_qty;      // 0 if not iceberg
    int64_t  price;            // 0 for MARKET
    int64_t  stop_price;       // 0 for non-stop
    uint64_t timestamp;
    uint64_t expire_time;      // 0 if not GTD
    uint32_t stp_group;        // 0 if no STP
    uint8_t  side;             // BUY=0, SELL=1
    uint8_t  order_type;       // LIMIT=0, MARKET=1, MTL=2, STOP_LIMIT=3, STOP_MARKET=4
    uint8_t  tif;              // GTC=0, GTD=1, IOC=2, FOK=3, DAY=4
    uint8_t  status;           // NEW=0, PARTIAL=1, FILLED=2, CANCELLED=3, ...
    uint8_t  stp_policy;       // CANCEL_NEWEST=0, ...
    uint8_t  post_only;        // 0 or 1
    uint8_t  _pad[2];          // explicit padding to known alignment
    struct Order *prev;        // intrusive queue link
    struct Order *next;        // intrusive queue link
} Order;
```

Think about the size. Pack the enums into `uint8_t`. Put the frequently accessed fields (price, remaining_qty, visible_qty, side) near the top for cache line efficiency. `prev`/`next` at the end. Aim for the struct fitting in 1-2 cache lines (64-128 bytes).

Use `static_assert(sizeof(Order) == expected_size, "Order struct size changed")` to lock the layout.

**PriceLevel — intrusive doubly-linked list of levels, with intrusive order queue:**

```c
typedef struct PriceLevel {
    int64_t price;
    struct PriceLevel *prev;   // intrusive level list link
    struct PriceLevel *next;
    Order *head;               // FIFO queue head (highest priority)
    Order *tail;               // FIFO queue tail (lowest priority)
    uint32_t order_count;      // optional: track count for fast empty check
} PriceLevel;
```

**Book — two sorted doubly-linked lists of PriceLevels:**

```c
typedef struct {
    PriceLevel *best_bid;      // head of bid list (descending price)
    PriceLevel *best_ask;      // head of ask list (ascending price)
    // ... stop list, order index, pools, etc.
} OrderBook;
```

`best_bid` points to the highest-priced bid level. Following `->next` gives decreasing prices. `best_ask` points to the lowest-priced ask level. Following `->next` gives increasing prices. Insert maintains sort order by walking from best toward worst.

**Pool allocator:**

```c
typedef struct {
    void *slab;                // backing memory (array of T)
    void **free_list;          // stack of freed pointers
    uint32_t free_count;       // number of items in free list
    uint32_t cursor;           // bump pointer index
    uint32_t capacity;         // total slots
    uint32_t item_size;        // sizeof(T)
} Pool;

void *pool_alloc(Pool *p);    // pop from free_list, or bump cursor
void  pool_free(Pool *p, void *ptr);  // push to free_list
```

Both O(1). No branching except the free_list empty check.

Alternatively, use a macro-based typed pool to avoid `void*` and casts:

```c
#define DEFINE_POOL(NAME, TYPE, CAP)                          \
    typedef struct {                                           \
        TYPE items[CAP];                                       \
        TYPE *free_stack[CAP];                                 \
        uint32_t free_top;                                     \
        uint32_t cursor;                                       \
    } NAME##Pool;                                              \
    static inline TYPE *NAME##_alloc(NAME##Pool *p) { ... }    \
    static inline void NAME##_free(NAME##Pool *p, TYPE *x) { ... }
```

Your choice. The macro version avoids all casts and gives type safety at zero runtime cost.

### Event / Callback System

Keep it minimal. A function pointer callback:

```c
typedef void (*EventCallback)(const Event *event, void *ctx);

typedef struct {
    // ... book, pools, etc.
    EventCallback on_event;
    void *event_ctx;
} Engine;
```

For the benchmark, set `on_event` to a no-op or a counter. For tests, set it to a function that records events in an array for verification.

Alternatively, skip callbacks entirely — have `process_order` return a small stack-allocated array of events/trades. Simpler, no function pointer overhead on the hot path. The benchmark can just ignore the return.

### What to Implement (from the spec)

Read `matching-engine-formal-spec.md` and implement ALL of:

1. **Order types:** LIMIT, MARKET, MARKET_TO_LIMIT, STOP_LIMIT, STOP_MARKET
2. **Time in force:** GTC, GTD, IOC, FOK, DAY
3. **Modifiers:** Iceberg (display_qty), Post-Only (reject policy), min_qty
4. **STP:** All four policies, per-order stp_policy
5. **Operations:** New order (PROCESS pipeline), Cancel, Amend
6. **Matching:** Price-time priority, passive price rule
7. **Stop triggering:** Including cascading triggers with depth limit
8. **Well-formedness checks** (WF-1 through WF-20)
9. **All invariants** (INV-1 through INV-14) as debug-mode assertions

**Critical — include the two bug fixes from the paper:**
- **BUG-1 fix:** When a stop order triggers, assign `stop->timestamp = engine->clock++` before re-entering the pipeline. Without this, FIFO is violated.
- **BUG-2 fix:** After STP DECREMENT, if `resting->visible_qty == 0 && resting->remaining_qty > 0 && resting->display_qty > 0`, reload the iceberg visible slice, refresh timestamp, move to back of queue.

### Resource Lifecycle

1. Every `pool_alloc` has a corresponding `pool_free`. Cancelled/filled orders are freed.
2. Empty price levels are freed back to the level pool.
3. The order index is cleaned on cancel/fill — `order_index[id] = NULL`.
4. Duplicate active OrderId submission is rejected.
5. Stop orders are freed when cancelled or triggered.

### Performance Target

**10,000,000 orders per second** sustained on a single core.

This target is deliberately higher than the C++ version. The rationale: no `std::map` iterator overhead, no template abstraction, no RAII destructor chains, no `std::unordered_map` hash node indirection. Pure C with intrusive data structures and pool allocators should be faster.

If the first pass doesn't hit 10M, profile and optimize:
- Check struct size and alignment
- Check branch prediction on the hot path (LIMIT order, single fill)
- Check cache misses — are orders and levels in the same pool region?
- Consider `__builtin_expect` for unlikely branches (stop triggers, STP conflicts, iceberg reload)
- Consider `restrict` pointers where aliasing is provably absent

### Test Suite

Write tests as plain C functions with `assert()`. No test framework needed.

```c
void test_basic_limit_match(void);
void test_market_sweep(void);
void test_mtl_fill_convert_rest(void);
void test_fok_reject_accept(void);
void test_ioc_partial_cancel(void);
void test_iceberg_reload_priority(void);
void test_post_only_reject(void);
void test_min_qty_reject_accept_clear(void);
void test_stp_all_policies(void);
void test_stop_trigger_cascade(void);
void test_cancel_amend(void);
void test_appendix_b_walkthrough(void);
void test_bug1_fifo_holds(void);
void test_bug2_iceberg_decrement_reload(void);
void test_resource_lifecycle(void);   // alloc/free counts match
```

Test `test_resource_lifecycle` is critical: after processing a sequence of orders and cancelling/filling all of them, verify that `pool.free_count + (pool.capacity - pool.cursor) == pool.capacity` for both order and level pools. No leaked slots.

### Benchmark

```c
void benchmark(void) {
    Engine engine;
    engine_init(&engine, /*max_orders=*/8000000);

    struct timespec start, end;
    const int N = 10000000;

    // Pre-generate order stream
    // Mix: ~60% LIMIT, ~15% MARKET, ~10% cancel, ~10% amend, ~5% other
    // Use a simple LCG for deterministic pseudo-random generation

    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int i = 0; i < N; i++) {
        process_order(&engine, &orders[i]);
    }
    clock_gettime(CLOCK_MONOTONIC, &end);

    double elapsed = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    printf("Orders:     %d\n", N);
    printf("Time:       %.3f s\n", elapsed);
    printf("Throughput: %.0f orders/sec\n", N / elapsed);
    printf("Latency:    %.0f ns/order\n", elapsed / N * 1e9);
    printf("Target:     10,000,000 orders/sec\n");
    printf("Result:     %s\n", (N / elapsed >= 10000000) ? "PASS" : "FAIL");
}
```

Compile with: `gcc -O3 -march=native -std=c17 -o matching_engine main.c engine.c pool.c`

### Comparison with C++ Version

After the benchmark passes, report a comparison:

```
┌──────────┬───────────────┬────────────┬─────────────┬────────────────┐
│ Language │ Throughput    │ Latency    │ Core Lines  │ Design         │
├──────────┼───────────────┼────────────┼─────────────┼────────────────┤
│ C        │ ??? ops/sec   │ ??? ns/op  │ ??? lines   │ intrusive/pool │
├──────────┼───────────────┼────────────┼─────────────┼────────────────┤
│ C++      │ (from prev)   │ (from prev)│ (from prev) │ std::map/pool  │
└──────────┴───────────────┴────────────┴─────────────┴────────────────┘
```

Include: line count (core engine only, excluding tests/benchmark), struct sizes, peak memory usage.

### Execution Plan

**Step 1 — Read.** Read `matching-engine-formal-spec.md`. Note both bug fixes.

**Step 2 — Design.** Decide exact struct layouts. Write them down. `static_assert` the sizes. Decide pool capacities. Decide the order index strategy (flat array vs hash table). Decide the event/callback approach.

**Step 3 — Implement.** Write the pool, the book operations, the matching loop, the full PROCESS pipeline, cancel, amend, stops, STP. Keep it compact — target under 1500 lines for the core engine (excluding tests/benchmark).

**Step 4 — Test.** Write and run all tests. Every test must pass. Debug until they do.

**Step 5 — Benchmark.** Run the throughput benchmark. Must hit ≥10M orders/sec. If not, profile with `perf stat` or `perf record` and optimize. Report the final number.

**Step 6 — Report.** Line count, throughput, latency, struct sizes, memory usage, comparison table, any design notes.

### Rules

- Pure C. No C++ features. No `//` comments are fine (C99+). No `new`, `delete`, `class`, `template`, `namespace`, `std::`, `virtual`, `throw`, `auto` (C++ sense), `nullptr` (use `NULL`), `bool` is fine (from `<stdbool.h>`).
- Compile with `gcc -std=c17 -Wall -Wextra -Werror -O3 -march=native`. Zero warnings.
- Do NOT use `malloc`/`free` on the hot path. Pools only.
- DO use `static_assert` for struct sizes and alignments.
- DO use `assert` for invariant checks in debug mode.
- DO use `__attribute__((hot))` on the main matching function if using GCC.
- DO use `restrict` where pointer aliasing is provably absent.
- DO use `__builtin_expect` sparingly for genuinely unlikely branches.
- DO implement proper resource lifecycle — free on cancel/fill, clean order index.
- DO include both bug fixes from the paper.
- When done, report that you are done.
