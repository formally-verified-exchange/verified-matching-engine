#include "types.h"
#include "engine.h"
#include <chrono>
#include <cstdio>
#include <cstdint>

// ── LCG pseudo-random (same as ~/matcher for reproducibility) ──
static uint64_t lcg_state = 0x123456789ABCDEF0ULL;

static inline uint64_t lcg_next() {
    lcg_state = lcg_state * 6364136223846793005ULL + 1442695040888963407ULL;
    return lcg_state;
}

static OrderInput mkLim(OrderId id, Side s, Price px, Quantity qty, TimeInForce tif) {
    OrderInput o{}; o.id=id; o.side=s; o.orderType=OrderType::LIMIT;
    o.timeInForce=tif; o.price=px; o.quantity=qty; return o;
}

// ── Deep-book benchmark (ported from ~/matcher/main.c:2785) ──
static void benchmark_deep_book() {
    printf("\n--- Deep-Book Benchmark ---\n");

    NullListener nl;
    Engine<NullListener> engine(nl);

    // Seed book: 10 bid levels (991..1000) x 50, 10 ask levels (1001..1010) x 50
    for (int lvl = 0; lvl < 10; lvl++) {
        for (int j = 0; j < 50; j++) {
            OrderId bid = engine.assignId();
            engine.submitOrder(mkLim(bid, Side::BUY,
                                     991 + lvl, 50, TimeInForce::GTC));
            OrderId ask = engine.assignId();
            engine.submitOrder(mkLim(ask, Side::SELL,
                                     1001 + lvl, 50, TimeInForce::GTC));
        }
    }

    // Track high-water ID for random cancel/amend targets
    constexpr OrderId MAX_ID = 1u << 20;

    const uint64_t TARGET_TRADES = 10'000'000ULL;
    uint64_t totalOps = 0;

    auto t0 = std::chrono::high_resolution_clock::now();

    while (engine.tradeCount() < TARGET_TRADES) {
        uint64_t r = lcg_next();
        totalOps++;

        // Step 1: Replenish one side to keep book deep
        {
            Side s = (r & 1) ? Side::BUY : Side::SELL;
            Price price;
            if (s == Side::BUY)
                price = 991 + (Price)(lcg_next() % 10);
            else
                price = 1001 + (Price)(lcg_next() % 10);
            Quantity qty = (Quantity)(20 + lcg_next() % 80);
            OrderId id = engine.assignId();
            engine.submitOrder(mkLim(id, s, price, qty, TimeInForce::GTC));
        }

        // Step 2: Aggressive order that crosses spread → trade
        {
            r = lcg_next();
            Side s = (r & 1) ? Side::BUY : Side::SELL;
            Price price;
            if (s == Side::BUY)
                price = 1001 + (Price)(lcg_next() % 10);
            else
                price = 991 + (Price)(lcg_next() % 10);
            Quantity qty = (Quantity)(1 + lcg_next() % 10);
            OrderId id = engine.assignId();
            engine.submitOrder(mkLim(id, s, price, qty, TimeInForce::IOC));
        }

        // Step 3: Cancel 2 random orders + occasionally amend
        {
            OrderId c1 = (OrderId)(1 + lcg_next() % MAX_ID);
            OrderId c2 = (OrderId)(1 + lcg_next() % MAX_ID);
            engine.cancelOrder(c1);
            engine.cancelOrder(c2);
            if (lcg_next() % 5 == 0) {
                OrderId aid = (OrderId)(1 + lcg_next() % MAX_ID);
                Quantity nq = (Quantity)(1 + lcg_next() % 40);
                engine.amendOrder(aid, 0, nq);
            }
        }
    }

    auto t1 = std::chrono::high_resolution_clock::now();
    double elapsed = std::chrono::duration<double>(t1 - t0).count();

    uint64_t trades = engine.tradeCount();

    printf("Total ops:    %llu\n", (unsigned long long)totalOps);
    printf("Trades:       %llu\n", (unsigned long long)trades);
    printf("Trade ratio:  %.1f%%\n", 100.0 * trades / totalOps);
    printf("Time:         %.3f s\n", elapsed);
    printf("Ops/sec:      %.2f M\n", totalOps / elapsed / 1e6);
    printf("Trades/sec:   %.2f M\n", trades / elapsed / 1e6);
    printf("Avg trade:    %.0f ns\n", elapsed / trades * 1e9);
    printf("───────────────────────────────────────────\n");
    printf("Peak orders:       %zu\n", engine.peakOrders());
    printf("Orders allocated:  %zu\n", engine.ordersAllocated());
    printf("Orders freed:      %zu\n", engine.ordersFreed());
    printf("Peak levels:       %zu\n", engine.peakLevels());
    printf("Active orders:     %zu\n", engine.activeOrders());
    printf("Active levels:     %zu\n", engine.activeLevels());
}

int main() {
    benchmark_deep_book();
    return 0;
}
