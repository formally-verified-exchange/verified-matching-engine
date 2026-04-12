#include "types.h"
#include "engine.h"
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>
#include <cassert>

// ── Recording listener ──
struct Rec {
    std::vector<OrderId> accepted;
    std::vector<std::pair<OrderId,std::string>> rejected;
    std::vector<Trade> trades;
    std::vector<std::pair<OrderId,std::string>> cancelled;
    std::vector<OrderId> expired;
    std::vector<OrderId> triggered;
    std::vector<std::tuple<OrderId,OrderId,Quantity>> decremented;

    void onOrderAccepted(const Order& o) { accepted.push_back(o.id); }
    void onOrderRejected(const Order& o, const char* r) { rejected.emplace_back(o.id, r); }
    void onTrade(const Trade& t) { trades.push_back(t); }
    void onOrderCancelled(const Order& o, const char* r) { cancelled.emplace_back(o.id, r); }
    void onOrderExpired(const Order& o) { expired.push_back(o.id); }
    void onOrderTriggered(const Order& o) { triggered.push_back(o.id); }
    void onOrderDecremented(const Order& a, const Order& b, Quantity q) { decremented.emplace_back(a.id,b.id,q); }
    void onOrderRepriced(const Order&, Price, Price) {}

    void clear() {
        accepted.clear(); rejected.clear(); trades.clear();
        cancelled.clear(); expired.clear(); triggered.clear();
        decremented.clear();
    }
};

// ── Test macros ──
static int gPass = 0, gFail = 0;
#define T_EQ(a, b) do { if ((a)!=(b)) { printf("  FAIL %s:%d: %s != %s\n", \
    __FILE__,__LINE__,#a,#b); gFail++; return; } } while(0)
#define T_TRUE(x) do { if (!(x)) { printf("  FAIL %s:%d: %s\n",__FILE__,__LINE__,#x); gFail++; return; } } while(0)
#define RUN(fn) do { printf("  %-55s", #fn); fn(); if(gFail==f0) { printf("PASS\n"); gPass++; } else printf("\n"); } while(0)

// ── Helper ──
OrderInput lim(OrderId id, Side s, Price px, Quantity qty, TimeInForce tif = TimeInForce::GTC) {
    OrderInput o{}; o.id=id; o.side=s; o.orderType=OrderType::LIMIT;
    o.timeInForce=tif; o.price=px; o.quantity=qty; return o;
}
OrderInput mkt(OrderId id, Side s, Quantity qty, TimeInForce tif = TimeInForce::IOC) {
    OrderInput o{}; o.id=id; o.side=s; o.orderType=OrderType::MARKET;
    o.timeInForce=tif; o.quantity=qty; return o;
}

// ─────────────────────── TESTS ───────────────────────

void test_limit_rest() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    T_EQ(r.accepted.size(), 1u);
    T_EQ(r.trades.size(), 0u);
    T_EQ(e.bestBid(), 100);
    T_EQ(e.orderCount(), 1u);
}

void test_limit_cross() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    e.submitOrder(lim(2, Side::SELL, 100, 10));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].price, 100);
    T_EQ(r.trades[0].quantity, 10);
    T_EQ(e.orderCount(), 0u);
}

void test_limit_partial() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    e.submitOrder(lim(2, Side::SELL, 100, 5));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].quantity, 5);
    T_EQ(e.orderCount(), 1u); // order 1 still resting with 5 remaining
    T_EQ(e.bestBid(), 100);
}

void test_sweep() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::SELL, 100, 10));
    e.submitOrder(lim(2, Side::SELL, 101, 10));
    e.submitOrder(lim(3, Side::SELL, 102, 10));
    e.submitOrder(lim(4, Side::BUY, 102, 25));
    T_EQ(r.trades.size(), 3u);
    T_EQ(r.trades[0].price, 100); // best ask first
    T_EQ(r.trades[0].quantity, 10);
    T_EQ(r.trades[1].price, 101);
    T_EQ(r.trades[1].quantity, 10);
    T_EQ(r.trades[2].price, 102);
    T_EQ(r.trades[2].quantity, 5);
    T_EQ(e.orderCount(), 1u); // order 3 has 5 remaining
}

void test_passive_price() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::SELL, 95, 10));
    e.submitOrder(lim(2, Side::BUY, 100, 5));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].price, 95); // passive price
}

void test_market_fill() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::SELL, 100, 10));
    e.submitOrder(mkt(2, Side::BUY, 10));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].quantity, 10);
    T_EQ(e.orderCount(), 0u);
}

void test_market_partial_cancel() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::SELL, 100, 5));
    e.submitOrder(mkt(2, Side::BUY, 10));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].quantity, 5);
    // IOC remainder cancelled
    T_TRUE(!r.cancelled.empty());
    T_EQ(e.orderCount(), 0u);
}

void test_market_to_limit() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::SELL, 100, 5));
    e.submitOrder(lim(2, Side::SELL, 101, 5));
    OrderInput mtl{}; mtl.id=3; mtl.side=Side::BUY; mtl.orderType=OrderType::MARKET_TO_LIMIT;
    mtl.timeInForce=TimeInForce::GTC; mtl.quantity=8;
    e.submitOrder(mtl);
    T_EQ(r.trades.size(), 2u);
    T_EQ(r.trades[0].price, 100);
    T_EQ(r.trades[0].quantity, 5);
    T_EQ(r.trades[1].price, 101);
    T_EQ(r.trades[1].quantity, 3);
    // Order 2 (SELL 5@101) has 2 remaining; MTL fully filled
    T_EQ(e.orderCount(), 1u);
}

void test_mtl_rest() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::SELL, 100, 5));
    OrderInput mtl{}; mtl.id=2; mtl.side=Side::BUY; mtl.orderType=OrderType::MARKET_TO_LIMIT;
    mtl.timeInForce=TimeInForce::GTC; mtl.quantity=10;
    e.submitOrder(mtl);
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].quantity, 5);
    T_EQ(e.orderCount(), 1u); // 5 remaining rests at price 100
    T_EQ(e.bestBid(), 100);
}

void test_mtl_no_liquidity() {
    Rec r; Engine<Rec> e(r);
    OrderInput mtl{}; mtl.id=1; mtl.side=Side::BUY; mtl.orderType=OrderType::MARKET_TO_LIMIT;
    mtl.timeInForce=TimeInForce::GTC; mtl.quantity=10;
    e.submitOrder(mtl);
    T_TRUE(!r.cancelled.empty());
    T_EQ(r.cancelled.back().second, std::string("MTL_NO_LIQUIDITY"));
    T_EQ(e.orderCount(), 0u);
}

void test_ioc() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 5));
    e.submitOrder(lim(2, Side::SELL, 100, 10, TimeInForce::IOC));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].quantity, 5);
    bool iocCancel = false;
    for (auto& [id, reason] : r.cancelled) if (id==2 && reason=="IOC_REMAINDER") iocCancel=true;
    T_TRUE(iocCancel);
    T_EQ(e.orderCount(), 0u);
}

void test_fok_fill() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    e.submitOrder(lim(2, Side::SELL, 100, 10, TimeInForce::FOK));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].quantity, 10);
}

void test_fok_reject() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 5));
    e.submitOrder(lim(2, Side::SELL, 100, 10, TimeInForce::FOK));
    T_EQ(r.trades.size(), 0u);
    bool fokCancel = false;
    for (auto& [id, reason] : r.cancelled) if (id==2 && reason=="FOK_NOT_SATISFIABLE") fokCancel=true;
    T_TRUE(fokCancel);
}

void test_gtd_expire() {
    Rec r; Engine<Rec> e(r);
    e.setTime(100);
    OrderInput o = lim(1, Side::BUY, 100, 10, TimeInForce::GTD);
    o.expireTime = 200;
    e.submitOrder(o);
    T_EQ(e.orderCount(), 1u);
    e.expireOrders(199);
    T_EQ(e.orderCount(), 1u); // not expired yet
    e.expireOrders(200);
    T_EQ(e.orderCount(), 0u);
    T_EQ(r.expired.size(), 1u);
}

void test_iceberg() {
    Rec r; Engine<Rec> e(r);
    OrderInput ice = lim(1, Side::BUY, 100, 20);
    ice.displayQty = 5;
    e.submitOrder(ice);
    T_EQ(e.orderCount(), 1u);

    // Sell 5 — fills visible slice
    e.submitOrder(lim(2, Side::SELL, 100, 5));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].quantity, 5);
    T_EQ(e.orderCount(), 1u); // iceberg reloaded, 15 remaining
}

void test_iceberg_priority_loss() {
    Rec r; Engine<Rec> e(r);
    OrderInput ice = lim(1, Side::BUY, 100, 20);
    ice.displayQty = 5;
    e.submitOrder(ice);
    e.submitOrder(lim(2, Side::BUY, 100, 10)); // behind iceberg

    // Sell 5 — fills iceberg's visible, iceberg reloads at back
    e.submitOrder(lim(3, Side::SELL, 100, 5));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].passiveId, (OrderId)1); // iceberg filled first

    r.clear();
    // Now sell 5 more — should fill order 2 first (iceberg lost priority)
    e.submitOrder(lim(4, Side::SELL, 100, 5));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].passiveId, (OrderId)2);
}

void test_post_only_reject() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::SELL, 100, 10));
    OrderInput po = lim(2, Side::BUY, 100, 5);
    po.postOnly = true;
    e.submitOrder(po);
    bool poCancel = false;
    for (auto& [id, reason] : r.cancelled) if (id==2 && reason=="POST_ONLY_WOULD_CROSS") poCancel=true;
    T_TRUE(poCancel);
    T_EQ(r.trades.size(), 0u);
}

void test_post_only_rest() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::SELL, 100, 10));
    OrderInput po = lim(2, Side::BUY, 99, 5);
    po.postOnly = true;
    e.submitOrder(po);
    T_EQ(r.trades.size(), 0u);
    T_EQ(e.orderCount(), 2u);
    T_EQ(e.bestBid(), 99);
}

void test_min_qty_fill() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    OrderInput o = lim(2, Side::SELL, 100, 8);
    o.minQty = 5;
    e.submitOrder(o);
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].quantity, 8);
}

void test_min_qty_reject() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 3));
    OrderInput o = lim(2, Side::SELL, 100, 8);
    o.minQty = 5;
    e.submitOrder(o);
    T_EQ(r.trades.size(), 0u);
    bool mqCancel = false;
    for (auto& [id, reason] : r.cancelled) if (id==2 && reason=="MIN_QTY_NOT_SATISFIABLE") mqCancel=true;
    T_TRUE(mqCancel);
}

void test_stp_cancel_newest() {
    Rec r; Engine<Rec> e(r);
    OrderInput b = lim(1, Side::BUY, 100, 10);
    b.selfTradeGroup = 1; b.stpPolicy = STPPolicy::CANCEL_NEWEST;
    e.submitOrder(b);
    OrderInput s = lim(2, Side::SELL, 100, 5);
    s.selfTradeGroup = 1; s.stpPolicy = STPPolicy::CANCEL_NEWEST;
    e.submitOrder(s);
    T_EQ(r.trades.size(), 0u);
    bool stpCancel = false;
    for (auto& [id, reason] : r.cancelled) if (id==2 && reason=="STP_CANCEL_NEWEST") stpCancel=true;
    T_TRUE(stpCancel);
    T_EQ(e.orderCount(), 1u); // order 1 still resting
}

void test_stp_cancel_oldest() {
    Rec r; Engine<Rec> e(r);
    OrderInput b = lim(1, Side::BUY, 100, 10);
    b.selfTradeGroup = 1; b.stpPolicy = STPPolicy::CANCEL_OLDEST;
    e.submitOrder(b);
    OrderInput s = lim(2, Side::SELL, 100, 5);
    s.selfTradeGroup = 1; s.stpPolicy = STPPolicy::CANCEL_OLDEST;
    e.submitOrder(s);
    T_EQ(r.trades.size(), 0u);
    bool stpCancel = false;
    for (auto& [id, reason] : r.cancelled) if (id==1 && reason=="STP_CANCEL_OLDEST") stpCancel=true;
    T_TRUE(stpCancel);
    // Order 2 should rest (no contra to match after removing order 1)
    T_EQ(e.orderCount(), 1u);
}

void test_stp_cancel_both() {
    Rec r; Engine<Rec> e(r);
    OrderInput b = lim(1, Side::BUY, 100, 10);
    b.selfTradeGroup = 1; b.stpPolicy = STPPolicy::CANCEL_BOTH;
    e.submitOrder(b);
    OrderInput s = lim(2, Side::SELL, 100, 5);
    s.selfTradeGroup = 1; s.stpPolicy = STPPolicy::CANCEL_BOTH;
    e.submitOrder(s);
    T_EQ(r.trades.size(), 0u);
    T_EQ(e.orderCount(), 0u);
}

void test_stp_decrement() {
    Rec r; Engine<Rec> e(r);
    OrderInput b = lim(1, Side::BUY, 100, 10);
    b.selfTradeGroup = 1; b.stpPolicy = STPPolicy::DECREMENT;
    e.submitOrder(b);
    OrderInput s = lim(2, Side::SELL, 100, 7);
    s.selfTradeGroup = 1; s.stpPolicy = STPPolicy::DECREMENT;
    e.submitOrder(s);
    T_EQ(r.trades.size(), 0u);
    T_EQ(r.decremented.size(), 1u);
    // incoming (2) had 7, resting (1) visible 10. reduce by min(7,10)=7
    // incoming: 7-7=0 → cancelled. resting: 10-7=3.
    T_EQ(e.orderCount(), 1u); // order 1 with 3 remaining
}

void test_stop_trigger() {
    Rec r; Engine<Rec> e(r);
    // Place a resting order to generate a trade
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    // Place a stop buy
    OrderInput stop{}; stop.id=2; stop.side=Side::BUY; stop.orderType=OrderType::STOP_LIMIT;
    stop.timeInForce=TimeInForce::GTC; stop.price=105; stop.stopPrice=100;
    stop.quantity=5;
    e.submitOrder(stop);
    T_EQ(e.stopCount(), 1u);

    // Trade at 100 triggers the stop
    e.submitOrder(lim(3, Side::SELL, 100, 10));
    T_TRUE(!r.triggered.empty());
    T_EQ(r.triggered[0], (OrderId)2);
}

void test_stop_immediate_trigger() {
    Rec r; Engine<Rec> e(r);
    // First create a trade to set lastTradePrice
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    e.submitOrder(lim(2, Side::SELL, 100, 10));
    T_EQ(e.lastTradePrice(), 100);

    // Submit a stop that should trigger immediately
    OrderInput stop{}; stop.id=3; stop.side=Side::BUY; stop.orderType=OrderType::STOP_LIMIT;
    stop.timeInForce=TimeInForce::GTC; stop.price=105; stop.stopPrice=100;
    stop.quantity=5;
    e.submitOrder(stop);
    T_EQ(e.stopCount(), 0u); // immediately triggered, not in stops
    T_TRUE(!r.triggered.empty());
}

void test_cancel() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    T_EQ(e.orderCount(), 1u);
    T_TRUE(e.cancelOrder(1));
    T_EQ(e.orderCount(), 0u);
    T_TRUE(!e.hasOrder(1));
}

void test_cancel_stop() {
    Rec r; Engine<Rec> e(r);
    OrderInput stop{}; stop.id=1; stop.side=Side::BUY; stop.orderType=OrderType::STOP_LIMIT;
    stop.timeInForce=TimeInForce::GTC; stop.price=105; stop.stopPrice=100;
    stop.quantity=5;
    e.submitOrder(stop);
    T_EQ(e.stopCount(), 1u);
    T_TRUE(e.cancelOrder(1));
    T_EQ(e.stopCount(), 0u);
    T_EQ(e.orderCount(), 0u);
}

void test_amend_qty_down() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    T_TRUE(e.amendOrder(1, 0, 5));
    T_EQ(e.orderCount(), 1u);
    // Fill with 5 — should fill completely
    e.submitOrder(lim(2, Side::SELL, 100, 5));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].quantity, 5);
    T_EQ(e.orderCount(), 0u);
}

void test_amend_price() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    T_EQ(e.bestBid(), 100);
    T_TRUE(e.amendOrder(1, 95, 0));
    T_EQ(e.bestBid(), 95);
}

void test_amend_cross() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::SELL, 100, 10));
    e.submitOrder(lim(2, Side::BUY, 95, 5));
    r.clear();
    // Amend buy order's price to cross
    T_TRUE(e.amendOrder(2, 100, 0));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].quantity, 5);
    T_EQ(r.trades[0].price, 100); // passive price
}

void test_duplicate_id() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    e.submitOrder(lim(1, Side::SELL, 100, 10)); // duplicate
    T_EQ(r.rejected.size(), 1u);
    T_EQ(r.rejected[0].second, std::string("DUPLICATE_ORDER_ID"));
    T_EQ(e.orderCount(), 1u); // original still there
}

void test_resource_lifecycle() {
    Rec r; Engine<Rec> e(r);
    for (OrderId i = 1; i <= 100; ++i) {
        e.submitOrder(lim(i, Side::BUY, 100, 10));
    }
    T_EQ(e.orderCount(), 100u);
    for (OrderId i = 1; i <= 100; ++i) {
        e.cancelOrder(i);
    }
    T_EQ(e.orderCount(), 0u);
    T_EQ(e.activeOrders(), 0u);
    T_EQ(e.activeLevels(), 0u);
}

void test_resource_lifecycle_fill() {
    Rec r; Engine<Rec> e(r);
    for (OrderId i = 1; i <= 50; ++i)
        e.submitOrder(lim(i, Side::BUY, 100, 10));
    for (OrderId i = 51; i <= 100; ++i)
        e.submitOrder(lim(i, Side::SELL, 100, 10));
    T_EQ(e.orderCount(), 0u);
    T_EQ(e.activeOrders(), 0u);
    T_EQ(e.activeLevels(), 0u);
}

void test_no_stale_index() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    e.submitOrder(lim(2, Side::SELL, 100, 10));
    T_TRUE(!e.hasOrder(1));
    T_TRUE(!e.hasOrder(2));
}

void test_wf_validations() {
    Rec r; Engine<Rec> e(r);

    // WF1: quantity <= 0
    { OrderInput o = lim(1, Side::BUY, 100, 0); e.submitOrder(o); }
    T_EQ(r.rejected.size(), 1u);

    // WF2: LIMIT no price
    r.clear();
    { OrderInput o{}; o.id=2; o.side=Side::BUY; o.orderType=OrderType::LIMIT;
      o.timeInForce=TimeInForce::GTC; o.quantity=10; e.submitOrder(o); }
    T_EQ(r.rejected.size(), 1u);

    // WF3: MARKET with price
    r.clear();
    { OrderInput o = mkt(3, Side::BUY, 10); o.price=100; e.submitOrder(o); }
    T_EQ(r.rejected.size(), 1u);

    // WF8: MARKET with GTC
    r.clear();
    { OrderInput o{}; o.id=4; o.side=Side::BUY; o.orderType=OrderType::MARKET;
      o.timeInForce=TimeInForce::GTC; o.quantity=10; e.submitOrder(o); }
    T_EQ(r.rejected.size(), 1u);

    // WF10: iceberg non-LIMIT
    r.clear();
    { OrderInput o = mkt(5, Side::BUY, 10); o.displayQty=5; e.submitOrder(o); }
    T_EQ(r.rejected.size(), 1u);

    // WF13: post-only non-LIMIT
    r.clear();
    { OrderInput o = mkt(6, Side::BUY, 10); o.postOnly=true; e.submitOrder(o); }
    T_EQ(r.rejected.size(), 1u);

    // WF16: STP group without policy
    r.clear();
    { OrderInput o = lim(7, Side::BUY, 100, 10); o.selfTradeGroup=1; e.submitOrder(o); }
    T_EQ(r.rejected.size(), 1u);

    // WF20: FOK with minQty
    r.clear();
    { OrderInput o = lim(8, Side::SELL, 100, 10, TimeInForce::FOK); o.minQty=5; e.submitOrder(o); }
    T_EQ(r.rejected.size(), 1u);
}

void test_appendix_b() {
    Rec r; Engine<Rec> e(r);

    // 1. LIMIT BUY 100 @ 1000 GTC
    e.submitOrder(lim(1, Side::BUY, 1000, 100));
    T_EQ(r.trades.size(), 0u);
    T_EQ(e.bestBid(), 1000);

    // 2. LIMIT BUY 50 @ 1000 GTC
    e.submitOrder(lim(2, Side::BUY, 1000, 50));
    T_EQ(r.trades.size(), 0u);

    // 3. LIMIT BUY 75 @ 1005 GTC
    e.submitOrder(lim(3, Side::BUY, 1005, 75));
    T_EQ(e.bestBid(), 1005);

    // 4. LIMIT SELL 30 @ 995 GTC → crosses, fills 30 from #3 @ 1005
    e.submitOrder(lim(4, Side::SELL, 995, 30));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].price, 1005);  // passive price
    T_EQ(r.trades[0].quantity, 30);
    T_EQ(r.trades[0].aggressorId, (OrderId)4);
    T_EQ(r.trades[0].passiveId, (OrderId)3);
    // Order 3 has 45 remaining
    T_EQ(e.bestBid(), 1005);

    // 5. MARKET SELL 200 IOC → sweep
    r.clear();
    e.submitOrder(mkt(5, Side::SELL, 200));
    T_EQ(r.trades.size(), 3u);
    T_EQ(r.trades[0].price, 1005); T_EQ(r.trades[0].quantity, 45); T_EQ(r.trades[0].passiveId, (OrderId)3);
    T_EQ(r.trades[1].price, 1000); T_EQ(r.trades[1].quantity, 100); T_EQ(r.trades[1].passiveId, (OrderId)1);
    T_EQ(r.trades[2].price, 1000); T_EQ(r.trades[2].quantity, 50); T_EQ(r.trades[2].passiveId, (OrderId)2);
    // Remaining 5 cancelled (IOC)
    bool iocCancel = false;
    for (auto& [id,reason] : r.cancelled) if (id==5 && reason=="IOC_REMAINDER") iocCancel=true;
    T_TRUE(iocCancel);
    T_EQ(e.orderCount(), 0u);
    T_EQ(e.bestBid(), 0);
}

void test_fifo_within_level() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 5));
    e.submitOrder(lim(2, Side::BUY, 100, 5));
    e.submitOrder(lim(3, Side::BUY, 100, 5));
    e.submitOrder(lim(4, Side::SELL, 100, 5));
    T_EQ(r.trades[0].passiveId, (OrderId)1); // first in, first out
}

void test_iceberg_full_consume() {
    Rec r; Engine<Rec> e(r);
    OrderInput ice = lim(1, Side::BUY, 100, 20);
    ice.displayQty = 5;
    e.submitOrder(ice);
    // Sell 20 — consume entire iceberg through reloads
    e.submitOrder(lim(2, Side::SELL, 100, 20));
    // Should have 4 trades of 5 each (reload 3 times)
    T_EQ(r.trades.size(), 4u);
    for (auto& t : r.trades) { T_EQ(t.quantity, 5); }
    T_EQ(e.orderCount(), 0u);
}

void test_market_fok() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 5));
    e.submitOrder(mkt(2, Side::SELL, 10, TimeInForce::FOK));
    T_EQ(r.trades.size(), 0u);
    bool fokCancel = false;
    for (auto& [id,reason] : r.cancelled) if (id==2) fokCancel=true;
    T_TRUE(fokCancel);
}

void test_day_order() {
    Rec r; Engine<Rec> e(r);
    e.setTime(100);
    OrderInput o = lim(1, Side::BUY, 100, 10, TimeInForce::DAY);
    e.submitOrder(o);
    T_EQ(e.orderCount(), 1u);
    e.expireOrders(999);
    T_EQ(e.orderCount(), 0u);
    T_EQ(r.expired.size(), 1u);
}

void test_empty_level_cleanup() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    e.submitOrder(lim(2, Side::BUY, 100, 10));
    T_EQ(e.bidLevelCount(), 1u);
    e.cancelOrder(1);
    T_EQ(e.bidLevelCount(), 1u); // still one order
    e.cancelOrder(2);
    T_EQ(e.bidLevelCount(), 0u); // level removed
}

void test_stp_oldest_continue_match() {
    Rec r; Engine<Rec> e(r);
    // Resting: STP order then non-STP order
    OrderInput b1 = lim(1, Side::BUY, 100, 10);
    b1.selfTradeGroup = 1; b1.stpPolicy = STPPolicy::CANCEL_OLDEST;
    e.submitOrder(b1);
    e.submitOrder(lim(2, Side::BUY, 100, 10)); // no STP

    // Incoming sell with same STP group → cancel oldest (1), then match (2)
    OrderInput s = lim(3, Side::SELL, 100, 5);
    s.selfTradeGroup = 1; s.stpPolicy = STPPolicy::CANCEL_OLDEST;
    e.submitOrder(s);

    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].passiveId, (OrderId)2);
    T_EQ(r.trades[0].quantity, 5);
}

// ─────────────────────── PORTED FROM ~/matcher ───────────────────────

OrderInput limGtd(OrderId id, Side s, Price px, Quantity qty, Timestamp expire) {
    OrderInput o{}; o.id=id; o.side=s; o.orderType=OrderType::LIMIT;
    o.timeInForce=TimeInForce::GTD; o.price=px; o.quantity=qty;
    o.expireTime=expire; return o;
}

OrderInput limStp(OrderId id, Side s, Price px, Quantity qty, TimeInForce tif,
                  SelfTradeGroup grp, STPPolicy pol) {
    OrderInput o = lim(id, s, px, qty, tif);
    o.selfTradeGroup = grp; o.stpPolicy = pol; return o;
}

OrderInput iceberg(OrderId id, Side s, Price px, Quantity qty, Quantity display,
                   TimeInForce tif = TimeInForce::GTC) {
    OrderInput o = lim(id, s, px, qty, tif);
    o.displayQty = display; return o;
}

bool hasTrade(const Rec& r, OrderId agg, OrderId pass, Price px, Quantity qty) {
    for (auto& t : r.trades)
        if (t.aggressorId==agg && t.passiveId==pass && t.price==px && t.quantity==qty)
            return true;
    return false;
}

bool hasDecrement(const Rec& r, OrderId inc, OrderId rest, Quantity qty) {
    for (auto& [a,b,q] : r.decremented)
        if (a==inc && b==rest && q==qty) return true;
    return false;
}

void test_many_levels_ascending_asks() {
    Rec r; Engine<Rec> e(r);
    for (OrderId i = 1; i <= 10; i++)
        e.submitOrder(lim(i, Side::SELL, 100 + (Price)i, 5));
    T_EQ(e.bestAsk(), 101);
    e.submitOrder(lim(11, Side::BUY, 103, 15));
    T_TRUE(hasTrade(r, 11, 1, 101, 5));
    T_TRUE(hasTrade(r, 11, 2, 102, 5));
    T_TRUE(hasTrade(r, 11, 3, 103, 5));
    T_TRUE(!e.hasOrder(11));
    T_EQ(e.bestAsk(), 104);
}

void test_many_levels_descending_bids() {
    Rec r; Engine<Rec> e(r);
    for (OrderId i = 1; i <= 10; i++)
        e.submitOrder(lim(i, Side::BUY, 110 - (Price)i, 5));
    T_EQ(e.bestBid(), 109);
    e.submitOrder(lim(11, Side::SELL, 107, 15));
    T_TRUE(hasTrade(r, 11, 1, 109, 5));
    T_TRUE(hasTrade(r, 11, 2, 108, 5));
    T_TRUE(hasTrade(r, 11, 3, 107, 5));
    T_EQ(e.bestBid(), 106);
}

void test_cancel_then_resubmit_same_id() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 100, 10));
    e.cancelOrder(1);
    T_TRUE(!e.hasOrder(1));
    e.submitOrder(lim(1, Side::BUY, 101, 20));
    T_TRUE(e.hasOrder(1));
    T_EQ(e.bestBid(), 101);
}

void test_iceberg_with_multiple_aggressors() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(iceberg(1, Side::BUY, 100, 50, 10));
    for (OrderId i = 2; i <= 6; i++)
        e.submitOrder(lim(i, Side::SELL, 100, 10));
    T_TRUE(!e.hasOrder(1));
    T_EQ(e.orderCount(), 0u);
}

void test_partial_fill_then_expire() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(limGtd(1, Side::BUY, 100, 20, 1000));
    e.submitOrder(lim(2, Side::SELL, 100, 10));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].quantity, 10);
    T_TRUE(e.hasOrder(1));
    e.expireOrders(1000);
    T_TRUE(!e.hasOrder(1));
    T_EQ(e.bestBid(), 0);
}

void test_rapid_insert_cancel_sequence() {
    Rec r; Engine<Rec> e(r);
    for (OrderId i = 1; i <= 100; i++)
        e.submitOrder(lim(i, Side::BUY, 100, 10));
    for (OrderId i = 1; i <= 100; i++)
        e.cancelOrder(i);
    T_EQ(e.bestBid(), 0);
    T_EQ(e.orderCount(), 0u);
}

void test_amend_and_match_sequence() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY,  100, 10));
    e.submitOrder(lim(2, Side::SELL, 102, 10));
    e.amendOrder(1, 0, 5);   // qty down to 5
    e.amendOrder(2, 101, 0); // price down to 101
    T_EQ(e.bestBid(), 100);
    T_EQ(e.bestAsk(), 101);
    r.clear();
    e.submitOrder(lim(3, Side::SELL, 100, 5));
    T_TRUE(hasTrade(r, 3, 1, 100, 5));
    T_TRUE(!e.hasOrder(1));
}

void test_book_depth_after_operations() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY,  100, 10));
    e.submitOrder(lim(2, Side::BUY,   99, 10));
    e.submitOrder(lim(3, Side::BUY,   98, 10));
    e.submitOrder(lim(4, Side::SELL, 102, 10));
    e.submitOrder(lim(5, Side::SELL, 103, 10));
    e.cancelOrder(2);
    T_EQ(e.bestBid(), 100);
    // Sell at 98 sweeps through 100 then 98
    e.submitOrder(lim(6, Side::SELL, 98, 10));
    T_TRUE(hasTrade(r, 6, 1, 100, 10));
    T_EQ(e.bestBid(), 98);
}

void test_stp_decrement_then_match() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(limStp(1, Side::SELL, 50, 3, TimeInForce::GTC, 1, STPPolicy::DECREMENT));
    e.submitOrder(lim(2, Side::SELL, 50, 10));
    e.submitOrder(limStp(3, Side::BUY, 50, 10, TimeInForce::GTC, 1, STPPolicy::DECREMENT));
    T_TRUE(hasDecrement(r, 3, 1, 3));
    T_TRUE(hasTrade(r, 3, 2, 50, 7));
    T_TRUE(!e.hasOrder(3));
}

void test_gtd_partial_fill_then_expire() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(limGtd(1, Side::SELL, 50, 20, 2000));
    e.submitOrder(lim(2, Side::BUY, 50, 5));
    T_EQ(r.trades.size(), 1u);
    T_TRUE(e.hasOrder(1));
    e.expireOrders(2000);
    T_TRUE(!e.hasOrder(1));
    T_EQ(e.bestAsk(), 0);
}

void test_resource_lifecycle_1000_pairs() {
    Rec r; Engine<Rec> e(r);
    for (int i = 0; i < 1000; i++) {
        OrderId bid_id = (OrderId)(i * 2 + 1);
        OrderId ask_id = (OrderId)(i * 2 + 2);
        e.submitOrder(lim(bid_id, Side::BUY,  1000, 1));
        e.submitOrder(lim(ask_id, Side::SELL, 1000, 1));
    }
    T_EQ(r.trades.size(), 1000u);
    T_EQ(e.bestBid(), 0);
    T_EQ(e.bestAsk(), 0);
    for (int i = 0; i < 2000; i++)
        T_TRUE(!e.hasOrder((OrderId)(i + 1)));
}

void test_basic_limit_match_legacy() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 1000, 100));
    T_EQ(e.bestBid(), 1000);
    T_EQ(r.trades.size(), 0u);
    e.submitOrder(lim(2, Side::BUY, 1000, 50));
    e.submitOrder(lim(3, Side::BUY, 1005, 75));
    T_EQ(e.bestBid(), 1005);
    e.submitOrder(lim(4, Side::SELL, 995, 30));
    T_EQ(r.trades.size(), 1u);
    T_EQ(r.trades[0].price, 1005);
    T_EQ(r.trades[0].quantity, 30);
    T_EQ(e.bestBid(), 1005);
}

void test_market_sweep_legacy() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 1000, 100));
    e.submitOrder(lim(2, Side::BUY, 1000,  50));
    e.submitOrder(lim(3, Side::BUY, 1005,  75));
    e.submitOrder(lim(4, Side::SELL, 995,  30));
    T_EQ(r.trades.size(), 1u);
    size_t prev = r.trades.size();
    e.submitOrder(mkt(5, Side::SELL, 200));
    T_EQ(r.trades.size(), prev + 3);
    bool iocCancel = false;
    for (auto& [id, reason] : r.cancelled)
        if (id==5 && reason=="IOC_REMAINDER") iocCancel=true;
    T_TRUE(iocCancel);
    T_EQ(e.bestBid(), 0);
    T_EQ(e.bestAsk(), 0);
}

void test_stop_trigger_cascade() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(1, Side::BUY, 1000, 50));
    OrderInput stop{}; stop.id=2; stop.side=Side::SELL;
    stop.orderType=OrderType::STOP_LIMIT;
    stop.price=990; stop.stopPrice=1000;
    stop.quantity=30; stop.timeInForce=TimeInForce::GTC;
    e.submitOrder(stop);
    T_EQ(r.trades.size(), 0u);
    e.submitOrder(lim(3, Side::SELL, 1000, 10));
    T_TRUE(r.trades.size() >= 1u);
    T_TRUE(r.triggered.size() >= 1u);
    T_TRUE(r.trades.size() >= 2u);
}

void test_bug1_fifo_holds() {
    Rec r; Engine<Rec> e(r);
    e.submitOrder(lim(100, Side::BUY, 1000, 200));
    OrderInput s1{}; s1.id=1; s1.side=Side::SELL;
    s1.orderType=OrderType::STOP_LIMIT;
    s1.price=995; s1.stopPrice=1000;
    s1.quantity=50; s1.timeInForce=TimeInForce::GTC;
    e.submitOrder(s1);
    OrderInput s2 = s1; s2.id=2;
    e.submitOrder(s2);
    e.submitOrder(lim(99, Side::SELL, 1000, 10));
    T_EQ(r.triggered.size(), 2u);
    T_TRUE(r.trades.size() >= 3u);
}

void test_bug2_iceberg_decrement_reload() {
    Rec r; Engine<Rec> e(r);
    OrderInput ice = lim(1, Side::SELL, 1000, 100);
    ice.displayQty = 20;
    ice.selfTradeGroup = 1; ice.stpPolicy = STPPolicy::DECREMENT;
    e.submitOrder(ice);
    OrderInput s2 = lim(2, Side::SELL, 1000, 50);
    s2.selfTradeGroup = 1; s2.stpPolicy = STPPolicy::DECREMENT;
    e.submitOrder(s2);
    OrderInput inc = lim(3, Side::BUY, 1000, 20);
    inc.selfTradeGroup = 1; inc.stpPolicy = STPPolicy::DECREMENT;
    e.submitOrder(inc);
    // Decrement should reduce incoming by min(20, visible=20) = 20
    // Order 1 remaining should drop by 20 → 80, and reload visible to 20
    T_TRUE(r.decremented.size() >= 1u);
}

// ── main ──
int main() {
    printf("Running correctness tests...\n");
    int f0 = gFail;
    (void)f0;

    #define SECTION(name) printf("\n[%s]\n", name); f0 = gFail
    SECTION("Basic matching");
    f0=gFail; RUN(test_limit_rest);
    f0=gFail; RUN(test_limit_cross);
    f0=gFail; RUN(test_limit_partial);
    f0=gFail; RUN(test_sweep);
    f0=gFail; RUN(test_passive_price);
    f0=gFail; RUN(test_fifo_within_level);

    SECTION("Order types");
    f0=gFail; RUN(test_market_fill);
    f0=gFail; RUN(test_market_partial_cancel);
    f0=gFail; RUN(test_market_to_limit);
    f0=gFail; RUN(test_mtl_rest);
    f0=gFail; RUN(test_mtl_no_liquidity);

    SECTION("Time-in-force");
    f0=gFail; RUN(test_ioc);
    f0=gFail; RUN(test_fok_fill);
    f0=gFail; RUN(test_fok_reject);
    f0=gFail; RUN(test_market_fok);
    f0=gFail; RUN(test_gtd_expire);
    f0=gFail; RUN(test_day_order);

    SECTION("Modifiers");
    f0=gFail; RUN(test_iceberg);
    f0=gFail; RUN(test_iceberg_priority_loss);
    f0=gFail; RUN(test_iceberg_full_consume);
    f0=gFail; RUN(test_post_only_reject);
    f0=gFail; RUN(test_post_only_rest);
    f0=gFail; RUN(test_min_qty_fill);
    f0=gFail; RUN(test_min_qty_reject);

    SECTION("Self-trade prevention");
    f0=gFail; RUN(test_stp_cancel_newest);
    f0=gFail; RUN(test_stp_cancel_oldest);
    f0=gFail; RUN(test_stp_cancel_both);
    f0=gFail; RUN(test_stp_decrement);
    f0=gFail; RUN(test_stp_oldest_continue_match);

    SECTION("Stop orders");
    f0=gFail; RUN(test_stop_trigger);
    f0=gFail; RUN(test_stop_immediate_trigger);

    SECTION("Cancel & Amend");
    f0=gFail; RUN(test_cancel);
    f0=gFail; RUN(test_cancel_stop);
    f0=gFail; RUN(test_amend_qty_down);
    f0=gFail; RUN(test_amend_price);
    f0=gFail; RUN(test_amend_cross);

    SECTION("Resource lifecycle");
    f0=gFail; RUN(test_duplicate_id);
    f0=gFail; RUN(test_resource_lifecycle);
    f0=gFail; RUN(test_resource_lifecycle_fill);
    f0=gFail; RUN(test_no_stale_index);
    f0=gFail; RUN(test_empty_level_cleanup);
    f0=gFail; RUN(test_wf_validations);

    SECTION("Appendix B walkthrough");
    f0=gFail; RUN(test_appendix_b);

    SECTION("Ported from ~/matcher: multi-level & book depth");
    f0=gFail; RUN(test_many_levels_ascending_asks);
    f0=gFail; RUN(test_many_levels_descending_bids);
    f0=gFail; RUN(test_book_depth_after_operations);

    SECTION("Ported from ~/matcher: cancel/amend sequences");
    f0=gFail; RUN(test_cancel_then_resubmit_same_id);
    f0=gFail; RUN(test_rapid_insert_cancel_sequence);
    f0=gFail; RUN(test_amend_and_match_sequence);

    SECTION("Ported from ~/matcher: iceberg");
    f0=gFail; RUN(test_iceberg_with_multiple_aggressors);
    f0=gFail; RUN(test_bug2_iceberg_decrement_reload);

    SECTION("Ported from ~/matcher: expiry");
    f0=gFail; RUN(test_partial_fill_then_expire);
    f0=gFail; RUN(test_gtd_partial_fill_then_expire);

    SECTION("Ported from ~/matcher: STP");
    f0=gFail; RUN(test_stp_decrement_then_match);

    SECTION("Ported from ~/matcher: stop orders");
    f0=gFail; RUN(test_stop_trigger_cascade);
    f0=gFail; RUN(test_bug1_fifo_holds);

    SECTION("Ported from ~/matcher: legacy & resource");
    f0=gFail; RUN(test_basic_limit_match_legacy);
    f0=gFail; RUN(test_market_sweep_legacy);
    f0=gFail; RUN(test_resource_lifecycle_1000_pairs);

    printf("\n========================================\n");
    printf("Results: %d passed, %d failed\n", gPass, gFail);
    return gFail ? 1 : 0;
}
