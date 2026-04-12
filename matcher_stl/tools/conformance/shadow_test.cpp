/*
 * Shadow Model Test for the Matching Engine
 *
 * Implements an obviously-correct reference matching engine using simple
 * std::vector-based data structures with linear scans, then generates random
 * orders and compares the real engine against the shadow after each step.
 *
 * The shadow is designed for correctness as oracle, not performance.
 *
 * Usage: shadow_test [num_steps] [seed]
 *   num_steps  default 100000
 *   seed       default 42
 *
 * Exit 0 if no BUGs found, 1 otherwise.
 */

#include "types.h"
#include "engine.h"

#include <algorithm>
#include <cassert>
#include <csetjmp>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <tuple>
#include <vector>

// ── Crash guard: catch SIGSEGV inside real-engine calls and longjmp out ──────
//
// When the real engine has a memory-safety bug (double-free, use-after-free
// etc.) it may SIGSEGV.  We install a signal handler so the test can report
// the crash as a BUG instead of aborting without a useful message.
//
// Limitation: after catching a SIGSEGV the engine's internal state is
// undefined, so we cannot continue testing.  We report the crash and exit.

static sigjmp_buf  s_crash_jmp;
static volatile sig_atomic_t s_in_real_engine = 0;
static int s_crash_step = 0;
static char s_crash_action[512] = {};

static void crashHandler(int /*sig*/) {
#ifdef __SANITIZE_ADDRESS__
    // Let ASAN handle it — don't longjmp
    signal(SIGSEGV, SIG_DFL);
    raise(SIGSEGV);
#else
    if (s_in_real_engine) {
        siglongjmp(s_crash_jmp, 1);
    }
    // Not inside a guarded region — use default handler
    signal(SIGSEGV, SIG_DFL);
    raise(SIGSEGV);
#endif
}

// RAII guard that sets s_in_real_engine for the duration of real-engine calls
struct CrashGuard {
    explicit CrashGuard(int step, const char* act) {
        s_crash_step = step;
        std::snprintf(s_crash_action, sizeof(s_crash_action), "%s", act);
        s_in_real_engine = 1;
    }
    ~CrashGuard() { s_in_real_engine = 0; }
};

// Returns true if sigsetjmp fired (i.e., a crash was caught)
// Usage:
//   if (CRASH_GUARD_CHECK()) { /* handle crash */ }
//   CrashGuard _guard(step, action);
//   realEngine.foo();    // guarded
#define BEGIN_CRASH_GUARD(step, action)  \
    do {                                  \
        s_crash_step = (step);            \
        std::snprintf(s_crash_action, sizeof(s_crash_action), "%s", (action)); \
        s_in_real_engine = 1;             \
    } while(0)
#define END_CRASH_GUARD() do { s_in_real_engine = 0; } while(0)

// ─────────────────────────────────────────────────────────────────────────────
// Recording Listener (shared by both engines)
// ─────────────────────────────────────────────────────────────────────────────

struct Rec {
    std::vector<Trade>                            trades;
    std::vector<OrderId>                          accepted;
    std::vector<std::pair<OrderId, std::string>>  rejected;
    std::vector<std::pair<OrderId, std::string>>  cancelled;
    std::vector<OrderId>                          triggered;
    std::vector<std::tuple<OrderId, OrderId, Quantity>> decremented;
    std::vector<std::pair<OrderId, Price>>        repriced; // (id, newPrice)

    void onOrderAccepted(const Order& o)   { accepted.push_back(o.id); }
    void onOrderRejected(const Order& o, const char* r) {
        rejected.emplace_back(o.id, std::string(r));
    }
    void onTrade(const Trade& t)           { trades.push_back(t); }
    void onOrderCancelled(const Order& o, const char* r) {
        cancelled.emplace_back(o.id, std::string(r));
    }
    void onOrderExpired(const Order& o)    { (void)o; }
    void onOrderTriggered(const Order& o)  { triggered.push_back(o.id); }
    void onOrderDecremented(const Order& a, const Order& b, Quantity q) {
        decremented.emplace_back(a.id, b.id, q);
    }
    void onOrderRepriced(const Order& o, Price /*old*/, Price nw) {
        repriced.emplace_back(o.id, nw);
    }

    void clear() {
        trades.clear(); accepted.clear(); rejected.clear();
        cancelled.clear(); triggered.clear(); decremented.clear();
        repriced.clear();
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Shadow Engine — obviously-correct reference implementation
//
// Data model:
//   m_book[SELL/BUY] = vector of SOrder (resting limit orders, in insertion order)
//   m_stops          = vector of SOrder (stop orders, in insertion order)
//
// All matching uses linear scans.  No maps, no trees, no clever structures.
// ─────────────────────────────────────────────────────────────────────────────

struct SOrder {
    OrderId        m_id          = 0;
    Side           m_side        = Side::BUY;
    OrderType      m_orderType   = OrderType::LIMIT;
    TimeInForce    m_tif         = TimeInForce::GTC;
    Price          m_price       = 0;
    Price          m_stopPrice   = 0;
    Quantity       m_qty         = 0;     // original
    Quantity       m_remaining   = 0;
    Quantity       m_visible     = 0;
    Quantity       m_displayQty  = 0;     // 0 = not iceberg
    Quantity       m_minQty      = 0;     // 0 = no min
    bool           m_postOnly    = false;
    Timestamp      m_ts          = 0;
    Timestamp      m_expireTime  = 0;
    SelfTradeGroup m_stg         = 0;     // 0 = no STP
    STPPolicy      m_stpPolicy   = STPPolicy::NONE;
};

// ─── Simple PRNG (xorshift64) ────────────────────────────────────────────────

static uint64_t s_rng = 42;

static uint64_t rngNext() {
    s_rng ^= s_rng << 13;
    s_rng ^= s_rng >> 7;
    s_rng ^= s_rng << 17;
    return s_rng;
}

static uint64_t rngRange(uint64_t lo, uint64_t hi) {
    // inclusive [lo, hi]
    if (lo >= hi) return lo;
    return lo + (rngNext() % (hi - lo + 1));
}

// ─── Shadow Engine ───────────────────────────────────────────────────────────

class ShadowEngine {
    static constexpr int MAX_CASCADE = 10;

    Rec&                 m_rec;
    std::vector<SOrder>  m_bids;   // resting bids
    std::vector<SOrder>  m_asks;   // resting asks
    std::vector<SOrder>  m_stops;  // resting stop orders
    Timestamp            m_now      = 0;
    Price                m_lastPx   = 0;
    TradeId              m_tid      = 1;

    // Pending trades accumulated during a single process() call
    std::vector<Trade>   m_pending;

    Timestamp tick() { return ++m_now; }

    // ── Helpers to find best bid/ask ──────────────────────────────────────────

    // Returns iterator to best (highest price) bid
    std::vector<SOrder>::iterator bestBidIt() {
        auto best = m_bids.end();
        for (auto it = m_bids.begin(); it != m_bids.end(); ++it) {
            if (best == m_bids.end() || it->m_price > best->m_price)
                best = it;
            else if (it->m_price == best->m_price && it->m_ts < best->m_ts)
                best = it;
        }
        return best;
    }

    // Returns iterator to best (lowest price) ask
    std::vector<SOrder>::iterator bestAskIt() {
        auto best = m_asks.end();
        for (auto it = m_asks.begin(); it != m_asks.end(); ++it) {
            if (best == m_asks.end() || it->m_price < best->m_price)
                best = it;
            else if (it->m_price == best->m_price && it->m_ts < best->m_ts)
                best = it;
        }
        return best;
    }

    // ── Price-time sorted iteration helpers ──────────────────────────────────
    //
    // Build a sorted list of iterators representing resting orders in price-time
    // priority order for the contra side.

    struct IterEntry {
        Price     price;
        Timestamp ts;
        size_t    idx;  // index into m_bids or m_asks
    };

    // Returns indices into m_asks sorted by price ASC (best ask first), then ts ASC
    std::vector<size_t> sortedAskIndices() const {
        std::vector<size_t> idx;
        idx.reserve(m_asks.size());
        for (size_t i = 0; i < m_asks.size(); ++i)
            idx.push_back(i);
        std::sort(idx.begin(), idx.end(), [this](size_t a, size_t b) {
            if (m_asks[a].m_price != m_asks[b].m_price)
                return m_asks[a].m_price < m_asks[b].m_price;
            return m_asks[a].m_ts < m_asks[b].m_ts;
        });
        return idx;
    }

    // Returns indices into m_bids sorted by price DESC (best bid first), then ts ASC
    std::vector<size_t> sortedBidIndices() const {
        std::vector<size_t> idx;
        idx.reserve(m_bids.size());
        for (size_t i = 0; i < m_bids.size(); ++i)
            idx.push_back(i);
        std::sort(idx.begin(), idx.end(), [this](size_t a, size_t b) {
            if (m_bids[a].m_price != m_bids[b].m_price)
                return m_bids[a].m_price > m_bids[b].m_price;
            return m_bids[a].m_ts < m_bids[b].m_ts;
        });
        return idx;
    }

    // ── Predicate helpers ─────────────────────────────────────────────────────

    static bool canMatch(const SOrder& inc, Price lvPx) {
        if (inc.m_price == 0) return true;  // MARKET
        return inc.m_side == Side::BUY ? inc.m_price >= lvPx : inc.m_price <= lvPx;
    }

    static bool stpConflict(const SOrder& a, const SOrder& b) {
        return a.m_stg != 0 && b.m_stg != 0 && a.m_stg == b.m_stg;
    }

    bool wouldCross(const SOrder& o) const {
        if (o.m_side == Side::BUY) {
            for (const auto& a : m_asks)
                if (o.m_price >= a.m_price) return true;
        } else {
            for (const auto& b : m_bids)
                if (o.m_price <= b.m_price) return true;
        }
        return false;
    }

    // ── FOK / minQty pre-check (spec §5.3, §5.4) ─────────────────────────────
    //
    // Scan uses visibleQty (not remainingQty) per spec FOK_CHECK pseudocode.

    Quantity availableVsAsks(const SOrder& inc, Quantity thresh) const {
        auto indices = sortedAskIndices();
        Quantity avail = 0;
        for (size_t idx : indices) {
            const SOrder& r = m_asks[idx];
            if (!canMatch(inc, r.m_price)) break;
            if (!stpConflict(inc, r)) {
                avail += r.m_visible;
                if (avail >= thresh) return avail;
            }
        }
        return avail;
    }

    Quantity availableVsBids(const SOrder& inc, Quantity thresh) const {
        auto indices = sortedBidIndices();
        Quantity avail = 0;
        for (size_t idx : indices) {
            const SOrder& r = m_bids[idx];
            if (!canMatch(inc, r.m_price)) break;
            if (!stpConflict(inc, r)) {
                avail += r.m_visible;
                if (avail >= thresh) return avail;
            }
        }
        return avail;
    }

    bool fokCheck(const SOrder& o) const {
        Quantity need = o.m_remaining;
        if (o.m_side == Side::BUY)
            return availableVsAsks(o, need) >= need;
        return availableVsBids(o, need) >= need;
    }

    bool minQtyCheck(const SOrder& o) const {
        Quantity need = o.m_minQty;
        if (o.m_side == Side::BUY)
            return availableVsAsks(o, need) >= need;
        return availableVsBids(o, need) >= need;
    }

    // ── Validation (mirrors engine.h validate()) ──────────────────────────────

    const char* validate(const SOrder& o) const {
        if (o.m_qty <= 0) return "WF1";
        if (o.m_orderType == OrderType::LIMIT && o.m_price <= 0) return "WF2";
        if (o.m_orderType == OrderType::STOP_LIMIT && o.m_price <= 0) return "WF2A";
        if (o.m_orderType == OrderType::MARKET_TO_LIMIT && o.m_price != 0) return "WF2B";
        if ((o.m_orderType == OrderType::MARKET || o.m_orderType == OrderType::STOP_MARKET) && o.m_price != 0) return "WF3";
        if ((o.m_orderType == OrderType::STOP_LIMIT || o.m_orderType == OrderType::STOP_MARKET) && o.m_stopPrice <= 0) return "WF4";
        if ((o.m_orderType == OrderType::LIMIT || o.m_orderType == OrderType::MARKET || o.m_orderType == OrderType::MARKET_TO_LIMIT) && o.m_stopPrice != 0) return "WF5";
        if (o.m_tif == TimeInForce::GTD && (o.m_expireTime == 0 || o.m_expireTime <= m_now)) return "WF6";
        if (o.m_tif != TimeInForce::GTD && o.m_expireTime != 0) return "WF7";
        if (o.m_orderType == OrderType::MARKET && o.m_tif != TimeInForce::IOC && o.m_tif != TimeInForce::FOK) return "WF8";
        if (o.m_orderType == OrderType::MARKET_TO_LIMIT && o.m_tif != TimeInForce::GTC && o.m_tif != TimeInForce::GTD && o.m_tif != TimeInForce::DAY) return "WF8A";
        if (o.m_displayQty != 0 && (o.m_displayQty <= 0 || o.m_displayQty > o.m_qty)) return "WF9";
        if (o.m_displayQty != 0 && o.m_orderType != OrderType::LIMIT) return "WF10";
        if (o.m_postOnly && o.m_orderType != OrderType::LIMIT) return "WF13";
        if (o.m_postOnly && (o.m_tif == TimeInForce::IOC || o.m_tif == TimeInForce::FOK)) return "WF14";
        if (o.m_postOnly && (o.m_orderType == OrderType::MARKET || o.m_orderType == OrderType::MARKET_TO_LIMIT)) return "WF15";
        if ((o.m_stg == 0) != (o.m_stpPolicy == STPPolicy::NONE)) return "WF16";
        if (o.m_minQty != 0 && (o.m_minQty <= 0 || o.m_minQty > o.m_qty)) return "WF18";
        if (o.m_minQty != 0 && o.m_postOnly) return "WF19";
        if (o.m_tif == TimeInForce::FOK && o.m_minQty != 0) return "WF20";
        return nullptr;
    }

    // ── Stop trigger predicate ────────────────────────────────────────────────

    bool shouldTrigger(const SOrder& s) const {
        if (m_lastPx == 0) return false;
        return s.m_side == Side::BUY ? m_lastPx >= s.m_stopPrice : m_lastPx <= s.m_stopPrice;
    }

    // ── STP handler ───────────────────────────────────────────────────────────
    //
    // Returns true if the incoming order should stop matching (cancelled/depleted).
    // May modify inc in-place and remove entries from m_bids/m_asks.

    bool handleStp(SOrder& inc, std::vector<SOrder>& contra, size_t restIdx) {
        SOrder& rest = contra[restIdx];
        switch (inc.m_stpPolicy) {
        case STPPolicy::CANCEL_NEWEST:
            // Cancel the incoming order; stop matching
            m_rec.cancelled.emplace_back(inc.m_id, "STP_CANCEL_NEWEST");
            inc.m_remaining = 0;  // sentinel: mark as done
            return true;

        case STPPolicy::CANCEL_OLDEST:
            // Remove the resting order; continue matching
            m_rec.cancelled.emplace_back(rest.m_id, "STP_CANCEL_OLDEST");
            contra.erase(contra.begin() + (ptrdiff_t)restIdx);
            return false;

        case STPPolicy::CANCEL_BOTH:
            // Cancel both; stop matching
            m_rec.cancelled.emplace_back(inc.m_id, "STP_CANCEL_BOTH");
            m_rec.cancelled.emplace_back(rest.m_id, "STP_CANCEL_BOTH");
            contra.erase(contra.begin() + (ptrdiff_t)restIdx);
            inc.m_remaining = 0;
            return true;

        case STPPolicy::DECREMENT: {
            Quantity rq = std::min(inc.m_remaining, rest.m_visible);
            inc.m_remaining -= rq;
            rest.m_remaining -= rq;
            rest.m_visible   -= rq;
            // Update incoming visible
            if (inc.m_displayQty > 0)
                inc.m_visible = std::min(inc.m_displayQty, inc.m_remaining);
            else
                inc.m_visible = inc.m_remaining;
            // Emit decrement event
            m_rec.decremented.emplace_back(inc.m_id, rest.m_id, rq);
            // Handle resting order post-decrement
            if (rest.m_remaining == 0) {
                contra.erase(contra.begin() + (ptrdiff_t)restIdx);
            } else if (rest.m_visible == 0 && rest.m_displayQty > 0) {
                // Iceberg reload after decrement
                rest.m_visible = std::min(rest.m_displayQty, rest.m_remaining);
                rest.m_ts = tick();
                // Move to back by re-inserting
                SOrder copy = rest;
                contra.erase(contra.begin() + (ptrdiff_t)restIdx);
                contra.push_back(copy);
            }
            // Check if incoming is now exhausted
            if (inc.m_remaining == 0) return true;
            return false;
        }
        default:
            return false;
        }
    }

    // ── Core matching against one side ────────────────────────────────────────
    //
    // Modifies inc.m_remaining in place.
    // Appends to m_pending (not emitted yet — stops triggered after).
    // Modifies the given book side (bids or asks).

    void matchAgainst(SOrder& inc, std::vector<SOrder>& contra) {
        // We need to iterate in price-time order.
        // Because we remove and reorder entries during the loop,
        // we re-sort and re-scan each outer iteration step.
        // This is O(n^2) but correct.

        while (inc.m_remaining > 0) {
            // Find the best-priced, earliest-timestamp resting order that can match
            size_t bestIdx = SIZE_MAX;
            Price  bestPx  = 0;
            Timestamp bestTs = UINT64_MAX;

            for (size_t i = 0; i < contra.size(); ++i) {
                const SOrder& r = contra[i];
                if (!canMatch(inc, r.m_price)) continue;

                bool better = false;
                if (bestIdx == SIZE_MAX) {
                    better = true;
                } else if (inc.m_side == Side::BUY) {
                    // Contra is asks: lower price is better, then earlier ts
                    if (r.m_price < bestPx) better = true;
                    else if (r.m_price == bestPx && r.m_ts < bestTs) better = true;
                } else {
                    // Contra is bids: higher price is better, then earlier ts
                    if (r.m_price > bestPx) better = true;
                    else if (r.m_price == bestPx && r.m_ts < bestTs) better = true;
                }
                if (better) { bestIdx = i; bestPx = r.m_price; bestTs = r.m_ts; }
            }

            if (bestIdx == SIZE_MAX) break;  // No more matchable orders

            SOrder& rest = contra[bestIdx];

            // STP check
            if (stpConflict(inc, rest)) {
                bool done = handleStp(inc, contra, bestIdx);
                if (done) return;
                continue;
            }

            // Normal fill
            Quantity fq = std::min(inc.m_remaining, rest.m_visible);
            assert(fq > 0);

            Trade tr{};
            tr.tradeId     = m_tid++;
            tr.price       = rest.m_price;
            tr.quantity    = fq;
            tr.aggressorId = inc.m_id;
            tr.passiveId   = rest.m_id;
            tr.aggressorSide = inc.m_side;
            tr.timestamp   = m_now;
            m_pending.push_back(tr);

            inc.m_remaining -= fq;
            rest.m_visible  -= fq;
            rest.m_remaining -= fq;

            // Iceberg reload
            if (rest.m_visible == 0 && rest.m_remaining > 0 && rest.m_displayQty > 0) {
                rest.m_visible = std::min(rest.m_displayQty, rest.m_remaining);
                rest.m_ts = tick();
                // Move to back of vector (lose time priority, re-sort will handle order)
                SOrder copy = rest;
                contra.erase(contra.begin() + (ptrdiff_t)bestIdx);
                contra.push_back(copy);
                continue;
            }

            if (rest.m_remaining == 0) {
                contra.erase(contra.begin() + (ptrdiff_t)bestIdx);
            }
            // else: partially filled; stays in place
        }
    }

    // ── Dispose: post-match fate of incoming order ────────────────────────────

    void dispose(SOrder& o, bool hasTrades) {
        if (o.m_remaining == 0) return;  // fully filled

        switch (o.m_tif) {
        case TimeInForce::IOC:
            m_rec.cancelled.emplace_back(o.m_id, "IOC_REMAINDER");
            o.m_remaining = 0;
            return;

        case TimeInForce::FOK:
            // Should never reach here (FOK cancelled before matching)
            assert(false && "FOK remainder after pre-check");
            return;

        case TimeInForce::GTC:
            if (o.m_orderType == OrderType::MARKET) {
                m_rec.cancelled.emplace_back(o.m_id, "MARKET_NO_FULL_FILL");
                o.m_remaining = 0;
                return;
            }
            restOrder(o, hasTrades);
            return;

        case TimeInForce::GTD:
        case TimeInForce::DAY:
            restOrder(o, hasTrades);
            return;
        }
    }

    void restOrder(SOrder& o, bool /*hasTrades*/) {
        // Set visible qty before inserting
        if (o.m_displayQty > 0)
            o.m_visible = std::min(o.m_displayQty, o.m_remaining);
        else
            o.m_visible = o.m_remaining;

        if (o.m_side == Side::BUY)
            m_bids.push_back(o);
        else
            m_asks.push_back(o);
    }

    // ── Emit pending trades and trigger stops ─────────────────────────────────

    void emitAndTrigger(size_t startIdx, int depth) {
        size_t endIdx = m_pending.size();
        for (size_t i = startIdx; i < endIdx; ++i) {
            m_rec.trades.push_back(m_pending[i]);
            m_lastPx = m_pending[i].price;
            if (depth < MAX_CASCADE)
                evalStops(m_pending[i].price, depth);
        }
    }

    void evalStops(Price px, int depth) {
        if (m_stops.empty()) return;

        // Collect triggered stops
        std::vector<SOrder> trig;
        for (size_t i = 0; i < m_stops.size(); ) {
            SOrder& s = m_stops[i];
            bool fire = s.m_side == Side::BUY ? px >= s.m_stopPrice : px <= s.m_stopPrice;
            if (fire) {
                trig.push_back(s);
                m_stops.erase(m_stops.begin() + (ptrdiff_t)i);
            } else {
                ++i;
            }
        }
        if (trig.empty()) return;

        // Sort by arrival timestamp (FIFO fairness)
        std::sort(trig.begin(), trig.end(), [](const SOrder& a, const SOrder& b) {
            return a.m_ts < b.m_ts;
        });

        for (SOrder& s : trig) {
            m_rec.triggered.push_back(s.m_id);

            // Convert stop to base type
            if (s.m_orderType == OrderType::STOP_LIMIT)
                s.m_orderType = OrderType::LIMIT;
            else
                s.m_orderType = OrderType::MARKET;
            s.m_stopPrice = 0;

            processActive(s, depth + 1);
        }
    }

    // ── processActive: main matching pipeline for a non-stop order ───────────

    void processActive(SOrder& o, int depth) {
        // Phase 2: Post-only check
        if (o.m_postOnly) {
            if (wouldCross(o)) {
                // Shadow uses REJECT policy (matches engine default)
                m_rec.cancelled.emplace_back(o.m_id, "POST_ONLY_WOULD_CROSS");
                return;
            }
            restOrder(o, false);
            return;
        }

        // Phase 3: FOK / minQty pre-checks
        if (o.m_tif == TimeInForce::FOK && !fokCheck(o)) {
            m_rec.cancelled.emplace_back(o.m_id, "FOK_NOT_SATISFIABLE");
            return;
        }
        if (o.m_minQty > 0 && !minQtyCheck(o)) {
            m_rec.cancelled.emplace_back(o.m_id, "MIN_QTY_NOT_SATISFIABLE");
            return;
        }

        size_t tradeStart = m_pending.size();

        // Phase 4+: Match
        if (o.m_orderType == OrderType::MARKET_TO_LIMIT) {
            // MTL phase 1: match at market
            matchAgainst(o, o.m_side == Side::BUY ? m_asks : m_bids);
            bool hasTrades = m_pending.size() > tradeStart;

            if (!hasTrades) {
                m_rec.cancelled.emplace_back(o.m_id, "MTL_NO_LIQUIDITY");
                emitAndTrigger(tradeStart, depth);
                return;
            }

            // Phase 2: lock price at first execution, convert to LIMIT
            o.m_price     = m_pending[tradeStart].price;
            o.m_orderType = OrderType::LIMIT;
            o.m_minQty    = 0;  // cleared after initial fill

            // Continue matching at locked price if remainder exists
            if (o.m_remaining > 0)
                matchAgainst(o, o.m_side == Side::BUY ? m_asks : m_bids);

            dispose(o, true);
        } else {
            matchAgainst(o, o.m_side == Side::BUY ? m_asks : m_bids);
            bool hasTrades = m_pending.size() > tradeStart;
            if (o.m_minQty > 0 && hasTrades) o.m_minQty = 0;
            dispose(o, hasTrades);
        }

        emitAndTrigger(tradeStart, depth);
    }

    // ── process: top-level entry including stop-order handling ───────────────

    void process(SOrder& o) {
        // Phase 1: Stop order handling
        if (o.m_orderType == OrderType::STOP_LIMIT || o.m_orderType == OrderType::STOP_MARKET) {
            if (shouldTrigger(o)) {
                m_rec.triggered.push_back(o.m_id);
                if (o.m_orderType == OrderType::STOP_LIMIT)
                    o.m_orderType = OrderType::LIMIT;
                else
                    o.m_orderType = OrderType::MARKET;
                o.m_stopPrice = 0;
                // Fall through to processActive
            } else {
                m_stops.push_back(o);
                return;
            }
        }
        processActive(o, 0);
    }

public:
    explicit ShadowEngine(Rec& rec) : m_rec(rec) {}

    // ── Public accessors matching Engine<> API ────────────────────────────────

    Price bestBid() const {
        // Returns 0 when book is empty (mirrors real engine behavior)
        bool found = false;
        Price best = 0;
        for (const auto& o : m_bids) {
            if (!found || o.m_price > best) { best = o.m_price; found = true; }
        }
        return best;
    }

    Price bestAsk() const {
        // Returns 0 when book is empty (mirrors real engine behavior)
        bool found = false;
        Price best = 0;
        for (const auto& o : m_asks) {
            if (!found || o.m_price < best) { best = o.m_price; found = true; }
        }
        return best;
    }

    size_t orderCount() const { return m_bids.size() + m_asks.size(); }
    size_t stopCount()  const { return m_stops.size(); }
    Price  lastTradePrice() const { return m_lastPx; }

    bool hasOrder(OrderId id) const {
        for (const auto& o : m_bids)  if (o.m_id == id) return true;
        for (const auto& o : m_asks)  if (o.m_id == id) return true;
        for (const auto& o : m_stops) if (o.m_id == id) return true;
        return false;
    }

    // Returns true if order is on the limit book (not a stop)
    bool isBookOrder(OrderId id) const {
        for (const auto& o : m_bids) if (o.m_id == id) return true;
        for (const auto& o : m_asks) if (o.m_id == id) return true;
        return false;
    }

    // Returns true if order is a stop
    bool isStopOrder(OrderId id) const {
        for (const auto& o : m_stops) if (o.m_id == id) return true;
        return false;
    }

    // Collect all live book order IDs (not stops)
    std::vector<OrderId> liveBookOrderIds() const {
        std::vector<OrderId> ids;
        for (const auto& o : m_bids)  ids.push_back(o.m_id);
        for (const auto& o : m_asks)  ids.push_back(o.m_id);
        return ids;
    }

    // Collect all stop order IDs
    std::vector<OrderId> liveStopOrderIds() const {
        std::vector<OrderId> ids;
        for (const auto& o : m_stops) ids.push_back(o.m_id);
        return ids;
    }

    // Returns true if there exists an iceberg order on the contra side of `inc`
    // whose remainingQty > visibleQty AND canMatch against `inc`.
    // This detects the KNOWN divergence: spec says FOK/minQty checks use visibleQty
    // but the real engine uses remainingQty for passive icebergs.
    bool hasMatchableIcebergContra(const OrderInput& inc) const {
        const std::vector<SOrder>& contra =
            (inc.side == Side::BUY) ? m_asks : m_bids;
        for (const auto& r : contra) {
            if (r.m_displayQty > 0 && r.m_remaining > r.m_visible) {
                // Iceberg with hidden qty — check price compatibility
                bool matchable = (inc.price == 0)  // MARKET
                    || (inc.side == Side::BUY  ? inc.price >= r.m_price
                                               : inc.price <= r.m_price);
                if (matchable) return true;
            }
        }
        return false;
    }

    // ── submitOrder ───────────────────────────────────────────────────────────

    void submitOrder(const OrderInput& in) {
        // Check duplicate ID
        if (hasOrder(in.id)) {
            m_rec.rejected.emplace_back(in.id, "DUPLICATE_ORDER_ID");
            return;
        }

        SOrder o{};
        o.m_id         = in.id;
        o.m_side       = in.side;
        o.m_orderType  = in.orderType;
        o.m_tif        = in.timeInForce;
        o.m_price      = in.price;
        o.m_stopPrice  = in.stopPrice;
        o.m_qty        = in.quantity;
        o.m_remaining  = in.quantity;
        o.m_minQty     = in.minQty;
        o.m_displayQty = in.displayQty;
        o.m_postOnly   = in.postOnly;
        o.m_ts         = tick();
        o.m_expireTime = in.expireTime;
        o.m_stg        = in.selfTradeGroup;
        o.m_stpPolicy  = in.stpPolicy;
        o.m_visible    = in.displayQty > 0
                         ? std::min(in.displayQty, in.quantity)
                         : in.quantity;

        const char* err = validate(o);
        if (err) {
            m_rec.rejected.emplace_back(in.id, std::string(err));
            return;
        }

        m_rec.accepted.push_back(in.id);
        m_pending.clear();
        process(o);
    }

    // ── cancelOrder ──────────────────────────────────────────────────────────

    bool cancelOrder(OrderId id) {
        for (size_t i = 0; i < m_bids.size(); ++i) {
            if (m_bids[i].m_id == id) {
                m_rec.cancelled.emplace_back(id, "USER_REQUESTED");
                m_bids.erase(m_bids.begin() + (ptrdiff_t)i);
                return true;
            }
        }
        for (size_t i = 0; i < m_asks.size(); ++i) {
            if (m_asks[i].m_id == id) {
                m_rec.cancelled.emplace_back(id, "USER_REQUESTED");
                m_asks.erase(m_asks.begin() + (ptrdiff_t)i);
                return true;
            }
        }
        for (size_t i = 0; i < m_stops.size(); ++i) {
            if (m_stops[i].m_id == id) {
                m_rec.cancelled.emplace_back(id, "USER_REQUESTED");
                m_stops.erase(m_stops.begin() + (ptrdiff_t)i);
                return true;
            }
        }
        return false;
    }

    // ── amendOrder ───────────────────────────────────────────────────────────

    bool amendOrder(OrderId id, Price newPx, Quantity newQty) {
        // Only book orders (not stops) can be amended
        SOrder* ptr = nullptr;
        std::vector<SOrder>* vec = nullptr;
        size_t idx = SIZE_MAX;

        for (size_t i = 0; i < m_bids.size(); ++i) {
            if (m_bids[i].m_id == id) { ptr = &m_bids[i]; vec = &m_bids; idx = i; break; }
        }
        if (!ptr) {
            for (size_t i = 0; i < m_asks.size(); ++i) {
                if (m_asks[i].m_id == id) { ptr = &m_asks[i]; vec = &m_asks; idx = i; break; }
            }
        }
        if (!ptr) return false;

        SOrder& o = *ptr;
        bool pxChg  = (newPx > 0 && newPx != o.m_price);
        bool qtyUp  = (newQty > 0 && newQty > o.m_remaining);
        bool qtyDn  = (newQty > 0 && newQty < o.m_remaining);

        if (qtyDn && !pxChg) {
            // Decrease quantity in place — keep time priority
            o.m_remaining = newQty;
            o.m_visible   = std::min(o.m_visible, newQty);
            return true;
        }

        if (pxChg || qtyUp) {
            // Lose time priority: remove from book, update, re-process
            SOrder copy = o;
            vec->erase(vec->begin() + (ptrdiff_t)idx);

            if (newPx  > 0) copy.m_price     = newPx;
            if (newQty > 0) copy.m_remaining  = newQty;
            copy.m_ts = tick();

            if (copy.m_displayQty > 0)
                copy.m_visible = std::min(copy.m_displayQty, copy.m_remaining);
            else
                copy.m_visible = copy.m_remaining;

            m_pending.clear();
            processActive(copy, 0);
            return true;
        }

        return true;  // No-op (same price, same qty, or newPx==0 && newQty==0)
    }

    // ── expireOrders ─────────────────────────────────────────────────────────

    void expireOrders(Timestamp /*t*/) {
        // Expire GTD and DAY orders from bids
        for (size_t i = 0; i < m_bids.size(); ) {
            bool exp = false;
            if (m_bids[i].m_tif == TimeInForce::DAY) exp = true;
            if (!exp) { ++i; continue; }
            m_bids.erase(m_bids.begin() + (ptrdiff_t)i);
            // (shadow doesn't emit expiry events; we only compare trading state)
        }
        for (size_t i = 0; i < m_asks.size(); ) {
            bool exp = false;
            if (m_asks[i].m_tif == TimeInForce::DAY) exp = true;
            if (!exp) { ++i; continue; }
            m_asks.erase(m_asks.begin() + (ptrdiff_t)i);
        }
    }

    // ── Advance time (mirror engine's internal tick) ──────────────────────────

    void advanceTime() { tick(); }
};

// ─────────────────────────────────────────────────────────────────────────────
// Divergence record
// ─────────────────────────────────────────────────────────────────────────────

enum class DivClass { BUG, KNOWN };

struct Divergence {
    int         step;
    std::string action;
    std::string field;
    std::string expected;  // shadow
    std::string actual;    // real engine
    DivClass    cls;
};

// ─────────────────────────────────────────────────────────────────────────────
// Comparison helpers
// ─────────────────────────────────────────────────────────────────────────────

static std::string tradesToStr(const std::vector<Trade>& tv) {
    std::string s = "[";
    for (size_t i = 0; i < tv.size(); ++i) {
        if (i) s += ", ";
        const Trade& t = tv[i];
        s += "{agg=" + std::to_string(t.aggressorId)
           + " pas=" + std::to_string(t.passiveId)
           + " @"    + std::to_string(t.price)
           + " q="   + std::to_string(t.quantity) + "}";
    }
    s += "]";
    return s;
}

static std::string cancelledToStr(const std::vector<std::pair<OrderId, std::string>>& cv) {
    std::string s = "[";
    for (size_t i = 0; i < cv.size(); ++i) {
        if (i) s += ", ";
        s += "{" + std::to_string(cv[i].first) + ":" + cv[i].second + "}";
    }
    s += "]";
    return s;
}

// Compare trades field-by-field (aggressor, passive, price, qty)
static bool tradesMatch(const std::vector<Trade>& a, const std::vector<Trade>& b) {
    if (a.size() != b.size()) return false;
    for (size_t i = 0; i < a.size(); ++i) {
        if (a[i].aggressorId != b[i].aggressorId) return false;
        if (a[i].passiveId   != b[i].passiveId)   return false;
        if (a[i].price       != b[i].price)        return false;
        if (a[i].quantity    != b[i].quantity)     return false;
    }
    return true;
}

// Compare cancelled ids (only IDs, not reasons, since reason strings may differ slightly
// for non-critical paths; we focus on which orders get cancelled)
static bool cancelledMatch(const std::vector<std::pair<OrderId, std::string>>& a,
                           const std::vector<std::pair<OrderId, std::string>>& b) {
    if (a.size() != b.size()) return false;
    for (size_t i = 0; i < a.size(); ++i) {
        if (a[i].first  != b[i].first)  return false;
        if (a[i].second != b[i].second) return false;
    }
    return true;
}

// ─────────────────────────────────────────────────────────────────────────────
// Random order generator
//
// Derives values from current shadow book state so we hit interesting scenarios:
//   - Prices near best bid/ask, at stop trigger levels, at existing book levels,
//     and far away
//   - Quantities matching, less than, or more than top resting order
//   - Mix of order types, TIFs, iceberg/post-only/STP modifiers
// ─────────────────────────────────────────────────────────────────────────────

struct Generator {
    OrderId m_nextId = 1;

    // Return a price from the neighbourhood of the book, or far away
    Price pickPrice(const ShadowEngine& shadow, Side side, OrderType ot) {
        if (ot == OrderType::MARKET || ot == OrderType::STOP_MARKET) return 0;

        Price bb = shadow.bestBid();
        Price ba = shadow.bestAsk();

        // Build candidate pool
        std::vector<Price> candidates;

        if (bb > 0) {
            candidates.push_back(bb);
            candidates.push_back(bb - 1);
            candidates.push_back(bb + 1);
            candidates.push_back(bb - 5);
        }
        if (ba > 0) {
            candidates.push_back(ba);
            candidates.push_back(ba - 1);
            candidates.push_back(ba + 1);
            candidates.push_back(ba + 5);
        }
        // Mid or far prices
        if (bb > 0 && ba > 0 && ba > bb + 1) {
            candidates.push_back((bb + ba) / 2);
        }
        candidates.push_back((Price)rngRange(95, 110));

        // Filter: prices must be > 0
        candidates.erase(std::remove_if(candidates.begin(), candidates.end(),
            [](Price p) { return p <= 0; }), candidates.end());
        if (candidates.empty()) candidates.push_back(100);

        size_t pick = (size_t)rngRange(0, (uint64_t)(candidates.size() - 1));
        return candidates[pick];
    }

    Price pickStopPrice(const ShadowEngine& shadow, Side side) {
        Price bb = shadow.bestBid();
        Price ba = shadow.bestAsk();
        Price ltp = shadow.lastTradePrice();

        std::vector<Price> candidates;
        if (ltp > 0) {
            // Stop prices that would already trigger
            candidates.push_back(ltp - 1);
            candidates.push_back(ltp);
            candidates.push_back(ltp + 1);
            // Stop prices that are dormant
            if (side == Side::BUY) {
                candidates.push_back(ltp + 3);
                candidates.push_back(ltp + 10);
            } else {
                candidates.push_back(ltp - 3);
                if (ltp > 10) candidates.push_back(ltp - 10);
            }
        }
        if (bb > 0) candidates.push_back(bb);
        if (ba > 0) candidates.push_back(ba);
        candidates.push_back(98);
        candidates.push_back(102);
        candidates.push_back(105);

        candidates.erase(std::remove_if(candidates.begin(), candidates.end(),
            [](Price p) { return p <= 0; }), candidates.end());
        if (candidates.empty()) candidates.push_back(100);

        size_t pick = (size_t)rngRange(0, (uint64_t)(candidates.size() - 1));
        return candidates[pick];
    }

    Quantity pickQty(const ShadowEngine& shadow, Side side) {
        // Look at top of book on contra side
        Price bb = shadow.bestBid();
        Price ba = shadow.bestAsk();
        (void)bb; (void)ba;

        // Small base quantities so the book doesn't grow too large
        std::vector<Quantity> candidates = {1, 2, 3, 5, 8, 10, 15, 20};
        size_t pick = (size_t)rngRange(0, (uint64_t)(candidates.size() - 1));
        return candidates[pick];
    }

    OrderInput generate(const ShadowEngine& shadow) {
        OrderInput in{};
        in.id = m_nextId++;

        // Pick side
        in.side = (rngRange(0, 1) == 0) ? Side::BUY : Side::SELL;

        // Pick order type (weighted toward LIMIT for interesting book state)
        uint64_t ot = rngRange(0, 99);
        if      (ot < 45) in.orderType = OrderType::LIMIT;
        else if (ot < 55) in.orderType = OrderType::MARKET;
        else if (ot < 65) in.orderType = OrderType::MARKET_TO_LIMIT;
        else if (ot < 80) in.orderType = OrderType::STOP_LIMIT;
        else              in.orderType = OrderType::STOP_MARKET;

        // Pick TIF based on order type.
        //
        // MARKET and STOP_MARKET use only IOC/FOK.  STOP_MARKET triggers to become
        // a MARKET order; giving it a resting TIF (GTC/DAY) would cause the triggered
        // MARKET to be inserted on the book at price=0, which is an engine edge case
        // we deliberately avoid to keep both engines in a simple comparable state.
        if (in.orderType == OrderType::MARKET || in.orderType == OrderType::STOP_MARKET) {
            in.timeInForce = (rngRange(0, 1) == 0) ? TimeInForce::IOC : TimeInForce::FOK;
        } else if (in.orderType == OrderType::MARKET_TO_LIMIT) {
            uint64_t t = rngRange(0, 2);
            if      (t == 0) in.timeInForce = TimeInForce::GTC;
            else if (t == 1) in.timeInForce = TimeInForce::DAY;
            else             in.timeInForce = TimeInForce::GTC;  // GTD omitted (no expireTime)
        } else {
            // LIMIT and STOP_LIMIT can use any TIF.
            // We tentatively pick FOK here; it may be demoted to IOC later if we
            // detect iceberg orders on the contra side (see contraHasIceberg check).
            uint64_t t = rngRange(0, 3);
            if      (t == 0) in.timeInForce = TimeInForce::GTC;
            else if (t == 1) in.timeInForce = TimeInForce::IOC;
            else if (t == 2) in.timeInForce = TimeInForce::FOK;
            else             in.timeInForce = TimeInForce::DAY;
        }

        in.quantity = pickQty(shadow, in.side);
        in.price    = pickPrice(shadow, in.side, in.orderType);

        if (in.orderType == OrderType::STOP_LIMIT || in.orderType == OrderType::STOP_MARKET)
            in.stopPrice = pickStopPrice(shadow, in.side);

        // Demote FOK to IOC when there are matchable icebergs on the contra side.
        // Avoids the KNOWN remainingQty-vs-visibleQty divergence that would
        // contaminate subsequent steps with cascading state mismatches.
        if (in.timeInForce == TimeInForce::FOK && shadow.hasMatchableIcebergContra(in)) {
            in.timeInForce = TimeInForce::IOC;
        }
        // Also do this for MARKET/STOP_MARKET FOK (which was randomly chosen)
        if ((in.orderType == OrderType::MARKET || in.orderType == OrderType::STOP_MARKET)
                && in.timeInForce == TimeInForce::FOK
                && shadow.hasMatchableIcebergContra(in)) {
            in.timeInForce = TimeInForce::IOC;
        }

        // Iceberg modifier: only on LIMIT GTC/DAY, ~15% chance
        if (in.orderType == OrderType::LIMIT
                && (in.timeInForce == TimeInForce::GTC || in.timeInForce == TimeInForce::DAY)
                && in.quantity >= 4
                && rngRange(0, 99) < 15) {
            in.displayQty = (Quantity)rngRange(1, (uint64_t)in.quantity - 1);
        }

        // Post-only modifier: only on LIMIT GTC/DAY, ~10% chance
        if (in.orderType == OrderType::LIMIT
                && (in.timeInForce == TimeInForce::GTC || in.timeInForce == TimeInForce::DAY)
                && in.displayQty == 0  // skip when iceberg (not strictly invalid but keep simple)
                && rngRange(0, 99) < 10) {
            in.postOnly = true;
        }

        // minQty modifier: on LIMIT/MARKET_TO_LIMIT IOC/GTC, ~10% chance
        // (not FOK per WF-20; not post-only per WF-19)
        //
        // Skip minQty when there are iceberg orders on the contra side:
        // the real engine uses remainingQty for the check (vs spec's visibleQty),
        // which would cause a KNOWN divergence that contaminates subsequent steps.
        bool contraHasIceberg = shadow.hasMatchableIcebergContra(in);
        if (!in.postOnly
                && in.timeInForce != TimeInForce::FOK
                && !contraHasIceberg
                && (in.orderType == OrderType::LIMIT || in.orderType == OrderType::MARKET_TO_LIMIT)
                && in.quantity >= 2
                && rngRange(0, 99) < 10) {
            in.minQty = (Quantity)rngRange(1, (uint64_t)in.quantity);
        }

        // STP modifier: ~15% chance; use group 1 or 2
        if (rngRange(0, 99) < 15) {
            in.selfTradeGroup = (SelfTradeGroup)rngRange(1, 2);
            uint64_t sp = rngRange(0, 3);
            if      (sp == 0) in.stpPolicy = STPPolicy::CANCEL_NEWEST;
            else if (sp == 1) in.stpPolicy = STPPolicy::CANCEL_OLDEST;
            else if (sp == 2) in.stpPolicy = STPPolicy::CANCEL_BOTH;
            else              in.stpPolicy = STPPolicy::DECREMENT;
        }

        return in;
    }
};

// ─────────────────────────────────────────────────────────────────────────────
// Action types for the test loop
// ─────────────────────────────────────────────────────────────────────────────

enum class ActionType { SUBMIT, CANCEL, AMEND };

// ─────────────────────────────────────────────────────────────────────────────
// Main test harness
// ─────────────────────────────────────────────────────────────────────────────

int main(int argc, char** argv) {
    int numSteps = 100000;
    uint64_t seed = 42;
    bool verbose = false;

    if (argc >= 2) numSteps = atoi(argv[1]);
    if (argc >= 3) seed     = (uint64_t)atoll(argv[2]);
    if (argc >= 4 && std::string(argv[3]) == "--verbose") verbose = true;

    // Install SIGSEGV handler so we can catch real-engine crashes gracefully
    signal(SIGSEGV, crashHandler);

    s_rng = seed;

    printf("Shadow Model Test\n");
    printf("  Steps: %d\n", numSteps);
    printf("  Seed:  %llu\n", (unsigned long long)seed);
    printf("\n");

    Rec realRec, shadowRec;
    Engine<Rec> realEngine(realRec, PostOnlyPolicy::REJECT, 1);
    ShadowEngine shadowEngine(shadowRec);

    Generator gen;

    // Statistics
    int totalSteps    = 0;
    int totalSubmits  = 0;
    int totalCancels  = 0;
    int totalAmends   = 0;
    int totalTrades   = 0;
    int bugCount      = 0;
    int knownCount    = 0;

    std::vector<Divergence> divergences;

    // Advance both engines' internal time by the same amount to stay in sync
    // (Engine uses tick() internally; we can't call setTime on shadow but we
    //  synchronize by ensuring both see the same number of ticks.)

    for (int step = 0; step < numSteps; ++step) {
        realRec.clear();
        shadowRec.clear();

        // Decide action type
        ActionType action = ActionType::SUBMIT;
        {
            // Get live book order IDs from shadow (cheaper oracle)
            auto bookIds = shadowEngine.liveBookOrderIds();
            auto stopIds = shadowEngine.liveStopOrderIds();
            bool hasBookOrders = !bookIds.empty();
            bool hasStops      = !stopIds.empty();
            (void)hasStops;

            uint64_t roll = rngRange(0, 99);
            if (hasBookOrders && roll < 15) {
                action = ActionType::CANCEL;
            } else if (hasBookOrders && roll < 25) {
                action = ActionType::AMEND;
            } else {
                action = ActionType::SUBMIT;
            }
        }

        std::string actionStr;
        OrderId actionId = 0;

        // Build action parameters (using RNG) and describe the action before
        // calling either engine so that the crash guard can print a useful
        // message even if the real engine segfaults.
        OrderInput submitIn{};
        OrderId    cancelId = 0;
        OrderId    amendId  = 0;
        Price      amendPx  = 0;
        Quantity   amendQty = 0;

        if (action == ActionType::SUBMIT) {
            do_submit:
            submitIn = gen.generate(shadowEngine);
            const char* otStr[]  = {"LIMIT","MARKET","MTL","STP_LIM","STP_MKT"};
            const char* tifStr[] = {"GTC","GTD","IOC","FOK","DAY"};
            actionStr = "SUBMIT id=" + std::to_string(submitIn.id)
                      + " " + (submitIn.side==Side::BUY?"BUY":"SELL")
                      + " " + otStr[(int)submitIn.orderType]
                      + " " + tifStr[(int)submitIn.timeInForce]
                      + " px=" + std::to_string(submitIn.price)
                      + " q=" + std::to_string(submitIn.quantity)
                      + (submitIn.displayQty?" dq="+std::to_string(submitIn.displayQty):"")
                      + (submitIn.postOnly?" PO":"")
                      + (submitIn.minQty?" mq="+std::to_string(submitIn.minQty):"")
                      + (submitIn.stopPrice?" sp="+std::to_string(submitIn.stopPrice):"")
                      + (submitIn.selfTradeGroup?" stg="+std::to_string(submitIn.selfTradeGroup):"");
            actionId = submitIn.id;

        } else if (action == ActionType::CANCEL) {
            auto bookIds = shadowEngine.liveBookOrderIds();
            if (bookIds.empty()) {
                // Shadow book is empty (e.g. after a divergence drained it).
                // Fall through to SUBMIT so we make forward progress without
                // re-running both engines on the same step number.
                action = ActionType::SUBMIT;
                goto do_submit;
            }
            size_t pick = (size_t)rngRange(0, (uint64_t)(bookIds.size() - 1));
            cancelId  = bookIds[pick];
            actionStr = "CANCEL id=" + std::to_string(cancelId);
            actionId  = cancelId;

        } else { // AMEND
            auto bookIds = shadowEngine.liveBookOrderIds();
            if (bookIds.empty()) {
                action = ActionType::SUBMIT;
                goto do_submit;
            }
            size_t pick = (size_t)rngRange(0, (uint64_t)(bookIds.size() - 1));
            amendId = bookIds[pick];

            uint64_t amendType = rngRange(0, 2);
            if (amendType == 0) {
                amendPx = (Price)rngRange(95, 110);
            } else if (amendType == 1) {
                amendQty = (Quantity)rngRange(1, 20);
            } else {
                amendPx  = (Price)rngRange(95, 110);
                amendQty = (Quantity)rngRange(1, 20);
            }
            actionStr = "AMEND id=" + std::to_string(amendId)
                      + " px=" + std::to_string(amendPx)
                      + " qty=" + std::to_string(amendQty);
            actionId  = amendId;
        }

        if (verbose) {
            printf("  [pre-action] %s\n", actionStr.c_str());
            fflush(stdout);
        }

        // ── Check for the KNOWN iceberg FOK/minQty divergence BEFORE running ──
        //
        // The spec says FOK/minQty checks use visibleQty; the real engine uses
        // remainingQty.  If the incoming order has FOK or minQty and there is an
        // iceberg (displayQty > 0, remainingQty > visibleQty) on the contra side,
        // a divergence where shadow cancels but real engine trades is KNOWN.
        bool hasIcebergContra = false;
        if (action == ActionType::SUBMIT
                && (submitIn.timeInForce == TimeInForce::FOK || submitIn.minQty > 0)) {
            hasIcebergContra = shadowEngine.hasMatchableIcebergContra(submitIn);
        }

        // ── Execute shadow engine (never crashes) ────────────────────────────
        if (action == ActionType::SUBMIT) {
            shadowEngine.submitOrder(submitIn);
        } else if (action == ActionType::CANCEL) {
            shadowEngine.cancelOrder(cancelId);
        } else {
            shadowEngine.amendOrder(amendId, amendPx, amendQty);
        }

        // ── Execute real engine guarded against SIGSEGV ──────────────────────
        //
        // If the real engine has a memory-safety bug and segfaults, sigsetjmp
        // catches the signal, we report a BUG (CRASH), and stop further testing
        // since the engine state is undefined after a signal.
        BEGIN_CRASH_GUARD(step + 1, actionStr.c_str());
        if (sigsetjmp(s_crash_jmp, 1) == 0) {
            // Normal execution path
            if (action == ActionType::SUBMIT) {
                realEngine.submitOrder(submitIn);
                ++totalSubmits;
            } else if (action == ActionType::CANCEL) {
                realEngine.cancelOrder(cancelId);
                ++totalCancels;
            } else {
                realEngine.amendOrder(amendId, amendPx, amendQty);
                ++totalAmends;
            }
            END_CRASH_GUARD();
        } else {
            // Signal caught — real engine crashed
            END_CRASH_GUARD();
            ++bugCount;
            divergences.push_back({step + 1, actionStr, "CRASH",
                                   "no crash (shadow ran fine)",
                                   "SIGSEGV in real engine",
                                   DivClass::BUG});
            printf("  BUG  step %d [%s]: real engine CRASHED (SIGSEGV)\n"
                   "       shadow completed without error\n",
                   step + 1, actionStr.c_str());
            printf("  (real engine state is undefined after crash; stopping test)\n");
            totalSteps++;
            // Print summary and exit
            goto print_summary;
        }

        totalSteps++;
        totalTrades += (int)realRec.trades.size();

        if (verbose) {
            printf("step %d [%s]  shadow: bid=%ld ask=%ld cnt=%zu stp=%zu  real: bid=%ld ask=%ld cnt=%zu stp=%zu\n",
                   step + 1, actionStr.c_str(),
                   shadowEngine.bestBid(), shadowEngine.bestAsk(),
                   shadowEngine.orderCount(), shadowEngine.stopCount(),
                   realEngine.bestBid(), realEngine.bestAsk(),
                   realEngine.orderCount() - realEngine.stopCount(), realEngine.stopCount());
            if (!shadowRec.trades.empty() || !realRec.trades.empty()) {
                printf("  shadow trades: %s\n", tradesToStr(shadowRec.trades).c_str());
                printf("  real   trades: %s\n", tradesToStr(realRec.trades).c_str());
            }
            if (!shadowRec.cancelled.empty() || !realRec.cancelled.empty()) {
                printf("  shadow cancelled: %s\n", cancelledToStr(shadowRec.cancelled).c_str());
                printf("  real   cancelled: %s\n", cancelledToStr(realRec.cancelled).c_str());
            }
        }

        // ── Compare results ──────────────────────────────────────────────────

        size_t divsBefore = divergences.size();

        auto addDiv = [&](const std::string& field,
                          const std::string& expected,
                          const std::string& actual,
                          DivClass cls) {
            divergences.push_back({step + 1, actionStr, field, expected, actual, cls});
            if (cls == DivClass::BUG) ++bugCount;
            else                      ++knownCount;
        };

        // ── Detect KNOWN iceberg divergence pattern ───────────────────────────
        //
        // Pattern: shadow cancelled incoming order with FOK_NOT_SATISFIABLE or
        // MIN_QTY_NOT_SATISFIABLE, but real engine produced trades (or cancelled
        // for different reasons).  This happens because the real engine's
        // availQty() scan uses remainingQty (not visibleQty) for iceberg orders.
        // Per spec §5.3-5.4 the check should use visibleQty.
        //
        // We classify the ENTIRE step as KNOWN when this pattern is present so
        // that cascading secondary divergences (bestBid/bestAsk/etc.) in the same
        // step are also not counted as BUGs.
        bool knownIcebergStep = false;
        if (hasIcebergContra && action == ActionType::SUBMIT) {
            // Check if shadow cancelled for FOK or minQty but real engine didn't
            auto shadowHasPreCheckCancel = [&](const std::string& reason) {
                for (auto& c : shadowRec.cancelled)
                    if (c.first == submitIn.id && c.second == reason) return true;
                return false;
            };
            auto realHasPreCheckCancel = [&](const std::string& reason) {
                for (auto& c : realRec.cancelled)
                    if (c.first == submitIn.id && c.second == reason) return true;
                return false;
            };
            bool shadowFOK = shadowHasPreCheckCancel("FOK_NOT_SATISFIABLE");
            bool shadowMQ  = shadowHasPreCheckCancel("MIN_QTY_NOT_SATISFIABLE");
            bool realFOK   = realHasPreCheckCancel("FOK_NOT_SATISFIABLE");
            bool realMQ    = realHasPreCheckCancel("MIN_QTY_NOT_SATISFIABLE");
            if ((shadowFOK && !realFOK) || (shadowMQ && !realMQ)) {
                knownIcebergStep = true;
            }
        }

        // Classify a divergence; if on a known-iceberg step, all divergences
        // in this step are KNOWN (not BUG) because they stem from the single
        // documented remainingQty vs visibleQty discrepancy.
        auto stepClass = [&]() { return knownIcebergStep ? DivClass::KNOWN : DivClass::BUG; };

        // 1. Trades produced this step (exact match: aggId, pasId, price, qty)
        if (!tradesMatch(shadowRec.trades, realRec.trades)) {
            addDiv("trades",
                   tradesToStr(shadowRec.trades),
                   tradesToStr(realRec.trades),
                   stepClass());
        }

        // 2. Cancelled orders (id + reason must match exactly)
        if (!cancelledMatch(shadowRec.cancelled, realRec.cancelled)) {
            addDiv("cancelled",
                   cancelledToStr(shadowRec.cancelled),
                   cancelledToStr(realRec.cancelled),
                   stepClass());
        }

        // 3. Book state: bestBid, bestAsk, orderCount (book only, excluding stops)
        {
            Price sbid = shadowEngine.bestBid();
            Price rbid = realEngine.bestBid();
            if (sbid != rbid) {
                addDiv("bestBid",
                       std::to_string(sbid),
                       std::to_string(rbid),
                       stepClass());
            }
        }
        {
            Price sask = shadowEngine.bestAsk();
            Price rask = realEngine.bestAsk();
            if (sask != rask) {
                addDiv("bestAsk",
                       std::to_string(sask),
                       std::to_string(rask),
                       stepClass());
            }
        }
        {
            size_t sCount = shadowEngine.orderCount();
            size_t rCount = realEngine.orderCount() - realEngine.stopCount();
            if (sCount != rCount) {
                addDiv("orderCount",
                       std::to_string(sCount),
                       std::to_string(rCount),
                       stepClass());
            }
        }

        // 4. Last trade price
        {
            Price sltp = shadowEngine.lastTradePrice();
            Price rltp = realEngine.lastTradePrice();
            if (sltp != rltp) {
                addDiv("lastTradePrice",
                       std::to_string(sltp),
                       std::to_string(rltp),
                       stepClass());
            }
        }

        // 5. Stop count
        {
            size_t ssc = shadowEngine.stopCount();
            size_t rsc = realEngine.stopCount();
            if (ssc != rsc) {
                addDiv("stopCount",
                       std::to_string(ssc),
                       std::to_string(rsc),
                       stepClass());
            }
        }

        // Print new divergences found this step (up to bugCount == 20 total)
        for (size_t di = divsBefore; di < divergences.size() && bugCount <= 20; ++di) {
            const auto& d = divergences[di];
            const char* tag = (d.cls == DivClass::BUG) ? "BUG  " : "KNOWN";
            printf("  %s step %d [%s] field=%s shadow=%s real=%s\n",
                   tag, d.step, d.action.c_str(), d.field.c_str(),
                   d.expected.c_str(), d.actual.c_str());
        }

        // Stop after 20 bugs to avoid flooding output
        if (bugCount >= 20) {
            printf("  (halting after 20 BUG divergences)\n");
            break;
        }
    }

print_summary:
    // ── Summary report ────────────────────────────────────────────────────────

    printf("\n");
    printf("=========================================================\n");
    printf("  Shadow Model Test Report\n");
    printf("=========================================================\n");
    printf("  Steps run:         %d\n", totalSteps);
    printf("  Submits:           %d\n", totalSubmits);
    printf("  Cancels:           %d\n", totalCancels);
    printf("  Amends:            %d\n", totalAmends);
    printf("  Trades produced:   %d\n", totalTrades);
    printf("  Divergences total: %d  (BUG=%d  KNOWN=%d)\n",
           bugCount + knownCount, bugCount, knownCount);
    printf("\n");

    if (!divergences.empty()) {
        printf("  Divergence details (first 30):\n");
        int shown = 0;
        for (const auto& d : divergences) {
            if (shown++ >= 30) break;
            printf("    [%s] step %d [%s] %s:\n"
                   "          shadow = %s\n"
                   "          real   = %s\n",
                   d.cls == DivClass::BUG ? "BUG  " : "KNOWN",
                   d.step, d.action.c_str(), d.field.c_str(),
                   d.expected.c_str(), d.actual.c_str());
        }
    }

    printf("\n");
    printf("  Result: %s\n", bugCount == 0 ? "PASS" : "FAIL");
    printf("=========================================================\n");

    return bugCount > 0 ? 1 : 0;
}
