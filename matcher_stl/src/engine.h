#pragma once
#include "types.h"
#include <tlsf/pool.hpp>
#include <map>
#include <vector>
#include <algorithm>
#include <cassert>
#include <new>
#include <cstring>

// STL-compatible pool allocator that falls back to ::operator new for n>1
template <typename T, size_t BlockSize = 4096>
class NodePoolAllocator {
public:
    using value_type = T;
    using propagate_on_container_copy_assignment = std::true_type;
    using propagate_on_container_move_assignment = std::true_type;
    using propagate_on_container_swap = std::true_type;

    template <typename U> struct rebind { using other = NodePoolAllocator<U, BlockSize>; };

    NodePoolAllocator() = default;
    template <typename U> NodePoolAllocator(const NodePoolAllocator<U, BlockSize>&) noexcept {}

    T* allocate(size_t n) {
        if (n == 1) return pool_.allocate();
        return static_cast<T*>(::operator new(n * sizeof(T)));
    }
    void deallocate(T* p, size_t n) noexcept {
        if (n == 1) pool_.deallocate(p);
        else ::operator delete(p);
    }
    bool operator==(const NodePoolAllocator&) const noexcept { return true; }
    bool operator!=(const NodePoolAllocator&) const noexcept { return false; }
private:
    tlsf::Pool<T, BlockSize> pool_;
};

// ─────────────────────────────────────────────────────────────
//  Flat order index with ID recycling
// ─────────────────────────────────────────────────────────────
class OrderIndex {
    static constexpr uint32_t INIT_CAP = 1u << 20;       // 1M slots
    static constexpr uint32_t FREE_STACK_CAP = 1u << 20;  // 1M recycled IDs
    Order**   slots_;
    uint32_t  cap_;
    uint32_t  count_ = 0;
    OrderId*  freeStack_;
    uint32_t  freeCount_ = 0;
    OrderId   nextId_ = 1;

    void grow(uint32_t need) {
        uint32_t nc = cap_;
        while (nc <= need) nc *= 2;
        Order** ns = new Order*[nc]();
        std::memcpy(ns, slots_, cap_ * sizeof(Order*));
        delete[] slots_;
        slots_ = ns;
        cap_ = nc;
    }
public:
    OrderIndex() : cap_(INIT_CAP) {
        slots_ = new Order*[cap_]();
        freeStack_ = new OrderId[FREE_STACK_CAP];
    }
    ~OrderIndex() { delete[] slots_; delete[] freeStack_; }
    OrderIndex(const OrderIndex&) = delete;
    OrderIndex& operator=(const OrderIndex&) = delete;

    uint32_t size() const { return count_; }

    Order* get(OrderId id) const {
        if (id >= cap_) return nullptr;
        return slots_[id];
    }
    bool has(OrderId id) const { return get(id) != nullptr; }

    void insert(OrderId id, Order* o) {
        if (id >= cap_) grow((uint32_t)id);
        slots_[id] = o;
        ++count_;
    }
    void erase(OrderId id) {
        slots_[id] = nullptr;
        --count_;
        if (freeCount_ < FREE_STACK_CAP)
            freeStack_[freeCount_++] = id;
    }

    // Auto-assign: pop from free stack, or increment nextId_
    OrderId assignId() {
        if (freeCount_ > 0)
            return freeStack_[--freeCount_];
        OrderId id = nextId_++;
        if (id >= cap_) grow((uint32_t)id);
        return id;
    }

    // Destructor iteration: visit all live entries
    template<typename F>
    void forEachLive(F&& fn) const {
        if (count_ == 0) return;
        uint32_t found = 0;
        for (uint32_t i = 0; i < cap_ && found < count_; ++i)
            if (slots_[i]) { fn(slots_[i]); ++found; }
    }
};

// ─────────────────────────────────────────────────────────────
//  Matching Engine
// ─────────────────────────────────────────────────────────────
template <typename Listener = NullListener>
class Engine {
    static constexpr int MAX_CASCADE = 10;
    static constexpr size_t PB = 4096;

    using BidMap   = std::map<Price, PriceLevel*, std::greater<Price>,
                              NodePoolAllocator<std::pair<const Price, PriceLevel*>, PB>>;
    using AskMap   = std::map<Price, PriceLevel*, std::less<Price>,
                              NodePoolAllocator<std::pair<const Price, PriceLevel*>, PB>>;

    Listener& L;
    BidMap bids_;
    AskMap asks_;
    OrderIndex idx_;
    std::vector<Order*> stops_;
    tlsf::Pool<Order, PB>      opool_;
    tlsf::Pool<PriceLevel, PB> lpool_;
    std::vector<Trade> trades_;
    Timestamp now_ = 0;
    TradeId   tid_ = 1;
    Price     lastPx_ = 0;
    PostOnlyPolicy poPol_;
    Price     tick_;
    size_t oA_=0, oF_=0, oP_=0, lA_=0, lF_=0, lP_=0;

public:
    Engine(Listener& l, PostOnlyPolicy pop = PostOnlyPolicy::REJECT, Price tickSz = 1)
        : L(l), poPol_(pop), tick_(tickSz) {
        trades_.reserve(4096);
        stops_.reserve(256);
    }

    ~Engine() {
        idx_.forEachLive([this](Order* o){ freeOrd(o); });
        for (auto& [p, lv] : bids_) freeLvl(lv);
        for (auto& [p, lv] : asks_) freeLvl(lv);
    }

    // ── Accessors ──
    Timestamp time() const     { return now_; }
    void setTime(Timestamp t)  { now_ = t; }
    Price bestBid() const      { return bids_.empty() ? 0 : bids_.begin()->first; }
    Price bestAsk() const      { return asks_.empty() ? 0 : asks_.begin()->first; }
    size_t orderCount() const  { return idx_.size(); }
    size_t stopCount() const   { return stops_.size(); }
    bool hasOrder(OrderId id) const { return idx_.has(id); }
    Price lastTradePrice() const { return lastPx_; }
    uint64_t tradeCount() const  { return tid_ - 1; }
    size_t ordersAllocated() const { return oA_; }
    size_t ordersFreed() const    { return oF_; }
    size_t peakOrders() const     { return oP_; }
    size_t levelsAllocated() const { return lA_; }
    size_t levelsFreed() const    { return lF_; }
    size_t peakLevels() const     { return lP_; }
    size_t activeOrders() const   { return oA_ - oF_; }
    size_t activeLevels() const   { return lA_ - lF_; }

    size_t bidLevelCount() const { return bids_.size(); }
    size_t askLevelCount() const { return asks_.size(); }

    // Auto-assign an order ID
    OrderId assignId() { return idx_.assignId(); }

    // ── Submit ──
    void submitOrder(const OrderInput& in) {
        if (idx_.has(in.id)) {
            Order tmp{}; tmp.id = in.id; tmp.status = OrderStatus::REJECTED;
            L.onOrderRejected(tmp, "DUPLICATE_ORDER_ID");
            return;
        }
        Order* o = allocOrd();
        o->id = in.id; o->side = in.side; o->orderType = in.orderType;
        o->timeInForce = in.timeInForce; o->price = in.price;
        o->stopPrice = in.stopPrice; o->quantity = in.quantity;
        o->remainingQty = in.quantity; o->minQty = in.minQty;
        o->displayQty = in.displayQty; o->postOnly = in.postOnly;
        o->status = OrderStatus::NEW; o->timestamp = tick();
        o->expireTime = in.expireTime; o->selfTradeGroup = in.selfTradeGroup;
        o->stpPolicy = in.stpPolicy;
        o->visibleQty = in.displayQty > 0
            ? std::min(in.displayQty, in.quantity) : in.quantity;

        const char* err = validate(o);
        if (err) {
            o->status = OrderStatus::REJECTED;
            L.onOrderRejected(*o, err);
            freeOrd(o); return;
        }
        idx_.insert(o->id, o);
        L.onOrderAccepted(*o);
        trades_.clear();
        process(o, 0);
    }

    // ── Cancel ──
    bool cancelOrder(OrderId id) {
        Order* o = idx_.get(id);
        if (!o) return false;
        if (o->status != OrderStatus::NEW && o->status != OrderStatus::PARTIALLY_FILLED)
            return false;
        o->status = OrderStatus::CANCELLED;
        if (o->level) {
            PriceLevel* lv = o->level;
            lv->remove(o);
            if (lv->empty()) rmLevel(lv, o->side);
        } else {
            rmStop(o);
        }
        L.onOrderCancelled(*o, "USER_REQUESTED");
        idx_.erase(o->id);
        freeOrd(o);
        return true;
    }

    // ── Amend ──
    bool amendOrder(OrderId id, Price newPx, Quantity newQty) {
        Order* o = idx_.get(id);
        if (!o) return false;
        if (o->status != OrderStatus::NEW && o->status != OrderStatus::PARTIALLY_FILLED)
            return false;
        if (!o->level) return false;

        bool pxChg  = (newPx > 0 && newPx != o->price);
        bool qtyUp  = (newQty > 0 && newQty > o->remainingQty);
        bool qtyDn  = (newQty > 0 && newQty < o->remainingQty);

        if (qtyDn && !pxChg) {
            o->remainingQty = newQty;
            o->visibleQty = std::min(o->visibleQty, newQty);
            return true;
        }
        if (pxChg || qtyUp) {
            PriceLevel* lv = o->level;
            lv->remove(o);
            if (lv->empty()) rmLevel(lv, o->side);
            if (newPx > 0)  o->price = newPx;
            if (newQty > 0) o->remainingQty = newQty;
            o->timestamp = tick();
            if (o->displayQty > 0)
                o->visibleQty = std::min(o->displayQty, o->remainingQty);
            else
                o->visibleQty = o->remainingQty;
            trades_.clear();
            processActive(o, 0);
            return true;
        }
        return true;
    }

    // ── Expire ──
    void expireOrders(Timestamp t) {
        std::vector<Order*> exp;
        auto scan = [&](auto& m) {
            for (auto& [px, lv] : m) {
                for (Order* o = lv->head; o; o = o->next) {
                    bool e = false;
                    if (o->timeInForce == TimeInForce::GTD && o->expireTime > 0 && t >= o->expireTime) e = true;
                    if (o->timeInForce == TimeInForce::DAY) e = true;
                    if (e) exp.push_back(o);
                }
            }
        };
        scan(bids_); scan(asks_);
        for (Order* o : exp) {
            o->status = OrderStatus::EXPIRED;
            PriceLevel* lv = o->level;
            if (lv) { lv->remove(o); if (lv->empty()) rmLevel(lv, o->side); }
            L.onOrderExpired(*o);
            idx_.erase(o->id);
            freeOrd(o);
        }
    }

private:
    // ── Pool helpers ──
    Order* allocOrd() {
        Order* o = opool_.allocate();
        o->prev = o->next = nullptr;
        o->level = nullptr;
        ++oA_; size_t a = oA_-oF_; if (a>oP_) oP_=a;
        return o;
    }
    void freeOrd(Order* o)      { opool_.deallocate(o); ++oF_; }
    PriceLevel* allocLvl(Price p) {
        PriceLevel* l = lpool_.allocate();
        new (l) PriceLevel{};
        l->price = p;
        ++lA_; size_t a = lA_-lF_; if (a>lP_) lP_=a;
        return l;
    }
    void freeLvl(PriceLevel* l) { lpool_.deallocate(l); ++lF_; }
    Timestamp tick()            { return ++now_; }

    // ── Level management ──
    void rmLevel(PriceLevel* lv, Side s) {
        if (s == Side::BUY) bids_.erase(lv->price); else asks_.erase(lv->price);
        freeLvl(lv);
    }
    template<typename M>
    void insertSide(Order* o, M& m) {
        auto it = m.find(o->price);
        PriceLevel* lv;
        if (it != m.end()) { lv = it->second; }
        else { lv = allocLvl(o->price); m[o->price] = lv; }
        lv->pushBack(o);
    }
    void insertOrder(Order* o) {
        if (o->displayQty > 0)
            o->visibleQty = std::min(o->displayQty, o->remainingQty);
        else
            o->visibleQty = o->remainingQty;
        if (o->side == Side::BUY) insertSide(o, bids_); else insertSide(o, asks_);
    }

    // ── Stop helpers ──
    void rmStop(Order* o) {
        for (size_t i = 0; i < stops_.size(); ++i)
            if (stops_[i] == o) { stops_[i] = stops_.back(); stops_.pop_back(); return; }
    }
    bool shouldTrigger(const Order* o) const {
        if (lastPx_ == 0) return false;
        return o->side == Side::BUY ? lastPx_ >= o->stopPrice : lastPx_ <= o->stopPrice;
    }

    // ── Predicates ──
    static bool canMatch(const Order* inc, Price lvPx) {
        if (inc->price == 0) return true;
        return inc->side == Side::BUY ? inc->price >= lvPx : inc->price <= lvPx;
    }
    bool wouldCross(const Order* o) const {
        if (o->side == Side::BUY)
            return !asks_.empty() && o->price >= asks_.begin()->first;
        return !bids_.empty() && o->price <= bids_.begin()->first;
    }
    static bool stpConflict(const Order* a, const Order* b) {
        return a->selfTradeGroup && b->selfTradeGroup && a->selfTradeGroup == b->selfTradeGroup;
    }

    // ── Validation (WF-1 … WF-20) ──
    const char* validate(const Order* o) const {
        if (o->quantity <= 0) return "WF1";
        if (o->orderType == OrderType::LIMIT && o->price <= 0) return "WF2";
        if (o->orderType == OrderType::STOP_LIMIT && o->price <= 0) return "WF2A";
        if (o->orderType == OrderType::MARKET_TO_LIMIT && o->price != 0) return "WF2B";
        if ((o->orderType == OrderType::MARKET || o->orderType == OrderType::STOP_MARKET) && o->price != 0) return "WF3";
        if ((o->orderType == OrderType::STOP_LIMIT || o->orderType == OrderType::STOP_MARKET) && o->stopPrice <= 0) return "WF4";
        if ((o->orderType == OrderType::LIMIT || o->orderType == OrderType::MARKET || o->orderType == OrderType::MARKET_TO_LIMIT) && o->stopPrice != 0) return "WF5";
        if (o->timeInForce == TimeInForce::GTD && (o->expireTime == 0 || o->expireTime <= now_)) return "WF6";
        if (o->timeInForce != TimeInForce::GTD && o->expireTime != 0) return "WF7";
        if (o->orderType == OrderType::MARKET && o->timeInForce != TimeInForce::IOC && o->timeInForce != TimeInForce::FOK) return "WF8";
        if (o->orderType == OrderType::MARKET_TO_LIMIT && o->timeInForce != TimeInForce::GTC && o->timeInForce != TimeInForce::GTD && o->timeInForce != TimeInForce::DAY) return "WF8A";
        if (o->displayQty != 0 && (o->displayQty <= 0 || o->displayQty > o->quantity)) return "WF9";
        if (o->displayQty != 0 && o->orderType != OrderType::LIMIT) return "WF10";
        if (o->postOnly && o->orderType != OrderType::LIMIT) return "WF13";
        if (o->postOnly && (o->timeInForce == TimeInForce::IOC || o->timeInForce == TimeInForce::FOK)) return "WF14";
        if (o->postOnly && (o->orderType == OrderType::MARKET || o->orderType == OrderType::MARKET_TO_LIMIT)) return "WF15";
        if ((o->selfTradeGroup == 0) != (o->stpPolicy == STPPolicy::NONE)) return "WF16";
        if (o->minQty != 0 && (o->minQty <= 0 || o->minQty > o->quantity)) return "WF18";
        if (o->minQty != 0 && o->postOnly) return "WF19";
        if (o->timeInForce == TimeInForce::FOK && o->minQty != 0) return "WF20";
        return nullptr;
    }

    // ── Quantity checks ──
    template<typename M>
    Quantity availQty(const Order* inc, const M& contra, Quantity thresh) const {
        Quantity avail = 0;
        for (auto it = contra.begin(); it != contra.end(); ++it) {
            if (!canMatch(inc, it->first)) break;
            for (Order* r = it->second->head; r; r = r->next) {
                if (!stpConflict(inc, r)) {
                    avail += r->remainingQty;
                    if (avail >= thresh) return avail;
                }
            }
        }
        return avail;
    }
    bool fokCheck(const Order* o) const {
        return o->side == Side::BUY
            ? availQty(o, asks_, o->quantity) >= o->quantity
            : availQty(o, bids_, o->quantity) >= o->quantity;
    }
    bool minQtyCheck(const Order* o) const {
        return o->side == Side::BUY
            ? availQty(o, asks_, o->minQty) >= o->minQty
            : availQty(o, bids_, o->minQty) >= o->minQty;
    }

    // ── STP handler ──
    void handleStp(Order* inc, Order* rest) {
        STPPolicy pol = inc->stpPolicy;
        switch (pol) {
        case STPPolicy::CANCEL_NEWEST:
            inc->status = OrderStatus::CANCELLED;
            L.onOrderCancelled(*inc, "STP_CANCEL_NEWEST");
            break;
        case STPPolicy::CANCEL_OLDEST: {
            rest->status = OrderStatus::CANCELLED;
            rest->level->remove(rest);
            L.onOrderCancelled(*rest, "STP_CANCEL_OLDEST");
            idx_.erase(rest->id);
            freeOrd(rest);
            break;
        }
        case STPPolicy::CANCEL_BOTH: {
            inc->status = OrderStatus::CANCELLED;
            rest->status = OrderStatus::CANCELLED;
            rest->level->remove(rest);
            L.onOrderCancelled(*inc, "STP_CANCEL_BOTH");
            L.onOrderCancelled(*rest, "STP_CANCEL_BOTH");
            idx_.erase(rest->id);
            freeOrd(rest);
            break;
        }
        case STPPolicy::DECREMENT: {
            Quantity rq = std::min(inc->remainingQty, rest->visibleQty);
            inc->remainingQty -= rq;
            rest->remainingQty -= rq;
            rest->visibleQty -= rq;
            if (inc->displayQty > 0)
                inc->visibleQty = std::min(inc->displayQty, inc->remainingQty);
            else
                inc->visibleQty = inc->remainingQty;
            if (inc->remainingQty == 0) inc->status = OrderStatus::CANCELLED;
            if (rest->remainingQty == 0) rest->status = OrderStatus::CANCELLED;
            L.onOrderDecremented(*inc, *rest, rq);
            if (rest->remainingQty == 0) {
                rest->level->remove(rest);
                idx_.erase(rest->id);
                freeOrd(rest);
            } else if (rest->visibleQty == 0 && rest->displayQty > 0) {
                rest->visibleQty = std::min(rest->displayQty, rest->remainingQty);
                rest->timestamp = tick();
                PriceLevel* lv = rest->level;
                lv->remove(rest); lv->pushBack(rest);
            }
            break;
        }
        default: break;
        }
    }

    // ── Core matching ──
    template<typename M>
    void matchAgainst(Order* inc, M& contra) {
        auto li = contra.begin();
        while (inc->remainingQty > 0 && li != contra.end()) {
            PriceLevel* lv = li->second;
            if (!canMatch(inc, lv->price)) break;

            while (inc->remainingQty > 0 && !lv->empty()) {
                Order* rest = lv->front();

                if (stpConflict(inc, rest)) {
                    handleStp(inc, rest);
                    if (inc->status == OrderStatus::CANCELLED || inc->remainingQty == 0)
                        return;
                    continue;
                }

                Quantity fq = std::min(inc->remainingQty, rest->visibleQty);
                assert(fq > 0);

                trades_.push_back({tid_++, rest->price, fq,
                                   inc->id, rest->id, inc->side, now_});

                inc->remainingQty -= fq;
                rest->visibleQty  -= fq;
                rest->remainingQty -= fq;

                if (rest->visibleQty == 0 && rest->remainingQty > 0 && rest->displayQty > 0) {
                    rest->visibleQty = std::min(rest->displayQty, rest->remainingQty);
                    rest->timestamp = tick();
                    lv->remove(rest); lv->pushBack(rest);
                    continue;
                }
                if (rest->remainingQty == 0) {
                    rest->status = OrderStatus::FILLED;
                    lv->remove(rest);
                    idx_.erase(rest->id);
                    freeOrd(rest);
                } else {
                    rest->status = OrderStatus::PARTIALLY_FILLED;
                }
            }

            if (lv->empty()) { li = contra.erase(li); freeLvl(lv); }
            else ++li;
        }
    }

    void matchOrd(Order* o) {
        if (o->side == Side::BUY) matchAgainst(o, asks_);
        else matchAgainst(o, bids_);
    }

    // ── Dispose ──
    void dispose(Order* o, bool hasTr) {
        if (o->remainingQty == 0) { o->status = OrderStatus::FILLED; return; }
        switch (o->timeInForce) {
        case TimeInForce::IOC:
            o->status = OrderStatus::CANCELLED;
            L.onOrderCancelled(*o, "IOC_REMAINDER");
            return;
        case TimeInForce::FOK:
            assert(false && "FOK remainder after check");
            return;
        case TimeInForce::GTC:
            if (o->orderType == OrderType::MARKET) {
                o->status = OrderStatus::CANCELLED;
                L.onOrderCancelled(*o, "MARKET_NO_FULL_FILL");
                return;
            }
            insertOrder(o);
            o->status = hasTr ? OrderStatus::PARTIALLY_FILLED : OrderStatus::NEW;
            return;
        case TimeInForce::GTD:
        case TimeInForce::DAY:
            insertOrder(o);
            o->status = hasTr ? OrderStatus::PARTIALLY_FILLED : OrderStatus::NEW;
            return;
        }
    }

    // ── Emit trades & trigger stops ──
    void emitAndTrigger(size_t start, int depth) {
        size_t end = trades_.size();
        for (size_t i = start; i < end; ++i) {
            L.onTrade(trades_[i]);
            lastPx_ = trades_[i].price;
            if (depth < MAX_CASCADE)
                evalStops(trades_[i].price, depth);
        }
    }

    void evalStops(Price px, int depth) {
        if (stops_.empty()) return;
        std::vector<Order*> trig;
        for (size_t i = 0; i < stops_.size();) {
            Order* s = stops_[i];
            bool fire = s->side == Side::BUY ? px >= s->stopPrice : px <= s->stopPrice;
            if (fire) { trig.push_back(s); stops_[i] = stops_.back(); stops_.pop_back(); }
            else ++i;
        }
        if (trig.empty()) return;
        std::sort(trig.begin(), trig.end(),
                  [](Order* a, Order* b){ return a->timestamp < b->timestamp; });
        for (Order* s : trig) {
            s->status = OrderStatus::TRIGGERED;
            L.onOrderTriggered(*s);
            if (s->orderType == OrderType::STOP_LIMIT) s->orderType = OrderType::LIMIT;
            else s->orderType = OrderType::MARKET;
            s->stopPrice = 0;
            processActive(s, depth + 1);
        }
    }

    // ── Process pipeline ──
    void process(Order* o, int depth) {
        // Phase 1: Stop orders
        if (o->orderType == OrderType::STOP_LIMIT || o->orderType == OrderType::STOP_MARKET) {
            if (shouldTrigger(o)) {
                o->status = OrderStatus::TRIGGERED;
                L.onOrderTriggered(*o);
                if (o->orderType == OrderType::STOP_LIMIT) o->orderType = OrderType::LIMIT;
                else o->orderType = OrderType::MARKET;
                o->stopPrice = 0;
            } else {
                stops_.push_back(o);
                return;
            }
        }
        processActive(o, depth);
    }

    void processActive(Order* o, int depth) {
        // Phase 2: Post-only
        if (o->postOnly) {
            if (wouldCross(o)) {
                if (poPol_ == PostOnlyPolicy::REJECT) {
                    o->status = OrderStatus::CANCELLED;
                    L.onOrderCancelled(*o, "POST_ONLY_WOULD_CROSS");
                    idx_.erase(o->id); freeOrd(o); return;
                } else {
                    Price old = o->price;
                    if (o->side == Side::BUY)
                        o->price = asks_.begin()->first - tick_;
                    else
                        o->price = bids_.begin()->first + tick_;
                    L.onOrderRepriced(*o, old, o->price);
                }
            }
            insertOrder(o);
            o->status = OrderStatus::NEW;
            return;
        }

        // Phase 3: FOK / minQty
        if (o->timeInForce == TimeInForce::FOK && !fokCheck(o)) {
            o->status = OrderStatus::CANCELLED;
            L.onOrderCancelled(*o, "FOK_NOT_SATISFIABLE");
            idx_.erase(o->id); freeOrd(o); return;
        }
        if (o->minQty > 0 && !minQtyCheck(o)) {
            o->status = OrderStatus::CANCELLED;
            L.onOrderCancelled(*o, "MIN_QTY_NOT_SATISFIABLE");
            idx_.erase(o->id); freeOrd(o); return;
        }

        // Phase 4+: Match
        size_t ts = trades_.size();
        OrderId savedId = o->id;
        if (o->orderType == OrderType::MARKET_TO_LIMIT) {
            matchOrd(o);
            bool ht = trades_.size() > ts;
            if (!ht) {
                o->status = OrderStatus::CANCELLED;
                L.onOrderCancelled(*o, "MTL_NO_LIQUIDITY");
                idx_.erase(o->id); freeOrd(o); return;
            }
            o->price = trades_[ts].price;
            o->orderType = OrderType::LIMIT;
            if (o->minQty > 0) o->minQty = 0;
            if (o->remainingQty > 0 && o->status != OrderStatus::CANCELLED)
                matchOrd(o);
            if (o->status != OrderStatus::CANCELLED)
                dispose(o, true);
        } else {
            matchOrd(o);
            bool ht = trades_.size() > ts;
            if (o->minQty > 0 && ht) o->minQty = 0;
            if (o->status != OrderStatus::CANCELLED)
                dispose(o, ht);
        }

        emitAndTrigger(ts, depth);

        // If dispose() inserted o on the book and the stop cascade then
        // matched and filled o as a resting order, o is already freed.
        // Check via the index before touching o.
        if (!idx_.has(savedId)) return;
        if (o->status == OrderStatus::FILLED || o->status == OrderStatus::CANCELLED) {
            idx_.erase(o->id); freeOrd(o);
        }
    }
};
