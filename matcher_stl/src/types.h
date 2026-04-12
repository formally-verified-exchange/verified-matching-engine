#pragma once
#include <cstdint>
#include <algorithm>

using Price       = int64_t;
using Quantity    = int64_t;
using Timestamp   = uint64_t;
using OrderId     = uint64_t;
using TradeId     = uint64_t;
using SelfTradeGroup = uint64_t;

enum class Side : uint8_t { BUY, SELL };
enum class OrderType : uint8_t { LIMIT, MARKET, MARKET_TO_LIMIT, STOP_LIMIT, STOP_MARKET };
enum class TimeInForce : uint8_t { GTC, GTD, IOC, FOK, DAY };
enum class OrderStatus : uint8_t { NEW, PARTIALLY_FILLED, FILLED, CANCELLED, REJECTED, EXPIRED, TRIGGERED };
enum class STPPolicy : uint8_t { NONE, CANCEL_NEWEST, CANCEL_OLDEST, CANCEL_BOTH, DECREMENT };
enum class PostOnlyPolicy : uint8_t { REJECT, REPRICE };

constexpr Side oppositeSide(Side s) { return s == Side::BUY ? Side::SELL : Side::BUY; }

struct PriceLevel;

struct Order {
    OrderId id = 0;
    Side side = Side::BUY;
    OrderType orderType = OrderType::LIMIT;
    TimeInForce timeInForce = TimeInForce::GTC;
    Price price = 0;
    Price stopPrice = 0;
    Quantity quantity = 0;
    Quantity remainingQty = 0;
    Quantity minQty = 0;
    Quantity displayQty = 0;
    Quantity visibleQty = 0;
    bool postOnly = false;
    OrderStatus status = OrderStatus::NEW;
    Timestamp timestamp = 0;
    Timestamp expireTime = 0;
    SelfTradeGroup selfTradeGroup = 0;
    STPPolicy stpPolicy = STPPolicy::NONE;
    Order* prev = nullptr;
    Order* next = nullptr;
    PriceLevel* level = nullptr;
};

struct PriceLevel {
    Price price = 0;
    Order* head = nullptr;
    Order* tail = nullptr;

    bool empty() const { return head == nullptr; }
    Order* front() const { return head; }

    void pushBack(Order* o) {
        o->prev = tail; o->next = nullptr; o->level = this;
        if (tail) tail->next = o; else head = o;
        tail = o;
    }

    void remove(Order* o) {
        if (o->prev) o->prev->next = o->next; else head = o->next;
        if (o->next) o->next->prev = o->prev; else tail = o->prev;
        o->prev = o->next = nullptr; o->level = nullptr;
    }
};

struct Trade {
    TradeId tradeId = 0;
    Price price = 0;
    Quantity quantity = 0;
    OrderId aggressorId = 0;
    OrderId passiveId = 0;
    Side aggressorSide = Side::BUY;
    Timestamp timestamp = 0;
};

struct OrderInput {
    OrderId id = 0;
    Side side = Side::BUY;
    OrderType orderType = OrderType::LIMIT;
    TimeInForce timeInForce = TimeInForce::GTC;
    Price price = 0;
    Price stopPrice = 0;
    Quantity quantity = 0;
    Quantity minQty = 0;
    Quantity displayQty = 0;
    bool postOnly = false;
    Timestamp expireTime = 0;
    SelfTradeGroup selfTradeGroup = 0;
    STPPolicy stpPolicy = STPPolicy::NONE;
};

struct NullListener {
    void onOrderAccepted(const Order&) {}
    void onOrderRejected(const Order&, const char*) {}
    void onTrade(const Trade&) {}
    void onOrderCancelled(const Order&, const char*) {}
    void onOrderExpired(const Order&) {}
    void onOrderTriggered(const Order&) {}
    void onOrderDecremented(const Order&, const Order&, Quantity) {}
    void onOrderRepriced(const Order&, Price, Price) {}
};
