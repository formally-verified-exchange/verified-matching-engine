/*
 * matching_engine.h
 * Price-Time Priority (FIFO) Matching Engine — Public API
 * C17, -fno-exceptions, no stdlib allocator on hot path
 */

#ifndef MATCHING_ENGINE_H
#define MATCHING_ENGINE_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>

/* -------------------------------------------------------------------------
 * Primitive domains
 * ------------------------------------------------------------------------- */

typedef uint64_t Price;       /* Fixed-point, e.g. cents * 100 => price in ticks */
typedef uint64_t Quantity;
typedef uint64_t Timestamp;
typedef uint32_t OrderId;
typedef uint16_t STPGroup;

#define PRICE_NULL    UINT64_MAX
#define QTY_NULL      UINT64_MAX
#define TIMESTAMP_NULL UINT64_MAX
#define ORDER_ID_NULL  0u
#define STP_GROUP_NULL 0u

/* -------------------------------------------------------------------------
 * Enumerations — packed into uint8_t for struct density
 * ------------------------------------------------------------------------- */

typedef uint8_t Side;
#define SIDE_BUY  ((Side)0)
#define SIDE_SELL ((Side)1)

typedef uint8_t OrderType;
#define ORDER_TYPE_LIMIT          ((OrderType)0)
#define ORDER_TYPE_MARKET         ((OrderType)1)
#define ORDER_TYPE_MARKET_TO_LIMIT ((OrderType)2)
#define ORDER_TYPE_STOP_LIMIT     ((OrderType)3)
#define ORDER_TYPE_STOP_MARKET    ((OrderType)4)

typedef uint8_t TimeInForce;
#define TIF_GTC ((TimeInForce)0)
#define TIF_GTD ((TimeInForce)1)
#define TIF_IOC ((TimeInForce)2)
#define TIF_FOK ((TimeInForce)3)
#define TIF_DAY ((TimeInForce)4)

typedef uint8_t OrderStatus;
#define STATUS_NEW              ((OrderStatus)0)
#define STATUS_PARTIALLY_FILLED ((OrderStatus)1)
#define STATUS_FILLED           ((OrderStatus)2)
#define STATUS_CANCELLED        ((OrderStatus)3)
#define STATUS_REJECTED         ((OrderStatus)4)
#define STATUS_EXPIRED          ((OrderStatus)5)
#define STATUS_TRIGGERED        ((OrderStatus)6)

typedef uint8_t STPPolicy;
#define STP_CANCEL_NEWEST  ((STPPolicy)0)
#define STP_CANCEL_OLDEST  ((STPPolicy)1)
#define STP_CANCEL_BOTH    ((STPPolicy)2)
#define STP_DECREMENT      ((STPPolicy)3)
#define STP_NONE           ((STPPolicy)255)

typedef uint8_t CancelReason;
#define CANCEL_USER_REQUESTED        ((CancelReason)0)
#define CANCEL_IOC_REMAINDER         ((CancelReason)1)
#define CANCEL_FOK_NOT_SATISFIABLE   ((CancelReason)2)
#define CANCEL_MIN_QTY               ((CancelReason)3)
#define CANCEL_MARKET_NO_FULL_FILL   ((CancelReason)4)
#define CANCEL_MTL_NO_LIQUIDITY      ((CancelReason)5)
#define CANCEL_POST_ONLY_WOULD_CROSS ((CancelReason)6)
#define CANCEL_STP_NEWEST            ((CancelReason)7)
#define CANCEL_STP_OLDEST            ((CancelReason)8)
#define CANCEL_STP_BOTH              ((CancelReason)9)

typedef uint8_t RejectReason;
#define REJECT_WF1  ((RejectReason)1)
#define REJECT_WF2  ((RejectReason)2)
#define REJECT_WF2A ((RejectReason)3)
#define REJECT_WF2B ((RejectReason)4)
#define REJECT_WF3  ((RejectReason)5)
#define REJECT_WF4  ((RejectReason)6)
#define REJECT_WF5  ((RejectReason)7)
#define REJECT_WF6  ((RejectReason)8)
#define REJECT_WF7  ((RejectReason)9)
#define REJECT_WF8  ((RejectReason)10)
#define REJECT_WF8A ((RejectReason)11)
#define REJECT_WF9  ((RejectReason)12)
#define REJECT_WF10 ((RejectReason)13)
#define REJECT_WF11 ((RejectReason)14)
#define REJECT_WF12 ((RejectReason)15)
#define REJECT_WF13 ((RejectReason)16)
#define REJECT_WF14 ((RejectReason)17)
#define REJECT_WF15 ((RejectReason)18)
#define REJECT_WF16 ((RejectReason)19)
#define REJECT_WF17 ((RejectReason)20)
#define REJECT_WF18 ((RejectReason)21)
#define REJECT_WF19 ((RejectReason)22)
#define REJECT_WF20 ((RejectReason)23)

/* -------------------------------------------------------------------------
 * Order (intrusive doubly-linked list within a price level)
 * Target: 2 cache lines (128 bytes)
 * ------------------------------------------------------------------------- */

typedef struct Order Order;
struct Order {
    /* === Cache line 1 (bytes 0-63): hot matching path ===
     * Everything the inner do_match loop reads/writes lives here.
     * One cache line fetch per order traversal. */
    Price       m_price;          /* limit price; PRICE_NULL for MARKET */
    Side        m_side;
    OrderType   m_order_type;
    STPGroup    m_stp_group;      /* 0 = no STP group */
    STPPolicy   m_stp_policy;
    OrderStatus m_status;
    uint8_t     m_pad0[2];

    Quantity    m_remaining_qty;  /* unfilled quantity */
    Quantity    m_visible_qty;    /* currently exposed (iceberg support) */

    Order      *m_next;           /* intrusive FIFO queue — chased every iteration */
    Order      *m_prev;           /* removal only, but free in this cache line */
    void       *m_level;          /* PriceLevel* — removal only */
    Quantity    m_display_qty;    /* iceberg slice size; QTY_NULL if not iceberg */

    /* === Cache line 2 (bytes 64-127): cold path ===
     * Order entry, expiry, identity — not touched by inner loop. */
    Price       m_stop_price;     /* stop activation price; PRICE_NULL if none */
    Quantity    m_original_qty;   /* original quantity at creation */
    Quantity    m_min_qty;        /* minimum first-fill qty; QTY_NULL if none */
    Timestamp   m_timestamp;      /* arrival time — determines FIFO priority */
    Timestamp   m_expire_time;    /* GTD expiry; TIMESTAMP_NULL if not GTD */
    OrderId     m_id;
    TimeInForce m_tif;
    uint8_t     m_post_only;      /* bool, 1 byte */
    uint8_t     m_pad1[6];
};

static_assert(sizeof(Order) <= 128, "Order must fit in 2 cache lines");

/* -------------------------------------------------------------------------
 * PriceLevel (intrusive doubly-linked list of levels)
 * ------------------------------------------------------------------------- */

typedef struct PriceLevel PriceLevel;
struct PriceLevel {
    Price       m_price;
    Order      *m_head;    /* front of FIFO queue (highest priority) */
    Order      *m_tail;    /* back of FIFO queue */
    uint32_t    m_count;   /* number of orders */
    uint32_t    m_pad;

    PriceLevel *m_prev;    /* prev level in sorted list */
    PriceLevel *m_next;    /* next level in sorted list */
};

static_assert(sizeof(PriceLevel) <= 64, "PriceLevel fits in 1 cache line");

/* -------------------------------------------------------------------------
 * Trade record
 * ------------------------------------------------------------------------- */

typedef struct Trade {
    uint64_t m_trade_id;
    Price    m_price;
    Quantity m_quantity;
    OrderId  m_aggressor_id;
    OrderId  m_passive_id;
    Side     m_aggressor_side;
    uint8_t  m_pad[7];
    Timestamp m_timestamp;
} Trade;

/* -------------------------------------------------------------------------
 * Event types and callback
 * ------------------------------------------------------------------------- */

#define EVT_ORDER_ACCEPTED    1
#define EVT_ORDER_REJECTED    2
#define EVT_TRADE_EXECUTED    3
#define EVT_ORDER_CANCELLED   4
#define EVT_ORDER_EXPIRED     5
#define EVT_ORDER_TRIGGERED   6
#define EVT_ORDER_DECREMENTED 7
#define EVT_BOOK_UPDATE       8

typedef struct {
    const Order *m_order;
    RejectReason m_reason;
} EvtRejected;

typedef struct {
    const Order *m_order;
    CancelReason m_reason;
} EvtCancelled;

typedef struct {
    const Order   *m_incoming;
    const Order   *m_resting;
    Quantity       m_qty;
} EvtDecremented;

typedef void (*EventCallback)(int event_type, const void *data, void *ctx);

/* -------------------------------------------------------------------------
 * Pool allocator
 * ------------------------------------------------------------------------- */

#define POOL_ORDER_CAPACITY   (1 << 20)  /* 1M orders */
#define POOL_LEVEL_CAPACITY   (1 << 16)  /* 64K price levels */
#define POOL_TRADE_CAPACITY   (1 << 20)  /* 1M trades (ring buffer) */

typedef struct {
    Order    m_storage[POOL_ORDER_CAPACITY];
    Order   *m_free_head;
    uint32_t m_allocated;
} OrderPool;

typedef struct {
    PriceLevel  m_storage[POOL_LEVEL_CAPACITY];
    PriceLevel *m_free_head;
    uint32_t    m_allocated;
} LevelPool;

/* -------------------------------------------------------------------------
 * Engine order index (flat array for O(1) lookup by ID)
 * ------------------------------------------------------------------------- */

#define MAX_ORDER_ID (POOL_ORDER_CAPACITY)

/* -------------------------------------------------------------------------
 * Order book (one side = linked list of price levels)
 * bids: descending price (best = head)
 * asks: ascending price (best = head)
 * stops: singly-linked list via StopNode
 * ------------------------------------------------------------------------- */

typedef struct {
    PriceLevel  *m_bids_head;      /* best bid */
    PriceLevel  *m_asks_head;      /* best ask */
    /* Stop orders use intrusive m_prev/m_next links.
     * Two unsorted singly-linked lists (buy and sell).
     * min_buy_stop and max_sell_stop provide O(1) early exit for evaluate_stops. */
    Order       *m_buy_stops_head;   /* BUY  stops: trigger when price >= stop_price */
    Order       *m_sell_stops_head;  /* SELL stops: trigger when price <= stop_price */
    Price        m_min_buy_stop;     /* minimum BUY stop_price in list; PRICE_NULL if empty */
    Price        m_max_sell_stop;    /* maximum SELL stop_price in list; 0 if empty */
    uint32_t     m_bid_levels;
    uint32_t     m_ask_levels;
    uint32_t     m_stop_count;
    uint32_t     m_pad;
} OrderBook;

/* -------------------------------------------------------------------------
 * Trade ring buffer (output buffer, not for storage)
 * ------------------------------------------------------------------------- */

typedef struct {
    Trade    m_trades[POOL_TRADE_CAPACITY];
    uint32_t m_head;  /* read position */
    uint32_t m_tail;  /* write position */
    uint32_t m_count;
} TradeBuffer;

/* -------------------------------------------------------------------------
 * Main engine struct
 * ------------------------------------------------------------------------- */

#define MAX_CASCADE_DEPTH 64

#define ID_FREE_STACK_CAP (1 << 16)  /* 64K recycled IDs */

typedef struct {
    OrderBook     m_book;
    Order        *m_order_index[MAX_ORDER_ID + 1]; /* index[0] unused */
    OrderPool     m_order_pool;
    LevelPool     m_level_pool;
    TradeBuffer   m_trade_buf;

    Timestamp     m_clock;
    uint64_t      m_trade_id_seq;
    uint32_t      m_next_order_id;  /* auto-increment when user doesn't supply */
    uint32_t      m_cascade_depth;  /* current recursion depth guard */

    /* Free-ID stack for O(1) auto-assign after ID space wraps */
    OrderId       m_id_free_stack[ID_FREE_STACK_CAP];
    uint32_t      m_id_free_count;

    EventCallback m_callback;
    void         *m_callback_ctx;
} MatchingEngine;

/* -------------------------------------------------------------------------
 * Order submission descriptor (passed by value to process_order)
 * ------------------------------------------------------------------------- */

typedef struct {
    OrderId     id;          /* 0 = auto-assign */
    Price       price;       /* PRICE_NULL for MARKET */
    Price       stop_price;  /* PRICE_NULL if not stop */
    Quantity    quantity;
    Quantity    display_qty; /* QTY_NULL = not iceberg */
    Quantity    min_qty;     /* QTY_NULL = none */
    Timestamp   expire_time; /* TIMESTAMP_NULL if not GTD */
    STPGroup    stp_group;   /* 0 = no STP */
    Side        side;
    OrderType   order_type;
    TimeInForce tif;
    STPPolicy   stp_policy;  /* STP_NONE if no STP */
    uint8_t     post_only;
} OrderDesc;

/* -------------------------------------------------------------------------
 * Amend descriptor
 * ------------------------------------------------------------------------- */

typedef struct {
    OrderId  id;
    Price    new_price;    /* PRICE_NULL = no change */
    Quantity new_qty;      /* QTY_NULL = no change */
} AmendDesc;

/* -------------------------------------------------------------------------
 * Return codes
 * ------------------------------------------------------------------------- */

typedef int ME_Result;
#define ME_OK              0
#define ME_ERR_NOT_FOUND  -1
#define ME_ERR_INVALID    -2
#define ME_ERR_POOL_FULL  -3

/* -------------------------------------------------------------------------
 * Public API
 * ------------------------------------------------------------------------- */

/* Initialise the engine. Must be called before any other function.
 * callback may be NULL (no-op). */
void engine_init(MatchingEngine *e, EventCallback cb, void *ctx);

/* Submit a new order. Returns ME_OK on acceptance (even if immediately
 * cancelled/filled), ME_ERR_POOL_FULL if resources exhausted. */
ME_Result engine_process(MatchingEngine *restrict e, const OrderDesc *restrict desc);

/* Cancel an active order by ID. */
ME_Result engine_cancel(MatchingEngine *restrict e, OrderId id);

/* Amend an active order (cancel-replace semantics). */
ME_Result engine_amend(MatchingEngine *restrict e, const AmendDesc *restrict desc);

/* Expire orders whose time has come. Pass current logical time.
 * Returns number of orders expired. */
int engine_expire(MatchingEngine *restrict e, Timestamp now);

/* Query: O(1) lookup. Returns NULL if not found / already filled. */
const Order *engine_find_order(const MatchingEngine *e, OrderId id);

/* Best bid/ask prices (PRICE_NULL if book empty on that side). */
Price engine_best_bid(const MatchingEngine *e);
Price engine_best_ask(const MatchingEngine *e);

/* Debug: validate all invariants. Calls assert() on violation. */
void engine_check_invariants(const MatchingEngine *e);

#endif /* MATCHING_ENGINE_H */
