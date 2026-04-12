/*
 * main.c
 * Tests + Benchmark for the Price-Time Priority Matching Engine
 * C17
 */

#define _POSIX_C_SOURCE 200809L
#include "matching_engine.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>

/* =========================================================================
 * Test helpers
 * ========================================================================= */

#define MAX_EVENTS 8192

typedef struct {
    int         type;
    /* trades */
    Price       trade_price;
    Quantity    trade_qty;
    OrderId     aggressor_id;
    OrderId     passive_id;
    /* cancelled / rejected / triggered / decremented */
    OrderId     order_id;
    OrderStatus order_status;
    int         reason;
    /* triggered: order id of triggered order */
    OrderId     triggered_id;
    /* decremented */
    OrderId     decrement_incoming_id;
    OrderId     decrement_resting_id;
    Quantity    decrement_qty;
} RecordedEvent;

typedef struct {
    RecordedEvent events[MAX_EVENTS];
    int           count;
    int           trade_count;
    int           cancel_count;
    int           reject_count;
    int           trigger_count;
    int           decrement_count;
    int           accept_count;
    int           expire_count;
} EventLog;

static void event_log_reset(EventLog *log) {
    memset(log, 0, sizeof(*log));
}

static void record_event(int type, const void *data, void *ctx) {
    EventLog *log = (EventLog *)ctx;
    if (log->count >= MAX_EVENTS) return;
    RecordedEvent *ev = &log->events[log->count++];
    ev->type = type;
    switch (type) {
    case EVT_ORDER_ACCEPTED: {
        const Order *o = (const Order *)data;
        ev->order_id = o->m_id;
        log->accept_count++;
        break;
    }
    case EVT_TRADE_EXECUTED: {
        const Trade *t = (const Trade *)data;
        ev->trade_price  = t->m_price;
        ev->trade_qty    = t->m_quantity;
        ev->aggressor_id = t->m_aggressor_id;
        ev->passive_id   = t->m_passive_id;
        log->trade_count++;
        break;
    }
    case EVT_ORDER_CANCELLED: {
        const EvtCancelled *c = (const EvtCancelled *)data;
        ev->order_id     = c->m_order->m_id;
        ev->order_status = c->m_order->m_status;
        ev->reason       = c->m_reason;
        log->cancel_count++;
        break;
    }
    case EVT_ORDER_REJECTED: {
        const EvtRejected *r = (const EvtRejected *)data;
        ev->order_id = r->m_order->m_id;
        ev->reason   = r->m_reason;
        log->reject_count++;
        break;
    }
    case EVT_ORDER_EXPIRED: {
        const Order *o = (const Order *)data;
        ev->order_id = o->m_id;
        log->expire_count++;
        break;
    }
    case EVT_ORDER_TRIGGERED: {
        const Order *o = (const Order *)data;
        ev->triggered_id = o->m_id;
        ev->order_id     = o->m_id;
        log->trigger_count++;
        break;
    }
    case EVT_ORDER_DECREMENTED: {
        const EvtDecremented *d = (const EvtDecremented *)data;
        ev->decrement_incoming_id = d->m_incoming->m_id;
        ev->decrement_resting_id  = d->m_resting->m_id;
        ev->decrement_qty         = d->m_qty;
        log->decrement_count++;
        break;
    }
    default:
        break;
    }
}

static MatchingEngine *alloc_engine(EventLog *log) {
    MatchingEngine *e = (MatchingEngine *)calloc(1, sizeof(MatchingEngine));
    assert(e && "out of memory for engine");
    engine_init(e, record_event, log);
    return e;
}

static void free_engine(MatchingEngine *e) {
    free(e);
}

/* -------------------------------------------------------------------------
 * Order submission helpers
 * ------------------------------------------------------------------------- */

static ME_Result submit_limit(MatchingEngine *e, OrderId id, Side side,
                               Price price, Quantity qty, TimeInForce tif) {
    OrderDesc d = {0};
    d.id          = id;
    d.side        = side;
    d.order_type  = ORDER_TYPE_LIMIT;
    d.price       = price;
    d.stop_price  = PRICE_NULL;
    d.quantity    = qty;
    d.display_qty = QTY_NULL;
    d.min_qty     = QTY_NULL;
    d.expire_time = TIMESTAMP_NULL;
    d.tif         = tif;
    d.stp_policy  = STP_NONE;
    return engine_process(e, &d);
}

static ME_Result submit_market(MatchingEngine *e, OrderId id, Side side,
                                Quantity qty, TimeInForce tif) {
    OrderDesc d = {0};
    d.id          = id;
    d.side        = side;
    d.order_type  = ORDER_TYPE_MARKET;
    d.price       = PRICE_NULL;
    d.stop_price  = PRICE_NULL;
    d.quantity    = qty;
    d.display_qty = QTY_NULL;
    d.min_qty     = QTY_NULL;
    d.expire_time = TIMESTAMP_NULL;
    d.tif         = tif;
    d.stp_policy  = STP_NONE;
    return engine_process(e, &d);
}

static ME_Result submit_limit_gtd(MatchingEngine *e, OrderId id, Side side,
                                   Price price, Quantity qty, Timestamp expire) {
    OrderDesc d = {0};
    d.id          = id;
    d.side        = side;
    d.order_type  = ORDER_TYPE_LIMIT;
    d.price       = price;
    d.stop_price  = PRICE_NULL;
    d.quantity    = qty;
    d.display_qty = QTY_NULL;
    d.min_qty     = QTY_NULL;
    d.expire_time = expire;
    d.tif         = TIF_GTD;
    d.stp_policy  = STP_NONE;
    return engine_process(e, &d);
}

static ME_Result submit_limit_stp(MatchingEngine *e, OrderId id, Side side,
                                   Price price, Quantity qty, TimeInForce tif,
                                   STPGroup grp, STPPolicy pol) {
    OrderDesc d = {0};
    d.id          = id;
    d.side        = side;
    d.order_type  = ORDER_TYPE_LIMIT;
    d.price       = price;
    d.stop_price  = PRICE_NULL;
    d.quantity    = qty;
    d.display_qty = QTY_NULL;
    d.min_qty     = QTY_NULL;
    d.expire_time = TIMESTAMP_NULL;
    d.tif         = tif;
    d.stp_group   = grp;
    d.stp_policy  = pol;
    return engine_process(e, &d);
}

static ME_Result submit_stop_limit(MatchingEngine *e, OrderId id, Side side,
                                    Price price, Price stop_price, Quantity qty,
                                    TimeInForce tif) {
    OrderDesc d = {0};
    d.id          = id;
    d.side        = side;
    d.order_type  = ORDER_TYPE_STOP_LIMIT;
    d.price       = price;
    d.stop_price  = stop_price;
    d.quantity    = qty;
    d.display_qty = QTY_NULL;
    d.min_qty     = QTY_NULL;
    d.expire_time = TIMESTAMP_NULL;
    d.tif         = tif;
    d.stp_policy  = STP_NONE;
    return engine_process(e, &d);
}

static ME_Result submit_stop_market(MatchingEngine *e, OrderId id, Side side,
                                     Price stop_price, Quantity qty,
                                     TimeInForce tif) {
    OrderDesc d = {0};
    d.id          = id;
    d.side        = side;
    d.order_type  = ORDER_TYPE_STOP_MARKET;
    d.price       = PRICE_NULL;
    d.stop_price  = stop_price;
    d.quantity    = qty;
    d.display_qty = QTY_NULL;
    d.min_qty     = QTY_NULL;
    d.expire_time = TIMESTAMP_NULL;
    d.tif         = tif;
    d.stp_policy  = STP_NONE;
    return engine_process(e, &d);
}

static ME_Result submit_iceberg(MatchingEngine *e, OrderId id, Side side,
                                 Price price, Quantity qty, Quantity display,
                                 TimeInForce tif) {
    OrderDesc d = {0};
    d.id          = id;
    d.side        = side;
    d.order_type  = ORDER_TYPE_LIMIT;
    d.price       = price;
    d.stop_price  = PRICE_NULL;
    d.quantity    = qty;
    d.display_qty = display;
    d.min_qty     = QTY_NULL;
    d.expire_time = TIMESTAMP_NULL;
    d.tif         = tif;
    d.stp_policy  = STP_NONE;
    return engine_process(e, &d);
}

static ME_Result submit_post_only(MatchingEngine *e, OrderId id, Side side,
                                   Price price, Quantity qty, TimeInForce tif) {
    OrderDesc d = {0};
    d.id          = id;
    d.side        = side;
    d.order_type  = ORDER_TYPE_LIMIT;
    d.price       = price;
    d.stop_price  = PRICE_NULL;
    d.quantity    = qty;
    d.display_qty = QTY_NULL;
    d.min_qty     = QTY_NULL;
    d.expire_time = TIMESTAMP_NULL;
    d.tif         = tif;
    d.stp_policy  = STP_NONE;
    d.post_only   = 1;
    return engine_process(e, &d);
}

static ME_Result submit_min_qty(MatchingEngine *e, OrderId id, Side side,
                                 Price price, Quantity qty, Quantity min_qty,
                                 TimeInForce tif) {
    OrderDesc d = {0};
    d.id          = id;
    d.side        = side;
    d.order_type  = ORDER_TYPE_LIMIT;
    d.price       = price;
    d.stop_price  = PRICE_NULL;
    d.quantity    = qty;
    d.display_qty = QTY_NULL;
    d.min_qty     = min_qty;
    d.expire_time = TIMESTAMP_NULL;
    d.tif         = tif;
    d.stp_policy  = STP_NONE;
    return engine_process(e, &d);
}

static ME_Result submit_mtl(MatchingEngine *e, OrderId id, Side side,
                             Quantity qty, TimeInForce tif) {
    OrderDesc d = {0};
    d.id          = id;
    d.side        = side;
    d.order_type  = ORDER_TYPE_MARKET_TO_LIMIT;
    d.price       = PRICE_NULL;
    d.stop_price  = PRICE_NULL;
    d.quantity    = qty;
    d.display_qty = QTY_NULL;
    d.min_qty     = QTY_NULL;
    d.expire_time = TIMESTAMP_NULL;
    d.tif         = tif;
    d.stp_policy  = STP_NONE;
    return engine_process(e, &d);
}

/* -------------------------------------------------------------------------
 * EventLog query helpers
 * ------------------------------------------------------------------------- */

static int has_trade(const EventLog *log, OrderId agg, OrderId pass,
                     Price price, Quantity qty) {
    for (int i = 0; i < log->count; i++) {
        const RecordedEvent *ev = &log->events[i];
        if (ev->type == EVT_TRADE_EXECUTED &&
            ev->aggressor_id == agg &&
            ev->passive_id   == pass &&
            ev->trade_price  == price &&
            ev->trade_qty    == qty)
            return 1;
    }
    return 0;
}

static int has_cancel(const EventLog *log, OrderId id, CancelReason reason) {
    for (int i = 0; i < log->count; i++) {
        const RecordedEvent *ev = &log->events[i];
        if (ev->type == EVT_ORDER_CANCELLED &&
            ev->order_id == id &&
            (int)ev->reason == (int)reason)
            return 1;
    }
    return 0;
}

static int has_reject(const EventLog *log, OrderId id, RejectReason reason) {
    for (int i = 0; i < log->count; i++) {
        const RecordedEvent *ev = &log->events[i];
        if (ev->type == EVT_ORDER_REJECTED &&
            ev->order_id == id &&
            (int)ev->reason == (int)reason)
            return 1;
    }
    return 0;
}

static int has_decrement(const EventLog *log, OrderId incoming, OrderId resting,
                         Quantity qty) {
    for (int i = 0; i < log->count; i++) {
        const RecordedEvent *ev = &log->events[i];
        if (ev->type == EVT_ORDER_DECREMENTED &&
            ev->decrement_incoming_id == incoming &&
            ev->decrement_resting_id  == resting &&
            ev->decrement_qty         == qty)
            return 1;
    }
    return 0;
}

static int count_type(const EventLog *log, int type) {
    int n = 0;
    for (int i = 0; i < log->count; i++)
        if (log->events[i].type == type) n++;
    return n;
}

/* Return the nth event (0-based) of given type, or NULL */
static const RecordedEvent *nth_event_of_type(const EventLog *log, int type,
                                               int n) {
    int cnt = 0;
    for (int i = 0; i < log->count; i++) {
        if (log->events[i].type == type) {
            if (cnt == n) return &log->events[i];
            cnt++;
        }
    }
    return NULL;
}


/* =========================================================================
 * 1. BASIC LIMIT MATCHING
 * ========================================================================= */

static void test_limit_rest_buy(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(engine_best_bid(e) == 100);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_status == STATUS_NEW);
    assert(count_type(&log, EVT_ORDER_ACCEPTED) == 1);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_limit_rest_buy\n");
}

static void test_limit_rest_sell(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(engine_best_ask(e) == 100);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_status == STATUS_NEW);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_limit_rest_sell\n");
}

static void test_limit_match_exact(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    /* Both filled — verify via events */
    assert(has_trade(&log, 2, 1, 100, 10));
    assert(has_cancel(&log, 1, CANCEL_USER_REQUESTED) == 0); /* no cancel — filled */
    assert(engine_find_order(e, 1) == NULL); /* freed */
    assert(engine_find_order(e, 2) == NULL);
    assert(engine_best_bid(e) == PRICE_NULL);
    assert(engine_best_ask(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_limit_match_exact\n");
}

static void test_limit_match_price_improvement(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  105, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL,  95, 10, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 2, 1, 105, 10)); /* trade at passive price */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_limit_match_price_improvement\n");
}

static void test_limit_partial_fill(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 50, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 30, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 2, 1, 100, 30));
    const Order *o1 = engine_find_order(e, 1);
    assert(o1 && o1->m_status == STATUS_PARTIALLY_FILLED);
    assert(o1->m_remaining_qty == 20);
    /* order 2 fully filled — not in index */
    assert(engine_find_order(e, 2) == NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_limit_partial_fill\n");
}

static void test_limit_fifo_same_price(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 4, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(engine_find_order(e, 1) == NULL); /* filled first */
    assert(engine_find_order(e, 2) != NULL);
    assert(engine_find_order(e, 3) != NULL);
    assert(has_trade(&log, 4, 1, 100, 10));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_limit_fifo_same_price\n");
}

static void test_limit_fifo_partial_chain(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 7, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY, 100, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_BUY, 100, 8, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 4, SIDE_SELL, 100, 15, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 4, 1, 100, 7));
    assert(has_trade(&log, 4, 2, 100, 5));
    assert(has_trade(&log, 4, 3, 100, 3));
    assert(engine_find_order(e, 1) == NULL); /* filled */
    assert(engine_find_order(e, 2) == NULL); /* filled */
    const Order *o3 = engine_find_order(e, 3);
    assert(o3 && o3->m_status == STATUS_PARTIALLY_FILLED);
    assert(o3->m_remaining_qty == 5);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_limit_fifo_partial_chain\n");
}

static void test_limit_sweep_two_levels(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  99, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_SELL, 98, 25, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 3, 1, 100, 10));
    assert(has_trade(&log, 3, 2,  99, 10));
    const Order *o3 = engine_find_order(e, 3);
    assert(o3 && o3->m_remaining_qty == 5);
    assert(o3->m_status == STATUS_PARTIALLY_FILLED);
    assert(engine_best_ask(e) == 98);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_limit_sweep_two_levels\n");
}

static void test_limit_sweep_three_levels(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 51, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_SELL, 52, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 4, SIDE_BUY,  55, 12, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 4, 1, 50, 5));
    assert(has_trade(&log, 4, 2, 51, 5));
    assert(has_trade(&log, 4, 3, 52, 2));
    assert(engine_find_order(e, 4) == NULL); /* filled */
    const Order *o3 = engine_find_order(e, 3);
    assert(o3 && o3->m_remaining_qty == 3);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_limit_sweep_three_levels\n");
}

static void test_limit_no_cross(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 101, 10, TIF_GTC) == ME_OK);
    assert(engine_find_order(e, 1)->m_status == STATUS_NEW);
    assert(engine_find_order(e, 2)->m_status == STATUS_NEW);
    assert(engine_best_bid(e) == 100);
    assert(engine_best_ask(e) == 101);
    assert(log.trade_count == 0);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_limit_no_cross\n");
}

static void test_limit_sell_aggressor(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  50, 10, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 2, 1, 50, 10));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_limit_sell_aggressor\n");
}

static void test_level_cleanup_after_full_fill(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    assert(engine_best_bid(e) == 100);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(engine_best_bid(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_level_cleanup_after_full_fill\n");
}

/* =========================================================================
 * 2. MARKET ORDERS
 * ========================================================================= */

static void test_market_full_fill(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 20, TIF_GTC) == ME_OK);
    assert(submit_market(e, 2, SIDE_BUY, 20, TIF_IOC) == ME_OK);
    assert(engine_find_order(e, 2) == NULL); /* filled */
    assert(has_trade(&log, 2, 1, 50, 20));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_market_full_fill\n");
}

static void test_market_partial_ioc(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_market(e, 2, SIDE_BUY, 20, TIF_IOC) == ME_OK);
    assert(has_trade(&log, 2, 1, 50, 10));
    assert(has_cancel(&log, 2, CANCEL_IOC_REMAINDER));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_market_partial_ioc\n");
}

static void test_market_empty_book(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_market(e, 1, SIDE_BUY, 10, TIF_IOC) == ME_OK);
    assert(has_cancel(&log, 1, CANCEL_IOC_REMAINDER));
    assert(log.trade_count == 0);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_market_empty_book\n");
}

static void test_market_fok_full(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_market(e, 2, SIDE_BUY, 10, TIF_FOK) == ME_OK);
    assert(engine_find_order(e, 2) == NULL); /* filled */
    assert(has_trade(&log, 2, 1, 50, 10));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_market_fok_full\n");
}

static void test_market_fok_reject(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_market(e, 2, SIDE_BUY, 10, TIF_FOK) == ME_OK);
    assert(has_cancel(&log, 2, CANCEL_FOK_NOT_SATISFIABLE));
    const Order *o1 = engine_find_order(e, 1);
    assert(o1 && o1->m_remaining_qty == 5);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_market_fok_reject\n");
}

static void test_market_sweep_multiple_levels(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 51, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_SELL, 52, 5, TIF_GTC) == ME_OK);
    assert(submit_market(e, 4, SIDE_BUY, 15, TIF_IOC) == ME_OK);
    assert(has_trade(&log, 4, 1, 50, 5));
    assert(has_trade(&log, 4, 2, 51, 5));
    assert(has_trade(&log, 4, 3, 52, 5));
    assert(engine_find_order(e, 4) == NULL); /* filled */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_market_sweep_multiple_levels\n");
}

static void test_market_sell(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_market(e, 2, SIDE_SELL, 10, TIF_IOC) == ME_OK);
    assert(has_trade(&log, 2, 1, 100, 10));
    assert(engine_find_order(e, 2) == NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_market_sell\n");
}

/* =========================================================================
 * 3. MARKET-TO-LIMIT (MTL)
 * ========================================================================= */

static void test_mtl_convert_and_rest(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 51, 10, TIF_GTC) == ME_OK);
    assert(submit_mtl(e, 3, SIDE_BUY, 25, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 3, 1, 50, 10));
    assert(has_trade(&log, 3, 2, 51, 10));
    const Order *o3 = engine_find_order(e, 3);
    assert(o3 && o3->m_order_type == ORDER_TYPE_LIMIT);
    assert(o3->m_price == 50);
    assert(o3->m_remaining_qty == 5);
    assert(o3->m_status == STATUS_PARTIALLY_FILLED);
    assert(engine_best_bid(e) == 50);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_mtl_convert_and_rest\n");
}

static void test_mtl_no_liquidity(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_mtl(e, 1, SIDE_BUY, 10, TIF_GTC) == ME_OK);
    assert(has_cancel(&log, 1, CANCEL_MTL_NO_LIQUIDITY));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_mtl_no_liquidity\n");
}

static void test_mtl_full_fill_phase1(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_mtl(e, 2, SIDE_BUY, 10, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 2, 1, 50, 10));
    /* MTL fully filled — either freed or still active as LIMIT */
    assert(log.trade_count >= 1);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_mtl_full_fill_phase1\n");
}

static void test_mtl_rest_visible_to_next(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_mtl(e, 2, SIDE_BUY, 10, TIF_GTC) == ME_OK);
    const Order *o2 = engine_find_order(e, 2);
    assert(o2 && o2->m_remaining_qty == 5);
    assert(engine_best_bid(e) == 50);
    event_log_reset(&log);
    assert(submit_limit(e, 3, SIDE_SELL, 50, 3, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 3, 2, 50, 3));
    o2 = engine_find_order(e, 2);
    assert(o2 && o2->m_remaining_qty == 2);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_mtl_rest_visible_to_next\n");
}

static void test_mtl_sell_side(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 5, TIF_GTC) == ME_OK);
    assert(submit_mtl(e, 2, SIDE_SELL, 10, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 2, 1, 100, 5));
    const Order *o2 = engine_find_order(e, 2);
    assert(o2 && o2->m_price == 100);
    assert(o2->m_order_type == ORDER_TYPE_LIMIT);
    assert(engine_best_ask(e) == 100);
    assert(o2->m_remaining_qty == 5);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_mtl_sell_side\n");
}

static void test_mtl_gtd(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    OrderDesc d = {0};
    d.id=2; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET_TO_LIMIT;
    d.price=PRICE_NULL; d.stop_price=PRICE_NULL;
    d.quantity=10; d.display_qty=QTY_NULL; d.min_qty=QTY_NULL;
    d.expire_time=5000; d.tif=TIF_GTD; d.stp_policy=STP_NONE;
    assert(engine_process(e, &d) == ME_OK);
    const Order *o2 = engine_find_order(e, 2);
    assert(o2 && o2->m_remaining_qty == 5);
    assert(o2->m_status == STATUS_PARTIALLY_FILLED);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_mtl_gtd\n");
}

/* =========================================================================
 * 4. TIME IN FORCE
 * ========================================================================= */

static void test_ioc_partial(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  50, 10, TIF_IOC) == ME_OK);
    assert(has_trade(&log, 2, 1, 50, 5));
    assert(has_cancel(&log, 2, CANCEL_IOC_REMAINDER));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_ioc_partial\n");
}

static void test_ioc_full_fill(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  50, 10, TIF_IOC) == ME_OK);
    assert(engine_find_order(e, 2) == NULL); /* filled */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_ioc_full_fill\n");
}

static void test_ioc_no_match(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 50, 10, TIF_IOC) == ME_OK);
    assert(has_cancel(&log, 1, CANCEL_IOC_REMAINDER));
    assert(engine_best_bid(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_ioc_no_match\n");
}

static void test_fok_reject_insufficient(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  50, 10, TIF_FOK) == ME_OK);
    assert(has_cancel(&log, 2, CANCEL_FOK_NOT_SATISFIABLE));
    const Order *o1 = engine_find_order(e, 1);
    assert(o1 && o1->m_remaining_qty == 5);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_fok_reject_insufficient\n");
}

static void test_fok_exact_fill(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  50, 10, TIF_FOK) == ME_OK);
    assert(engine_find_order(e, 2) == NULL); /* filled */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_fok_exact_fill\n");
}

static void test_fok_across_levels(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 51, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_BUY,  51, 10, TIF_FOK) == ME_OK);
    assert(engine_find_order(e, 3) == NULL); /* filled */
    assert(has_trade(&log, 3, 1, 50, 5));
    assert(has_trade(&log, 3, 2, 51, 5));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_fok_across_levels\n");
}

static void test_fok_empty_book(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_FOK) == ME_OK);
    assert(has_cancel(&log, 1, CANCEL_FOK_NOT_SATISFIABLE));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_fok_empty_book\n");
}

static void test_gtc_rest(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_status == STATUS_NEW);
    assert(engine_best_bid(e) == 100);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_gtc_rest\n");
}

static void test_gtd_rest_and_expire(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_gtd(e, 1, SIDE_BUY, 100, 10, 1000) == ME_OK);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_status == STATUS_NEW);
    engine_expire(e, 999);
    assert(engine_find_order(e, 1) != NULL); /* still active */
    engine_expire(e, 1000);
    assert(engine_find_order(e, 1) == NULL); /* expired and freed */
    assert(engine_best_bid(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_gtd_rest_and_expire\n");
}

static void test_gtd_multiple_expire(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_gtd(e, 1, SIDE_BUY,  100, 10, 1000) == ME_OK);
    assert(submit_limit_gtd(e, 2, SIDE_SELL, 102, 10, 1000) == ME_OK);
    engine_expire(e, 1000);
    assert(engine_find_order(e, 1) == NULL);
    assert(engine_find_order(e, 2) == NULL);
    assert(engine_best_bid(e) == PRICE_NULL);
    assert(engine_best_ask(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_gtd_multiple_expire\n");
}

static void test_gtd_gtc_coexist(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit_gtd(e, 2, SIDE_BUY, 99, 10, 500) == ME_OK);
    engine_expire(e, 500);
    assert(engine_find_order(e, 1) != NULL); /* GTC stays */
    assert(engine_find_order(e, 2) == NULL); /* GTD expired */
    assert(engine_best_bid(e) == 100);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_gtd_gtc_coexist\n");
}

static void test_day_rest(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL;
    d.quantity=10; d.display_qty=QTY_NULL; d.min_qty=QTY_NULL;
    d.expire_time=TIMESTAMP_NULL; d.tif=TIF_DAY; d.stp_policy=STP_NONE;
    assert(engine_process(e, &d) == ME_OK);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_status == STATUS_NEW);
    assert(engine_best_bid(e) == 100);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_day_rest\n");
}

/* =========================================================================
 * 5. ICEBERG ORDERS
 * ========================================================================= */

static void test_iceberg_visible_qty(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_iceberg(e, 1, SIDE_BUY, 100, 100, 20, TIF_GTC) == ME_OK);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_visible_qty == 20);
    assert(o->m_remaining_qty == 100);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_iceberg_visible_qty\n");
}

static void test_iceberg_reload_after_fill(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_iceberg(e, 1, SIDE_BUY, 100, 100, 20, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 20, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 2, 1, 100, 20));
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_visible_qty == 20);
    assert(o->m_remaining_qty == 80);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_iceberg_reload_after_fill\n");
}

static void test_iceberg_priority_loss_after_reload(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_iceberg(e, 1, SIDE_BUY, 100, 100, 20, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY, 100, 50, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_SELL, 100, 20, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 3, 1, 100, 20));
    event_log_reset(&log);
    /* Iceberg reloaded -> lost priority -> order 2 gets matched first */
    assert(submit_limit(e, 4, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 4, 2, 100, 10));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_iceberg_priority_loss_after_reload\n");
}

static void test_iceberg_multiple_reloads(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_iceberg(e, 1, SIDE_BUY, 100, 60, 20, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 60, TIF_GTC) == ME_OK);
    assert(engine_find_order(e, 1) == NULL); /* fully filled */
    assert(count_type(&log, EVT_TRADE_EXECUTED) == 3);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_iceberg_multiple_reloads\n");
}

static void test_iceberg_reload_remaining_less_than_display(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_iceberg(e, 1, SIDE_BUY, 100, 30, 20, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 20, TIF_GTC) == ME_OK);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_visible_qty == 10);
    assert(o->m_remaining_qty == 10);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_iceberg_reload_remaining_less_than_display\n");
}

static void test_iceberg_full_drain(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_iceberg(e, 1, SIDE_BUY, 100, 25, 20, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 25, TIF_GTC) == ME_OK);
    assert(engine_find_order(e, 1) == NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_iceberg_full_drain\n");
}

static void test_iceberg_partial_visible_no_reload(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_iceberg(e, 1, SIDE_BUY, 100, 100, 20, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_visible_qty == 10); /* 20-10=10 */
    assert(o->m_remaining_qty == 90);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_iceberg_partial_visible_no_reload\n");
}

static void test_fok_with_iceberg(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_iceberg(e, 1, SIDE_SELL, 50, 100, 10, TIF_GTC) == ME_OK);
    /* visible=10 but remaining=100; FOK should see 100 available */
    assert(submit_limit(e, 2, SIDE_BUY, 50, 50, TIF_FOK) == ME_OK);
    assert(engine_find_order(e, 2) == NULL); /* filled */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_fok_with_iceberg\n");
}

static void test_iceberg_sell_side(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_iceberg(e, 1, SIDE_SELL, 50, 60, 15, TIF_GTC) == ME_OK);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_visible_qty == 15);
    assert(submit_limit(e, 2, SIDE_BUY, 50, 15, TIF_GTC) == ME_OK);
    o = engine_find_order(e, 1);
    assert(o && o->m_visible_qty == 15); /* reloaded */
    assert(o->m_remaining_qty == 45);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_iceberg_sell_side\n");
}

/* =========================================================================
 * 6. POST-ONLY
 * ========================================================================= */

static void test_postonly_reject_would_cross(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_post_only(e, 2, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(has_cancel(&log, 2, CANCEL_POST_ONLY_WOULD_CROSS));
    const Order *o1 = engine_find_order(e, 1);
    assert(o1 && o1->m_remaining_qty == 10);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_postonly_reject_would_cross\n");
}

static void test_postonly_rest_no_cross(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 102, 10, TIF_GTC) == ME_OK);
    assert(submit_post_only(e, 2, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    const Order *o2 = engine_find_order(e, 2);
    assert(o2 && o2->m_status == STATUS_NEW);
    assert(engine_best_bid(e) == 100);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_postonly_rest_no_cross\n");
}

static void test_postonly_sell_would_cross(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_post_only(e, 2, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(has_cancel(&log, 2, CANCEL_POST_ONLY_WOULD_CROSS));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_postonly_sell_would_cross\n");
}

static void test_postonly_sell_rest(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 98, 10, TIF_GTC) == ME_OK);
    assert(submit_post_only(e, 2, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    const Order *o2 = engine_find_order(e, 2);
    assert(o2 && o2->m_status == STATUS_NEW);
    assert(engine_best_ask(e) == 100);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_postonly_sell_rest\n");
}

static void test_postonly_empty_book(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_post_only(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_status == STATUS_NEW);
    assert(engine_best_bid(e) == 100);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_postonly_empty_book\n");
}

/* =========================================================================
 * 7. MINQTY
 * ========================================================================= */

static void test_minqty_reject_insufficient(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 3, TIF_GTC) == ME_OK);
    assert(submit_min_qty(e, 2, SIDE_BUY, 50, 10, 5, TIF_GTC) == ME_OK);
    assert(has_cancel(&log, 2, CANCEL_MIN_QTY));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_minqty_reject_insufficient\n");
}

static void test_minqty_exact_threshold(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_min_qty(e, 2, SIDE_BUY, 50, 10, 5, TIF_GTC) == ME_OK);
    const Order *o2 = engine_find_order(e, 2);
    assert(o2 && o2->m_status == STATUS_PARTIALLY_FILLED);
    assert(o2->m_min_qty == QTY_NULL); /* cleared */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_minqty_exact_threshold\n");
}

static void test_minqty_cleared_after_fill(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_min_qty(e, 2, SIDE_BUY, 50, 20, 5, TIF_GTC) == ME_OK);
    const Order *o2 = engine_find_order(e, 2);
    assert(o2 && o2->m_min_qty == QTY_NULL);
    assert(o2->m_remaining_qty == 10);
    assert(o2->m_status == STATUS_PARTIALLY_FILLED);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_minqty_cleared_after_fill\n");
}

static void test_minqty_resting_has_no_constraint(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_min_qty(e, 2, SIDE_BUY, 50, 20, 5, TIF_GTC) == ME_OK);
    event_log_reset(&log);
    /* Order 2 resting with minQty cleared; fill 1 unit (< original minQty) */
    assert(submit_limit(e, 3, SIDE_SELL, 50, 1, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 3, 2, 50, 1));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_minqty_resting_has_no_constraint\n");
}

/* =========================================================================
 * 8. STP (SELF-TRADE PREVENTION)
 * ========================================================================= */

static void test_stp_cancel_newest(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 10, TIF_GTC, 1, STP_CANCEL_NEWEST) == ME_OK);
    assert(submit_limit_stp(e, 2, SIDE_BUY,  50, 10, TIF_GTC, 1, STP_CANCEL_NEWEST) == ME_OK);
    assert(has_cancel(&log, 2, CANCEL_STP_NEWEST));
    assert(engine_find_order(e, 1) != NULL);
    assert(log.trade_count == 0);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_cancel_newest\n");
}

static void test_stp_cancel_oldest(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 10, TIF_GTC, 1, STP_CANCEL_OLDEST) == ME_OK);
    assert(submit_limit_stp(e, 2, SIDE_BUY,  50, 10, TIF_GTC, 1, STP_CANCEL_OLDEST) == ME_OK);
    assert(has_cancel(&log, 1, CANCEL_STP_OLDEST));
    assert(engine_find_order(e, 1) == NULL);
    const Order *o2 = engine_find_order(e, 2);
    assert(o2 && o2->m_status == STATUS_NEW);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_cancel_oldest\n");
}

static void test_stp_cancel_both(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 10, TIF_GTC, 1, STP_CANCEL_BOTH) == ME_OK);
    assert(submit_limit_stp(e, 2, SIDE_BUY,  50, 10, TIF_GTC, 1, STP_CANCEL_BOTH) == ME_OK);
    assert(engine_find_order(e, 1) == NULL);
    assert(engine_find_order(e, 2) == NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_cancel_both\n");
}

static void test_stp_decrement(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 10, TIF_GTC, 1, STP_DECREMENT) == ME_OK);
    assert(submit_limit_stp(e, 2, SIDE_BUY,  50, 7,  TIF_GTC, 1, STP_DECREMENT) == ME_OK);
    const Order *o1 = engine_find_order(e, 1);
    assert(o1 && o1->m_remaining_qty == 3);
    assert(engine_find_order(e, 2) == NULL); /* incoming cancelled */
    assert(log.trade_count == 0);
    assert(has_decrement(&log, 2, 1, 7));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_decrement\n");
}

static void test_stp_decrement_resting_to_zero(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 5,  TIF_GTC, 1, STP_DECREMENT) == ME_OK);
    assert(submit_limit_stp(e, 2, SIDE_BUY,  50, 10, TIF_GTC, 1, STP_DECREMENT) == ME_OK);
    /* resting=5, incoming=10: min=5, resting goes to 0 (cancelled), incoming goes to 5, rests */
    assert(engine_find_order(e, 1) == NULL);
    const Order *o2 = engine_find_order(e, 2);
    assert(o2 && o2->m_remaining_qty == 5);
    assert(o2->m_status == STATUS_NEW);
    assert(engine_best_bid(e) == 50);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_decrement_resting_to_zero\n");
}

static void test_stp_cancel_oldest_continues_to_non_stp(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 10, TIF_GTC, 1, STP_CANCEL_OLDEST) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK); /* no STP group */
    assert(submit_limit_stp(e, 3, SIDE_BUY, 50, 10, TIF_GTC, 1, STP_CANCEL_OLDEST) == ME_OK);
    assert(engine_find_order(e, 1) == NULL);
    assert(has_trade(&log, 3, 2, 50, 10));
    assert(engine_find_order(e, 3) == NULL); /* filled */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_cancel_oldest_continues_to_non_stp\n");
}

static void test_stp_cancel_oldest_multiple_same_group(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 5, TIF_GTC, 1, STP_CANCEL_OLDEST) == ME_OK);
    assert(submit_limit_stp(e, 2, SIDE_SELL, 50, 5, TIF_GTC, 1, STP_CANCEL_OLDEST) == ME_OK);
    assert(submit_limit_stp(e, 3, SIDE_BUY,  50, 10, TIF_GTC, 1, STP_CANCEL_OLDEST) == ME_OK);
    assert(engine_find_order(e, 1) == NULL);
    assert(engine_find_order(e, 2) == NULL);
    const Order *o3 = engine_find_order(e, 3);
    assert(o3 && o3->m_status == STATUS_NEW);
    assert(log.trade_count == 0);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_cancel_oldest_multiple_same_group\n");
}

static void test_stp_incoming_policy_governs(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 10, TIF_GTC, 1, STP_CANCEL_OLDEST) == ME_OK);
    assert(submit_limit_stp(e, 2, SIDE_BUY,  50, 10, TIF_GTC, 1, STP_CANCEL_NEWEST) == ME_OK);
    /* Incoming policy=CANCEL_NEWEST -> incoming (2) gets cancelled */
    assert(has_cancel(&log, 2, CANCEL_STP_NEWEST));
    const Order *o1 = engine_find_order(e, 1);
    assert(o1 && o1->m_status == STATUS_NEW);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_incoming_policy_governs\n");
}

static void test_stp_different_groups_no_conflict(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 10, TIF_GTC, 1, STP_CANCEL_NEWEST) == ME_OK);
    assert(submit_limit_stp(e, 2, SIDE_BUY,  50, 10, TIF_GTC, 2, STP_CANCEL_NEWEST) == ME_OK);
    assert(has_trade(&log, 2, 1, 50, 10));
    assert(engine_find_order(e, 1) == NULL);
    assert(engine_find_order(e, 2) == NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_different_groups_no_conflict\n");
}

static void test_stp_no_group_no_conflict(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK); /* no STP */
    assert(submit_limit_stp(e, 2, SIDE_BUY, 50, 10, TIF_GTC, 1, STP_CANCEL_NEWEST) == ME_OK);
    assert(has_trade(&log, 2, 1, 50, 10));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_no_group_no_conflict\n");
}

static void test_stp_across_price_levels(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 5,  TIF_GTC, 1, STP_CANCEL_OLDEST) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 51, 10, TIF_GTC) == ME_OK); /* no STP */
    assert(submit_limit_stp(e, 3, SIDE_BUY, 51, 10, TIF_GTC, 1, STP_CANCEL_OLDEST) == ME_OK);
    assert(engine_find_order(e, 1) == NULL);
    assert(has_trade(&log, 3, 2, 51, 10));
    assert(engine_find_order(e, 3) == NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_across_price_levels\n");
}

static void test_stp_market_with_stp(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 10, TIF_GTC, 1, STP_CANCEL_NEWEST) == ME_OK);
    /* Market BUY with same STP group */
    OrderDesc d = {0};
    d.id=2; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET;
    d.price=PRICE_NULL; d.stop_price=PRICE_NULL;
    d.quantity=10; d.display_qty=QTY_NULL; d.min_qty=QTY_NULL;
    d.expire_time=TIMESTAMP_NULL; d.tif=TIF_IOC;
    d.stp_group=1; d.stp_policy=STP_CANCEL_NEWEST;
    assert(engine_process(e, &d) == ME_OK);
    assert(has_cancel(&log, 2, CANCEL_STP_NEWEST));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_market_with_stp\n");
}

/* =========================================================================
 * 9. STOP ORDERS
 * ========================================================================= */

static void test_stop_limit_immediate_buy(void) {
    /* This engine triggers stops only after a trade, not on submission.
     * We submit the stop first, then trigger it via a trade at or above stop_price. */
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    /* Resting ask for triggered stop to match */
    assert(submit_limit(e, 4, SIDE_SELL, 61, 10, TIF_GTC) == ME_OK);
    /* Buy stop limit: stop=50, limit=61 */
    assert(submit_stop_limit(e, 3, SIDE_BUY, 61, 50, 10, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 1);
    /* Trade at 60 >= 50 -> triggers stop */
    assert(submit_limit(e, 1, SIDE_SELL, 60, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  60, 5, TIF_GTC) == ME_OK);
    assert(log.trigger_count >= 1);
    const Order *o3 = engine_find_order(e, 3);
    if (o3) assert(o3->m_order_type == ORDER_TYPE_LIMIT);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stop_limit_immediate_buy\n");
}

static void test_stop_limit_immediate_sell(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    /* Resting bid for triggered sell stop to match */
    assert(submit_limit(e, 4, SIDE_BUY, 99, 10, TIF_GTC) == ME_OK);
    /* Sell stop limit: stop=110, limit=99 */
    assert(submit_stop_limit(e, 3, SIDE_SELL, 99, 110, 10, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 1);
    /* Trade at 100 <= 110 -> triggers */
    assert(submit_limit(e, 1, SIDE_SELL, 100, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  100, 5, TIF_GTC) == ME_OK);
    assert(log.trigger_count >= 1);
    const Order *o3 = engine_find_order(e, 3);
    if (o3) assert(o3->m_order_type == ORDER_TYPE_LIMIT);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stop_limit_immediate_sell\n");
}

static void test_stop_rests_when_not_triggered(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    /* no trades yet -> lastTradePrice=0 -> buy stop at 50 not triggered */
    assert(submit_stop_limit(e, 1, SIDE_BUY, 51, 50, 10, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 1);
    assert(engine_best_bid(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stop_rests_when_not_triggered\n");
}

static void test_stop_no_trigger_no_trades(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_stop_limit(e, 1, SIDE_BUY, 51, 50, 10, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 1);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stop_no_trigger_no_trades\n");
}

static void test_stop_triggered_by_trade(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_stop_limit(e, 1, SIDE_BUY, 51, 50, 10, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 1);
    /* resting ask for triggered stop to match */
    assert(submit_limit(e, 2, SIDE_SELL, 51, 10, TIF_GTC) == ME_OK);
    /* trade at 50 triggers stop */
    assert(submit_limit(e, 3, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 4, SIDE_BUY,  50, 5, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 0);
    const Order *o1 = engine_find_order(e, 1);
    if (o1) assert(o1->m_order_type == ORDER_TYPE_LIMIT);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stop_triggered_by_trade\n");
}

static void test_sell_stop_triggered(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_stop_limit(e, 1, SIDE_SELL, 99, 100, 10, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 1);
    assert(submit_limit(e, 2, SIDE_BUY, 99, 10, TIF_GTC) == ME_OK);
    /* trade at 100 -> lastTrade=100 <= 100 -> trigger */
    assert(submit_limit(e, 3, SIDE_SELL, 100, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 4, SIDE_BUY,  100, 5, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 0);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_sell_stop_triggered\n");
}

static void test_sell_stop_not_triggered(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_stop_limit(e, 1, SIDE_SELL, 89, 90, 10, TIF_GTC) == ME_OK);
    /* trade at 91: 91 <= 90 is false -> no trigger */
    assert(submit_limit(e, 2, SIDE_SELL, 91, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_BUY,  91, 5, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 1);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_sell_stop_not_triggered\n");
}

static void test_stop_market_immediate(void) {
    /* Engine triggers stops after trades only. Submit stop first, then
     * create a trade at or above stop_price to trigger it. */
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    /* Resting ask for triggered stop market to consume */
    assert(submit_limit(e, 3, SIDE_SELL, 101, 10, TIF_GTC) == ME_OK);
    /* Buy stop market: stop=100 */
    assert(submit_stop_market(e, 4, SIDE_BUY, 100, 5, TIF_IOC) == ME_OK);
    assert(e->m_book.m_stop_count == 1);
    /* Trade at 100 (>= stop=100) triggers stop */
    assert(submit_limit(e, 1, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    assert(log.trigger_count >= 1);
    assert(has_trade(&log, 4, 3, 101, 5));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stop_market_immediate\n");
}

static void test_sell_stop_market(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    /* Resting bid for triggered sell stop market to consume */
    assert(submit_limit(e, 3, SIDE_BUY, 99, 10, TIF_GTC) == ME_OK);
    /* Sell stop market: stop=110 */
    assert(submit_stop_market(e, 4, SIDE_SELL, 110, 5, TIF_IOC) == ME_OK);
    assert(e->m_book.m_stop_count == 1);
    /* Trade at 100 (<= stop=110) triggers stop */
    assert(submit_limit(e, 1, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 4, 3, 99, 5));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_sell_stop_market\n");
}

static void test_multiple_stops_triggered_by_one_trade(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_stop_limit(e, 1, SIDE_BUY, 101, 50,  5, TIF_GTC) == ME_OK);
    assert(submit_stop_limit(e, 2, SIDE_BUY, 101, 60,  5, TIF_GTC) == ME_OK);
    assert(submit_stop_limit(e, 3, SIDE_BUY, 101, 70,  5, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 3);
    assert(submit_limit(e, 4, SIDE_SELL, 101, 20, TIF_GTC) == ME_OK);
    /* trade at 70 -> triggers all 3 */
    assert(submit_limit(e, 5, SIDE_SELL, 70, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 6, SIDE_BUY,  70, 5, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 0);
    assert(log.trigger_count == 3);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_multiple_stops_triggered_by_one_trade\n");
}

static void test_stop_fifo_order(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_stop_limit(e, 1, SIDE_BUY, 200, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_stop_limit(e, 2, SIDE_BUY, 200, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_SELL, 200, 20, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 4, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 5, SIDE_BUY,  50, 5, TIF_GTC) == ME_OK);
    /* Both triggered; check FIFO: order 1 triggered before order 2 */
    const RecordedEvent *t0 = nth_event_of_type(&log, EVT_ORDER_TRIGGERED, 0);
    const RecordedEvent *t1 = nth_event_of_type(&log, EVT_ORDER_TRIGGERED, 1);
    assert(t0 && t1);
    assert(t0->triggered_id == 1);
    assert(t1->triggered_id == 2);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stop_fifo_order\n");
}

static void test_stop_cascade_triggers_another(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    /* lastTradePrice=100 */
    assert(submit_limit(e, 3, SIDE_BUY, 89, 10, TIF_GTC) == ME_OK);
    assert(submit_stop_limit(e, 4, SIDE_SELL, 89, 90, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 5, SIDE_BUY, 88, 10, TIF_GTC) == ME_OK);
    assert(submit_stop_limit(e, 6, SIDE_SELL, 88, 89, 5, TIF_GTC) == ME_OK);
    /* trade at 90 triggers stop 4 (89<=90->yes), stop4 trades at 89 triggers stop 6 */
    assert(submit_limit(e, 7, SIDE_SELL, 90, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 8, SIDE_BUY,  90, 5, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 0);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stop_cascade_triggers_another\n");
}

static void test_cancel_stop_order(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_stop_limit(e, 1, SIDE_BUY, 51, 50, 10, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 1);
    assert(engine_cancel(e, 1) == ME_OK);
    assert(has_cancel(&log, 1, CANCEL_USER_REQUESTED));
    assert(e->m_book.m_stop_count == 0);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_cancel_stop_order\n");
}

static void test_stop_converts_to_limit_and_matches(void) {
    /* Engine triggers stops after trades only. Set up stop first, then
     * trigger via a trade, verifying the stop converts and matches. */
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    /* Resting ask for the triggered stop to match */
    assert(submit_limit(e, 3, SIDE_SELL, 55, 10, TIF_GTC) == ME_OK);
    /* Buy stop: stop=50, limit=55 */
    assert(submit_stop_limit(e, 4, SIDE_BUY, 55, 50, 5, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 1);
    /* Trade at 50 (>= stop_price=50) triggers stop */
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  50, 10, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 0);
    assert(has_trade(&log, 4, 3, 55, 5));
    assert(engine_find_order(e, 4) == NULL); /* filled */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stop_converts_to_limit_and_matches\n");
}

static void test_stop_converts_and_rests(void) {
    /* Buy stop: stop=50, limit=45 -> triggers when trade at 50, converts to LIMIT@45,
     * no asks at 45 -> rests. */
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    /* Buy stop: stop=50, limit=45 */
    assert(submit_stop_limit(e, 3, SIDE_BUY, 45, 50, 10, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 1);
    /* Trade at 50 triggers the stop */
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  50, 10, TIF_GTC) == ME_OK);
    assert(e->m_book.m_stop_count == 0);
    const Order *o3 = engine_find_order(e, 3);
    assert(o3 && o3->m_status == STATUS_NEW);
    assert(o3->m_order_type == ORDER_TYPE_LIMIT);
    assert(engine_best_bid(e) == 45);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stop_converts_and_rests\n");
}

/* =========================================================================
 * 10. CANCEL OPERATIONS
 * ========================================================================= */

static void test_cancel_resting(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(engine_cancel(e, 1) == ME_OK);
    assert(has_cancel(&log, 1, CANCEL_USER_REQUESTED));
    assert(engine_best_bid(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_cancel_resting\n");
}

static void test_cancel_already_filled(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    /* order 1 is filled, engine_find_order returns NULL */
    assert(engine_find_order(e, 1) == NULL);
    int before = log.count;
    ME_Result r = engine_cancel(e, 1);
    /* cancel of non-existent -> ME_ERR_NOT_FOUND, no new event */
    assert(r == ME_ERR_NOT_FOUND);
    assert(log.count == before);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_cancel_already_filled\n");
}

static void test_cancel_already_cancelled(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(engine_cancel(e, 1) == ME_OK);
    int before = log.count;
    ME_Result r = engine_cancel(e, 1);
    assert(r == ME_ERR_NOT_FOUND);
    assert(log.count == before);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_cancel_already_cancelled\n");
}

static void test_cancel_nonexistent(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    ME_Result r = engine_cancel(e, 999);
    assert(r == ME_ERR_NOT_FOUND);
    assert(log.count == 0);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_cancel_nonexistent\n");
}

static void test_cancel_middle_of_level(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(engine_cancel(e, 2) == ME_OK);
    assert(has_cancel(&log, 2, CANCEL_USER_REQUESTED));
    assert(engine_best_bid(e) == 100);
    event_log_reset(&log);
    assert(submit_limit(e, 4, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 4, 1, 100, 10)); /* FIFO: order 1 first */
    event_log_reset(&log);
    assert(submit_limit(e, 5, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 5, 3, 100, 10)); /* order 3 next */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_cancel_middle_of_level\n");
}

static void test_cancel_last_at_level(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  99, 10, TIF_GTC) == ME_OK);
    assert(engine_cancel(e, 1) == ME_OK);
    assert(engine_best_bid(e) == 99);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_cancel_last_at_level\n");
}

static void test_cancel_partially_filled(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 20, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    const Order *o1 = engine_find_order(e, 1);
    assert(o1 && o1->m_status == STATUS_PARTIALLY_FILLED);
    assert(engine_cancel(e, 1) == ME_OK);
    assert(has_cancel(&log, 1, CANCEL_USER_REQUESTED));
    assert(engine_find_order(e, 1) == NULL);
    assert(engine_best_bid(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_cancel_partially_filled\n");
}

/* =========================================================================
 * 11. AMEND OPERATIONS
 * ========================================================================= */

static void test_amend_qty_decrease_keeps_priority(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    Timestamp ts = engine_find_order(e, 1)->m_timestamp;
    AmendDesc a = { 1, PRICE_NULL, 5 };
    assert(engine_amend(e, &a) == ME_OK);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_remaining_qty == 5);
    assert(o->m_timestamp == ts); /* priority kept */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_amend_qty_decrease_keeps_priority\n");
}

static void test_amend_price_loses_priority(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    Timestamp ts2 = engine_find_order(e, 2)->m_timestamp;
    AmendDesc a = { 1, 101, QTY_NULL };
    assert(engine_amend(e, &a) == ME_OK);
    const Order *o1 = engine_find_order(e, 1);
    assert(o1 && o1->m_price == 101);
    assert(o1->m_timestamp > ts2); /* loses priority */
    assert(engine_best_bid(e) == 101);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_amend_price_loses_priority\n");
}

static void test_amend_qty_increase_loses_priority(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    Timestamp ts2 = engine_find_order(e, 2)->m_timestamp;
    AmendDesc a = { 1, PRICE_NULL, 20 };
    assert(engine_amend(e, &a) == ME_OK);
    const Order *o1 = engine_find_order(e, 1);
    assert(o1 && o1->m_remaining_qty == 20);
    assert(o1->m_timestamp > ts2);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_amend_qty_increase_loses_priority\n");
}

static void test_amend_crosses_spread(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,  48, 10, TIF_GTC) == ME_OK);
    event_log_reset(&log);
    AmendDesc a = { 2, 50, QTY_NULL };
    assert(engine_amend(e, &a) == ME_OK);
    assert(has_trade(&log, 2, 1, 50, 10));
    assert(engine_find_order(e, 1) == NULL);
    assert(engine_find_order(e, 2) == NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_amend_crosses_spread\n");
}

static void test_amend_nonexistent(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    AmendDesc a = { 999, 100, 10 };
    ME_Result r = engine_amend(e, &a);
    assert(r == ME_ERR_NOT_FOUND);
    assert(log.count == 0);
    free_engine(e);
    printf("PASS: test_amend_nonexistent\n");
}

static void test_amend_filled_order(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    int before = log.count;
    AmendDesc a = { 1, 101, QTY_NULL };
    ME_Result r = engine_amend(e, &a);
    assert(r == ME_ERR_NOT_FOUND);
    assert(log.count == before);
    free_engine(e);
    printf("PASS: test_amend_filled_order\n");
}

static void test_amend_same_price_same_qty(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    Timestamp ts = engine_find_order(e, 1)->m_timestamp;
    AmendDesc a = { 1, 100, 10 };
    assert(engine_amend(e, &a) == ME_OK);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_timestamp == ts);
    assert(o->m_remaining_qty == 10);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_amend_same_price_same_qty\n");
}

static void test_amend_iceberg_qty_decrease(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_iceberg(e, 1, SIDE_BUY, 100, 50, 10, TIF_GTC) == ME_OK);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_visible_qty == 10);
    AmendDesc a = { 1, PRICE_NULL, 5 };
    assert(engine_amend(e, &a) == ME_OK);
    o = engine_find_order(e, 1);
    assert(o && o->m_remaining_qty == 5);
    assert(o->m_visible_qty == 5); /* min(display=10, remaining=5) */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_amend_iceberg_qty_decrease\n");
}

/* =========================================================================
 * 12. VALIDATION (WF checks)
 * ========================================================================= */

static void test_wf1_zero_qty(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=0;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF1));
    free_engine(e);
    printf("PASS: test_wf1_zero_qty\n");
}

static void test_wf2_limit_no_price(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=0; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF2));
    free_engine(e);
    printf("PASS: test_wf2_limit_no_price\n");
}

static void test_wf2a_stop_limit_no_price(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_STOP_LIMIT;
    d.price=0; d.stop_price=50; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF2A));
    free_engine(e);
    printf("PASS: test_wf2a_stop_limit_no_price\n");
}

static void test_wf2b_mtl_with_price(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET_TO_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF2B));
    free_engine(e);
    printf("PASS: test_wf2b_mtl_with_price\n");
}

static void test_wf3_market_with_price(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_IOC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF3));
    free_engine(e);
    printf("PASS: test_wf3_market_with_price\n");
}

static void test_wf3_stop_market_with_price(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_STOP_MARKET;
    d.price=100; d.stop_price=50; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_IOC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF3));
    free_engine(e);
    printf("PASS: test_wf3_stop_market_with_price\n");
}

static void test_wf4_stop_limit_no_stop_price(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_STOP_LIMIT;
    d.price=50; d.stop_price=0; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF4));
    free_engine(e);
    printf("PASS: test_wf4_stop_limit_no_stop_price\n");
}

static void test_wf4_stop_market_no_stop_price(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_STOP_MARKET;
    d.price=PRICE_NULL; d.stop_price=0; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_IOC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF4));
    free_engine(e);
    printf("PASS: test_wf4_stop_market_no_stop_price\n");
}

static void test_wf5_limit_with_stop_price(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=50; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF5));
    free_engine(e);
    printf("PASS: test_wf5_limit_with_stop_price\n");
}

static void test_wf5_market_with_stop_price(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET;
    d.price=PRICE_NULL; d.stop_price=50; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_IOC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF5));
    free_engine(e);
    printf("PASS: test_wf5_market_with_stop_price\n");
}

static void test_wf5_mtl_with_stop_price(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET_TO_LIMIT;
    d.price=PRICE_NULL; d.stop_price=50; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF5));
    free_engine(e);
    printf("PASS: test_wf5_mtl_with_stop_price\n");
}

static void test_wf6_gtd_no_expire(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTD; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF6));
    free_engine(e);
    printf("PASS: test_wf6_gtd_no_expire\n");
}

static void test_wf7_non_gtd_with_expire(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=1000;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF7));
    free_engine(e);
    printf("PASS: test_wf7_non_gtd_with_expire\n");
}

static void test_wf8_market_gtc(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET;
    d.price=PRICE_NULL; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF8));
    free_engine(e);
    printf("PASS: test_wf8_market_gtc\n");
}

static void test_wf8_market_gtd(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET;
    d.price=PRICE_NULL; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=1000;
    d.tif=TIF_GTD; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF8));
    free_engine(e);
    printf("PASS: test_wf8_market_gtd\n");
}

static void test_wf8a_mtl_ioc(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET_TO_LIMIT;
    d.price=PRICE_NULL; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_IOC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF8A));
    free_engine(e);
    printf("PASS: test_wf8a_mtl_ioc\n");
}

static void test_wf8a_mtl_fok(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET_TO_LIMIT;
    d.price=PRICE_NULL; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_FOK; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF8A));
    free_engine(e);
    printf("PASS: test_wf8a_mtl_fok\n");
}

static void test_wf9_display_gt_qty(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=20; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF9));
    free_engine(e);
    printf("PASS: test_wf9_display_gt_qty\n");
}

static void test_wf10_iceberg_on_market(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET;
    d.price=PRICE_NULL; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=5; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_IOC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF10));
    free_engine(e);
    printf("PASS: test_wf10_iceberg_on_market\n");
}

static void test_wf13_postonly_on_market(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET;
    d.price=PRICE_NULL; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_IOC; d.stp_policy=STP_NONE; d.post_only=1;
    engine_process(e, &d);
    assert(log.reject_count == 1);
    free_engine(e);
    printf("PASS: test_wf13_postonly_on_market\n");
}

static void test_wf14_postonly_ioc(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_IOC; d.stp_policy=STP_NONE; d.post_only=1;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF14));
    free_engine(e);
    printf("PASS: test_wf14_postonly_ioc\n");
}

static void test_wf14_postonly_fok(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_FOK; d.stp_policy=STP_NONE; d.post_only=1;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF14));
    free_engine(e);
    printf("PASS: test_wf14_postonly_fok\n");
}

static void test_wf15_mtl_postonly(void) {
    /* MTL + post_only is invalid; WF-13 or WF-15 both reject it */
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_MARKET_TO_LIMIT;
    d.price=PRICE_NULL; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE; d.post_only=1;
    engine_process(e, &d);
    assert(log.reject_count == 1 && log.events[0].order_id == 1);
    free_engine(e);
    printf("PASS: test_wf15_mtl_postonly\n");
}

static void test_wf16_group_without_policy(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_group=1; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF16));
    free_engine(e);
    printf("PASS: test_wf16_group_without_policy\n");
}

static void test_wf16_policy_without_group(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=QTY_NULL; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_group=0; d.stp_policy=STP_CANCEL_NEWEST;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF16));
    free_engine(e);
    printf("PASS: test_wf16_policy_without_group\n");
}

static void test_wf18_minqty_gt_qty(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=20; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF18));
    free_engine(e);
    printf("PASS: test_wf18_minqty_gt_qty\n");
}

static void test_wf19_minqty_with_postonly(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=5; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_GTC; d.stp_policy=STP_NONE; d.post_only=1;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF19));
    free_engine(e);
    printf("PASS: test_wf19_minqty_with_postonly\n");
}

static void test_wf20_fok_with_minqty(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc d = {0};
    d.id=1; d.side=SIDE_BUY; d.order_type=ORDER_TYPE_LIMIT;
    d.price=100; d.stop_price=PRICE_NULL; d.quantity=10;
    d.display_qty=QTY_NULL; d.min_qty=5; d.expire_time=TIMESTAMP_NULL;
    d.tif=TIF_FOK; d.stp_policy=STP_NONE;
    engine_process(e, &d);
    assert(has_reject(&log, 1, REJECT_WF20));
    free_engine(e);
    printf("PASS: test_wf20_fok_with_minqty\n");
}

/* =========================================================================
 * 13. INVARIANTS
 * ========================================================================= */

static void test_inv_uncrossed_book(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,   99, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_SELL, 102, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 4, SIDE_SELL, 103, 10, TIF_GTC) == ME_OK);
    Price bid = engine_best_bid(e);
    Price ask = engine_best_ask(e);
    assert(bid < ask);
    assert(submit_limit(e, 5, SIDE_SELL, 99, 5, TIF_GTC) == ME_OK);
    bid = engine_best_bid(e);
    ask = engine_best_ask(e);
    assert(bid == PRICE_NULL || ask == PRICE_NULL || bid < ask);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_inv_uncrossed_book\n");
}

static void test_inv_no_ghosts_on_book(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(engine_best_bid(e) == PRICE_NULL);
    assert(engine_best_ask(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_inv_no_ghosts_on_book\n");
}

static void test_inv_no_market_on_book(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_market(e, 1, SIDE_BUY, 10, TIF_IOC) == ME_OK);
    assert(engine_best_bid(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_inv_no_market_on_book\n");
}

static void test_inv_no_mtl_on_book(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_mtl(e, 2, SIDE_BUY, 10, TIF_GTC) == ME_OK);
    const Order *o2 = engine_find_order(e, 2);
    assert(o2 && o2->m_order_type == ORDER_TYPE_LIMIT);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_inv_no_mtl_on_book\n");
}

static void test_inv_minqty_cleared_on_book(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    assert(submit_min_qty(e, 2, SIDE_BUY, 50, 20, 5, TIF_GTC) == ME_OK);
    const Order *o2 = engine_find_order(e, 2);
    assert(o2 && o2->m_min_qty == QTY_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_inv_minqty_cleared_on_book\n");
}

static void test_inv_passive_price_rule(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  105, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL,  95, 10, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 2, 1, 105, 10));
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_inv_passive_price_rule\n");
}

static void test_inv_stp_no_self_trade(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 10, TIF_GTC, 1, STP_CANCEL_BOTH) == ME_OK);
    assert(submit_limit_stp(e, 2, SIDE_BUY,  50, 10, TIF_GTC, 1, STP_CANCEL_BOTH) == ME_OK);
    assert(log.trade_count == 0);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_inv_stp_no_self_trade\n");
}

/* =========================================================================
 * 14. EVENT ORDERING
 * ========================================================================= */

static void test_event_order_accept_then_trade(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK);
    event_log_reset(&log);
    assert(submit_limit(e, 2, SIDE_BUY, 50, 10, TIF_GTC) == ME_OK);
    assert(log.count >= 2);
    assert(log.events[0].type == EVT_ORDER_ACCEPTED);
    assert(log.events[0].order_id == 2);
    assert(log.events[1].type == EVT_TRADE_EXECUTED);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_event_order_accept_then_trade\n");
}

static void test_event_trades_best_price_first(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_SELL, 50, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 51, 5, TIF_GTC) == ME_OK);
    event_log_reset(&log);
    assert(submit_limit(e, 3, SIDE_BUY, 51, 10, TIF_GTC) == ME_OK);
    const RecordedEvent *t0 = nth_event_of_type(&log, EVT_TRADE_EXECUTED, 0);
    const RecordedEvent *t1 = nth_event_of_type(&log, EVT_TRADE_EXECUTED, 1);
    assert(t0 && t1);
    assert(t0->trade_price == 50);
    assert(t1->trade_price == 51);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_event_trades_best_price_first\n");
}

/* =========================================================================
 * 15. APPENDIX B
 * ========================================================================= */

static void test_appendix_b(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);

    assert(submit_limit(e, 1, SIDE_BUY, 1000, 100, TIF_GTC) == ME_OK);
    assert(engine_best_bid(e) == 1000);

    assert(submit_limit(e, 2, SIDE_BUY, 1000,  50, TIF_GTC) == ME_OK);

    assert(submit_limit(e, 3, SIDE_BUY, 1005,  75, TIF_GTC) == ME_OK);
    assert(engine_best_bid(e) == 1005);

    event_log_reset(&log);
    assert(submit_limit(e, 4, SIDE_SELL, 995, 30, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 4, 3, 1005, 30));
    const Order *o3 = engine_find_order(e, 3);
    assert(o3 && o3->m_remaining_qty == 45);
    assert(engine_find_order(e, 4) == NULL); /* filled */

    event_log_reset(&log);
    assert(submit_market(e, 5, SIDE_SELL, 200, TIF_IOC) == ME_OK);
    assert(has_trade(&log, 5, 3, 1005, 45));
    assert(has_trade(&log, 5, 1, 1000, 100));
    assert(has_trade(&log, 5, 2, 1000, 50));
    assert(has_cancel(&log, 5, CANCEL_IOC_REMAINDER));
    assert(engine_best_bid(e) == PRICE_NULL);
    assert(engine_best_ask(e) == PRICE_NULL);

    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_appendix_b\n");
}

/* =========================================================================
 * 16. COMPLEX / EDGE CASE SCENARIOS
 * ========================================================================= */

static void test_many_levels_ascending_asks(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    for (OrderId i = 1; i <= 10; i++)
        assert(submit_limit(e, i, SIDE_SELL, 100 + i, 5, TIF_GTC) == ME_OK);
    assert(engine_best_ask(e) == 101);
    assert(submit_limit(e, 11, SIDE_BUY, 103, 15, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 11, 1, 101, 5));
    assert(has_trade(&log, 11, 2, 102, 5));
    assert(has_trade(&log, 11, 3, 103, 5));
    assert(engine_find_order(e, 11) == NULL); /* filled */
    assert(engine_best_ask(e) == 104);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_many_levels_ascending_asks\n");
}

static void test_many_levels_descending_bids(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    for (OrderId i = 1; i <= 10; i++)
        assert(submit_limit(e, i, SIDE_BUY, 110 - i, 5, TIF_GTC) == ME_OK);
    assert(engine_best_bid(e) == 109);
    assert(submit_limit(e, 11, SIDE_SELL, 107, 15, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 11, 1, 109, 5));
    assert(has_trade(&log, 11, 2, 108, 5));
    assert(has_trade(&log, 11, 3, 107, 5));
    assert(engine_best_bid(e) == 106);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_many_levels_descending_bids\n");
}

static void test_cancel_then_resubmit_same_id(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(engine_cancel(e, 1) == ME_OK);
    assert(engine_find_order(e, 1) == NULL);
    /* Re-submit with same ID */
    assert(submit_limit(e, 1, SIDE_BUY, 101, 20, TIF_GTC) == ME_OK);
    const Order *o = engine_find_order(e, 1);
    assert(o && o->m_status == STATUS_NEW);
    assert(o->m_price == 101);
    assert(engine_best_bid(e) == 101);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_cancel_then_resubmit_same_id\n");
}

static void test_iceberg_with_multiple_aggressors(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_iceberg(e, 1, SIDE_BUY, 100, 50, 10, TIF_GTC) == ME_OK);
    for (OrderId i = 2; i <= 6; i++)
        assert(submit_limit(e, i, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(engine_find_order(e, 1) == NULL); /* fully consumed */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_iceberg_with_multiple_aggressors\n");
}

static void test_partial_fill_then_expire(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_gtd(e, 1, SIDE_BUY, 100, 20, 1000) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    const Order *o1 = engine_find_order(e, 1);
    assert(o1 && o1->m_status == STATUS_PARTIALLY_FILLED);
    assert(o1->m_remaining_qty == 10);
    engine_expire(e, 1000);
    assert(engine_find_order(e, 1) == NULL);
    assert(engine_best_bid(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_partial_fill_then_expire\n");
}

static void test_rapid_insert_cancel_sequence(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    for (OrderId i = 1; i <= 100; i++)
        assert(submit_limit(e, i, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    for (OrderId i = 1; i <= 100; i++)
        assert(engine_cancel(e, i) == ME_OK);
    assert(engine_best_bid(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_rapid_insert_cancel_sequence\n");
}

static void test_amend_and_match_sequence(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 102, 10, TIF_GTC) == ME_OK);
    { AmendDesc a = {1, PRICE_NULL, 5}; assert(engine_amend(e, &a) == ME_OK); }
    { AmendDesc a = {2, 101, QTY_NULL}; assert(engine_amend(e, &a) == ME_OK); }
    assert(engine_best_bid(e) == 100);
    assert(engine_best_ask(e) == 101);
    event_log_reset(&log);
    assert(submit_limit(e, 3, SIDE_SELL, 100, 5, TIF_GTC) == ME_OK);
    assert(has_trade(&log, 3, 1, 100, 5));
    assert(engine_find_order(e, 1) == NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_amend_and_match_sequence\n");
}

static void test_book_depth_after_operations(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY,   99, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_BUY,   98, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 4, SIDE_SELL, 102, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 5, SIDE_SELL, 103, 10, TIF_GTC) == ME_OK);
    assert(engine_cancel(e, 2) == ME_OK);
    assert(engine_best_bid(e) == 100);
    assert(submit_limit(e, 6, SIDE_SELL, 98, 10, TIF_GTC) == ME_OK);
    assert(engine_best_bid(e) == 98);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_book_depth_after_operations\n");
}

static void test_stp_decrement_then_match(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_stp(e, 1, SIDE_SELL, 50, 3,  TIF_GTC, 1, STP_DECREMENT) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 50, 10, TIF_GTC) == ME_OK); /* no STP */
    assert(submit_limit_stp(e, 3, SIDE_BUY, 50, 10, TIF_GTC, 1, STP_DECREMENT) == ME_OK);
    assert(has_decrement(&log, 3, 1, 3));
    assert(has_trade(&log, 3, 2, 50, 7));
    assert(engine_find_order(e, 3) == NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stp_decrement_then_match\n");
}

static void test_gtd_partial_fill_then_expire(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit_gtd(e, 1, SIDE_SELL, 50, 20, 2000) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY, 50, 5, TIF_GTC) == ME_OK);
    const Order *o1 = engine_find_order(e, 1);
    assert(o1 && o1->m_status == STATUS_PARTIALLY_FILLED);
    engine_expire(e, 2000);
    assert(engine_find_order(e, 1) == NULL);
    assert(engine_best_ask(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_gtd_partial_fill_then_expire\n");
}

/* =========================================================================
 * From test_correctness.cpp: unique tests not already covered
 * ========================================================================= */

static void test_duplicate_id(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    /* Submit duplicate ID — engine must reject with ME_ERR_INVALID */
    assert(submit_limit(e, 1, SIDE_SELL, 100, 10, TIF_GTC) == ME_ERR_INVALID);
    /* Original order must still be active */
    assert(engine_find_order(e, 1) != NULL);
    assert(engine_find_order(e, 1)->m_side == SIDE_BUY);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_duplicate_id\n");
}

static void test_resource_lifecycle(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    for (int i = 0; i < 1000; i++) {
        OrderId bid_id = (OrderId)(i * 2 + 1);
        OrderId ask_id = (OrderId)(i * 2 + 2);
        assert(submit_limit(e, bid_id, SIDE_BUY,  1000, 1, TIF_GTC) == ME_OK);
        assert(submit_limit(e, ask_id, SIDE_SELL, 1000, 1, TIF_GTC) == ME_OK);
    }
    assert(log.trade_count == 1000);
    assert(engine_best_bid(e) == PRICE_NULL);
    assert(engine_best_ask(e) == PRICE_NULL);
    for (int i = 0; i < 2000; i++)
        assert(engine_find_order(e, (OrderId)(i + 1)) == NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_resource_lifecycle\n");
}

static void test_resource_lifecycle_fill(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    for (OrderId i = 1; i <= 50; i++)
        assert(submit_limit(e, i, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    for (OrderId i = 51; i <= 100; i++)
        assert(submit_limit(e, i, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(engine_best_bid(e) == PRICE_NULL);
    assert(engine_best_ask(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_resource_lifecycle_fill\n");
}

static void test_no_stale_index(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY,  100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 10, TIF_GTC) == ME_OK);
    assert(engine_find_order(e, 1) == NULL);
    assert(engine_find_order(e, 2) == NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_no_stale_index\n");
}

static void test_empty_level_cleanup(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY, 100, 10, TIF_GTC) == ME_OK);
    assert(e->m_book.m_bid_levels == 1);
    assert(engine_cancel(e, 1) == ME_OK);
    assert(e->m_book.m_bid_levels == 1); /* still one order */
    assert(engine_cancel(e, 2) == ME_OK);
    assert(e->m_book.m_bid_levels == 0); /* level removed */
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_empty_level_cleanup\n");
}

static void test_iceberg_full_consume(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_iceberg(e, 1, SIDE_BUY, 100, 20, 5, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_SELL, 100, 20, TIF_GTC) == ME_OK);
    /* 4 trades of 5 each through reloads */
    assert(count_type(&log, EVT_TRADE_EXECUTED) == 4);
    assert(engine_find_order(e, 1) == NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_iceberg_full_consume\n");
}

/* =========================================================================
 * Legacy tests kept from original main.c
 * ========================================================================= */

static void test_basic_limit_match(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 1000, 100, TIF_GTC) == ME_OK);
    assert(engine_best_bid(e) == 1000);
    assert(log.trade_count == 0);
    assert(submit_limit(e, 2, SIDE_BUY, 1000, 50, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_BUY, 1005, 75, TIF_GTC) == ME_OK);
    assert(engine_best_bid(e) == 1005);
    assert(submit_limit(e, 4, SIDE_SELL, 995, 30, TIF_GTC) == ME_OK);
    assert(log.trade_count == 1);
    {
        int found = 0;
        for (int i = 0; i < log.count; i++) {
            if (log.events[i].type == EVT_TRADE_EXECUTED) {
                assert(log.events[i].trade_price == 1005);
                assert(log.events[i].trade_qty   == 30);
                found = 1;
            }
        }
        assert(found);
    }
    const Order *o3 = engine_find_order(e, 3);
    assert(o3 && o3->m_remaining_qty == 45);
    assert(engine_best_bid(e) == 1005);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_basic_limit_match\n");
}

static void test_market_sweep(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 1000, 100, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 2, SIDE_BUY, 1000,  50, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 3, SIDE_BUY, 1005,  75, TIF_GTC) == ME_OK);
    assert(submit_limit(e, 4, SIDE_SELL, 995,  30, TIF_GTC) == ME_OK);
    assert(log.trade_count == 1);
    assert(engine_find_order(e, 3)->m_remaining_qty == 45);
    int prev_trades = log.trade_count;
    assert(submit_market(e, 5, SIDE_SELL, 200, TIF_IOC) == ME_OK);
    assert(log.trade_count == prev_trades + 3);
    int found_ioc = 0;
    for (int i = 0; i < log.count; i++) {
        if (log.events[i].type == EVT_ORDER_CANCELLED &&
            log.events[i].reason == CANCEL_IOC_REMAINDER)
            found_ioc = 1;
    }
    assert(found_ioc);
    assert(engine_best_bid(e) == PRICE_NULL);
    assert(engine_best_ask(e) == PRICE_NULL);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_market_sweep\n");
}

static void test_stop_trigger_cascade(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 1, SIDE_BUY, 1000, 50, TIF_GTC) == ME_OK);
    OrderDesc stop = {0};
    stop.id=2; stop.side=SIDE_SELL; stop.order_type=ORDER_TYPE_STOP_LIMIT;
    stop.price=990; stop.stop_price=1000;
    stop.quantity=30; stop.display_qty=QTY_NULL; stop.min_qty=QTY_NULL;
    stop.expire_time=TIMESTAMP_NULL; stop.tif=TIF_GTC; stop.stp_policy=STP_NONE;
    assert(engine_process(e, &stop) == ME_OK);
    assert(log.trade_count == 0);
    assert(submit_limit(e, 3, SIDE_SELL, 1000, 10, TIF_GTC) == ME_OK);
    assert(log.trade_count >= 1);
    assert(log.trigger_count == 1);
    assert(log.trade_count >= 2);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_stop_trigger_cascade\n");
}

static void test_bug1_fifo_holds(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    assert(submit_limit(e, 100, SIDE_BUY, 1000, 200, TIF_GTC) == ME_OK);
    OrderDesc s1 = {0};
    s1.id=1; s1.side=SIDE_SELL; s1.order_type=ORDER_TYPE_STOP_LIMIT;
    s1.price=995; s1.stop_price=1000;
    s1.quantity=50; s1.display_qty=QTY_NULL; s1.min_qty=QTY_NULL;
    s1.expire_time=TIMESTAMP_NULL; s1.tif=TIF_GTC; s1.stp_policy=STP_NONE;
    engine_process(e, &s1);
    OrderDesc s2 = s1; s2.id=2;
    engine_process(e, &s2);
    assert(submit_limit(e, 99, SIDE_SELL, 1000, 10, TIF_GTC) == ME_OK);
    assert(log.trigger_count == 2);
    assert(log.trade_count >= 3);
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_bug1_fifo_holds\n");
}

static void test_bug2_iceberg_decrement_reload(void) {
    EventLog log; event_log_reset(&log);
    MatchingEngine *e = alloc_engine(&log);
    OrderDesc ice = {0};
    ice.id=1; ice.side=SIDE_SELL; ice.order_type=ORDER_TYPE_LIMIT;
    ice.price=1000; ice.stop_price=PRICE_NULL;
    ice.quantity=100; ice.display_qty=20; ice.min_qty=QTY_NULL;
    ice.expire_time=TIMESTAMP_NULL; ice.tif=TIF_GTC;
    ice.stp_group=1; ice.stp_policy=STP_DECREMENT;
    engine_process(e, &ice);
    OrderDesc s2 = {0};
    s2.id=2; s2.side=SIDE_SELL; s2.order_type=ORDER_TYPE_LIMIT;
    s2.price=1000; s2.stop_price=PRICE_NULL;
    s2.quantity=50; s2.display_qty=QTY_NULL; s2.min_qty=QTY_NULL;
    s2.expire_time=TIMESTAMP_NULL; s2.tif=TIF_GTC;
    s2.stp_group=1; s2.stp_policy=STP_DECREMENT;
    engine_process(e, &s2);
    OrderDesc inc = {0};
    inc.id=3; inc.side=SIDE_BUY; inc.order_type=ORDER_TYPE_LIMIT;
    inc.price=1000; inc.stop_price=PRICE_NULL;
    inc.quantity=20; inc.display_qty=QTY_NULL; inc.min_qty=QTY_NULL;
    inc.expire_time=TIMESTAMP_NULL; inc.tif=TIF_GTC;
    inc.stp_group=1; inc.stp_policy=STP_DECREMENT;
    engine_process(e, &inc);
    const Order *o1 = engine_find_order(e, 1);
    if (o1) {
        assert(o1->m_remaining_qty == 80);
        assert(o1->m_visible_qty   == 20);
    }
    engine_check_invariants(e);
    free_engine(e);
    printf("PASS: test_bug2_iceberg_decrement_reload\n");
}

/* =========================================================================
 * LCG pseudo-random number generator
 * ========================================================================= */

static uint64_t lcg_state = 0x123456789ABCDEF0ULL;

static inline uint64_t lcg_next(void) {
    lcg_state = lcg_state * 6364136223846793005ULL + 1442695040888963407ULL;
    return lcg_state;
}

/* =========================================================================
 * Benchmark: 10M orders, mixed workload
 * ========================================================================= */

static void benchmark(void) {
    printf("\n--- Benchmark ---\n");

    MatchingEngine *e = (MatchingEngine *)calloc(1, sizeof(MatchingEngine));
    assert(e);
    engine_init(e, NULL, NULL);

    /* Book: 10 bid levels (991..1000) x 50 orders, 10 ask levels (1001..1010) x 50.
     * Strategy: each iteration replenishes + aggresses to guarantee trades.
     * MAX_ORDER_ID is 16M, plenty of headroom for 10M trades worth of IDs. */
    OrderId next_id = 1;
    for (int lvl = 0; lvl < 10; lvl++) {
        for (int j = 0; j < 50; j++) {
            submit_limit(e, next_id++, SIDE_BUY,
                         (Price)(991 + lvl), (Quantity)50, TIF_GTC);
            submit_limit(e, next_id++, SIDE_SELL,
                         (Price)(1001 + lvl), (Quantity)50, TIF_GTC);
        }
    }

    const uint64_t TARGET_TRADES = 10000000ULL;
    uint64_t total_ops = 0;

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    while (e->m_trade_id_seq < TARGET_TRADES) {
        uint64_t r = lcg_next();
        total_ops++;

        /* Step 1: Replenish one side to keep book deep (auto-assign ID) */
        {
            Side s = (Side)(r & 1);
            Price price;
            if (s == SIDE_BUY)
                price = 991 + (Price)(lcg_next() % 10);
            else
                price = 1001 + (Price)(lcg_next() % 10);
            Quantity qty = (Quantity)(20 + lcg_next() % 80);
            OrderDesc d = {0};
            d.side = s;
            d.order_type = ORDER_TYPE_LIMIT;
            d.price = price;
            d.stop_price = PRICE_NULL;
            d.quantity = qty;
            d.display_qty = QTY_NULL;
            d.min_qty = QTY_NULL;
            d.expire_time = TIMESTAMP_NULL;
            d.tif = TIF_GTC;
            d.stp_policy = STP_NONE;
            engine_process(e, &d);
        }

        /* Step 2: Aggressive order that crosses spread → trade (auto-assign ID) */
        {
            r = lcg_next();
            Side s = (Side)(r & 1);
            Price price;
            if (s == SIDE_BUY)
                price = 1001 + (Price)(lcg_next() % 10);
            else
                price = 991 + (Price)(lcg_next() % 10);
            Quantity qty = (Quantity)(1 + lcg_next() % 10);
            OrderDesc d = {0};
            d.side = s;
            d.order_type = ORDER_TYPE_LIMIT;
            d.price = price;
            d.stop_price = PRICE_NULL;
            d.quantity = qty;
            d.display_qty = QTY_NULL;
            d.min_qty = QTY_NULL;
            d.expire_time = TIMESTAMP_NULL;
            d.tif = TIF_IOC;
            d.stp_policy = STP_NONE;
            engine_process(e, &d);
        }

        /* Step 3: Cancel 2 random orders + occasionally amend — keeps pool healthy */
        {
            engine_cancel(e, (OrderId)(1 + lcg_next() % MAX_ORDER_ID));
            engine_cancel(e, (OrderId)(1 + lcg_next() % MAX_ORDER_ID));
            if (lcg_next() % 5 == 0) {
                OrderId amend_id = (OrderId)(1 + lcg_next() % MAX_ORDER_ID);
                Quantity new_qty = (Quantity)(1 + lcg_next() % 40);
                AmendDesc a = { amend_id, PRICE_NULL, new_qty };
                engine_amend(e, &a);
            }
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);

    double elapsed = (t1.tv_sec - t0.tv_sec) +
                     (t1.tv_nsec - t0.tv_nsec) * 1e-9;

    printf("Total ops:    %llu\n", (unsigned long long)total_ops);
    printf("Trades:       %llu\n", (unsigned long long)e->m_trade_id_seq);
    printf("Trade ratio:  %.1f%%\n", 100.0 * e->m_trade_id_seq / total_ops);
    printf("Time:         %.3f s\n", elapsed);
    printf("Ops/sec:      %.2f M\n", total_ops / elapsed / 1e6);
    printf("Trades/sec:   %.2f M\n", e->m_trade_id_seq / elapsed / 1e6);
    printf("Avg trade:    %.0f ns\n", elapsed / e->m_trade_id_seq * 1e9);

    free(e);
}

/* =========================================================================
 * main
 * ========================================================================= */

int main(void) {
    printf("=== Matching Engine Tests ===\n\n"); fflush(stdout);

    /* --- Basic LIMIT --- */
    printf("--- Basic LIMIT ---\n");
    test_limit_rest_buy();           fflush(stdout);
    test_limit_rest_sell();          fflush(stdout);
    test_limit_match_exact();        fflush(stdout);
    test_limit_match_price_improvement(); fflush(stdout);
    test_limit_partial_fill();       fflush(stdout);
    test_limit_fifo_same_price();    fflush(stdout);
    test_limit_fifo_partial_chain(); fflush(stdout);
    test_limit_sweep_two_levels();   fflush(stdout);
    test_limit_sweep_three_levels(); fflush(stdout);
    test_limit_no_cross();           fflush(stdout);
    test_limit_sell_aggressor();     fflush(stdout);
    test_level_cleanup_after_full_fill(); fflush(stdout);

    /* --- MARKET --- */
    printf("\n--- MARKET ---\n");
    test_market_full_fill();         fflush(stdout);
    test_market_partial_ioc();       fflush(stdout);
    test_market_empty_book();        fflush(stdout);
    test_market_fok_full();          fflush(stdout);
    test_market_fok_reject();        fflush(stdout);
    test_market_sweep_multiple_levels(); fflush(stdout);
    test_market_sell();              fflush(stdout);

    /* --- MTL --- */
    printf("\n--- MTL ---\n");
    test_mtl_convert_and_rest();     fflush(stdout);
    test_mtl_no_liquidity();         fflush(stdout);
    test_mtl_full_fill_phase1();     fflush(stdout);
    test_mtl_rest_visible_to_next(); fflush(stdout);
    test_mtl_sell_side();            fflush(stdout);
    test_mtl_gtd();                  fflush(stdout);

    /* --- Time-In-Force --- */
    printf("\n--- Time-In-Force ---\n");
    test_ioc_partial();              fflush(stdout);
    test_ioc_full_fill();            fflush(stdout);
    test_ioc_no_match();             fflush(stdout);
    test_fok_reject_insufficient();  fflush(stdout);
    test_fok_exact_fill();           fflush(stdout);
    test_fok_across_levels();        fflush(stdout);
    test_fok_empty_book();           fflush(stdout);
    test_gtc_rest();                 fflush(stdout);
    test_gtd_rest_and_expire();      fflush(stdout);
    test_gtd_multiple_expire();      fflush(stdout);
    test_gtd_gtc_coexist();          fflush(stdout);
    test_day_rest();                 fflush(stdout);

    /* --- Iceberg --- */
    printf("\n--- Iceberg ---\n");
    test_iceberg_visible_qty();      fflush(stdout);
    test_iceberg_reload_after_fill(); fflush(stdout);
    test_iceberg_priority_loss_after_reload(); fflush(stdout);
    test_iceberg_multiple_reloads(); fflush(stdout);
    test_iceberg_reload_remaining_less_than_display(); fflush(stdout);
    test_iceberg_full_drain();       fflush(stdout);
    test_iceberg_partial_visible_no_reload(); fflush(stdout);
    test_fok_with_iceberg();         fflush(stdout);
    test_iceberg_sell_side();        fflush(stdout);

    /* --- Post-Only --- */
    printf("\n--- Post-Only ---\n");
    test_postonly_reject_would_cross(); fflush(stdout);
    test_postonly_rest_no_cross();   fflush(stdout);
    test_postonly_sell_would_cross(); fflush(stdout);
    test_postonly_sell_rest();       fflush(stdout);
    test_postonly_empty_book();      fflush(stdout);

    /* --- MinQty --- */
    printf("\n--- MinQty ---\n");
    test_minqty_reject_insufficient(); fflush(stdout);
    test_minqty_exact_threshold();   fflush(stdout);
    test_minqty_cleared_after_fill(); fflush(stdout);
    test_minqty_resting_has_no_constraint(); fflush(stdout);

    /* --- STP --- */
    printf("\n--- STP ---\n");
    test_stp_cancel_newest();        fflush(stdout);
    test_stp_cancel_oldest();        fflush(stdout);
    test_stp_cancel_both();          fflush(stdout);
    test_stp_decrement();            fflush(stdout);
    test_stp_decrement_resting_to_zero(); fflush(stdout);
    test_stp_cancel_oldest_continues_to_non_stp(); fflush(stdout);
    test_stp_cancel_oldest_multiple_same_group(); fflush(stdout);
    test_stp_incoming_policy_governs(); fflush(stdout);
    test_stp_different_groups_no_conflict(); fflush(stdout);
    test_stp_no_group_no_conflict(); fflush(stdout);
    test_stp_across_price_levels();  fflush(stdout);
    test_stp_market_with_stp();      fflush(stdout);

    /* --- Stop Orders --- */
    printf("\n--- Stop Orders ---\n");
    test_stop_limit_immediate_buy(); fflush(stdout);
    test_stop_limit_immediate_sell(); fflush(stdout);
    test_stop_rests_when_not_triggered(); fflush(stdout);
    test_stop_no_trigger_no_trades(); fflush(stdout);
    test_stop_triggered_by_trade();  fflush(stdout);
    test_sell_stop_triggered();      fflush(stdout);
    test_sell_stop_not_triggered();  fflush(stdout);
    test_stop_market_immediate();    fflush(stdout);
    test_sell_stop_market();         fflush(stdout);
    test_multiple_stops_triggered_by_one_trade(); fflush(stdout);
    test_stop_fifo_order();          fflush(stdout);
    test_stop_cascade_triggers_another(); fflush(stdout);
    test_cancel_stop_order();        fflush(stdout);
    test_stop_converts_to_limit_and_matches(); fflush(stdout);
    test_stop_converts_and_rests();  fflush(stdout);

    /* --- Cancel --- */
    printf("\n--- Cancel ---\n");
    test_cancel_resting();           fflush(stdout);
    test_cancel_already_filled();    fflush(stdout);
    test_cancel_already_cancelled(); fflush(stdout);
    test_cancel_nonexistent();       fflush(stdout);
    test_cancel_middle_of_level();   fflush(stdout);
    test_cancel_last_at_level();     fflush(stdout);
    test_cancel_partially_filled();  fflush(stdout);

    /* --- Amend --- */
    printf("\n--- Amend ---\n");
    test_amend_qty_decrease_keeps_priority(); fflush(stdout);
    test_amend_price_loses_priority(); fflush(stdout);
    test_amend_qty_increase_loses_priority(); fflush(stdout);
    test_amend_crosses_spread();     fflush(stdout);
    test_amend_nonexistent();        fflush(stdout);
    test_amend_filled_order();       fflush(stdout);
    test_amend_same_price_same_qty(); fflush(stdout);
    test_amend_iceberg_qty_decrease(); fflush(stdout);

    /* --- Validation (WF) --- */
    printf("\n--- Validation (WF-1 to WF-20) ---\n");
    test_wf1_zero_qty();             fflush(stdout);
    test_wf2_limit_no_price();       fflush(stdout);
    test_wf2a_stop_limit_no_price(); fflush(stdout);
    test_wf2b_mtl_with_price();      fflush(stdout);
    test_wf3_market_with_price();    fflush(stdout);
    test_wf3_stop_market_with_price(); fflush(stdout);
    test_wf4_stop_limit_no_stop_price(); fflush(stdout);
    test_wf4_stop_market_no_stop_price(); fflush(stdout);
    test_wf5_limit_with_stop_price(); fflush(stdout);
    test_wf5_market_with_stop_price(); fflush(stdout);
    test_wf5_mtl_with_stop_price();  fflush(stdout);
    test_wf6_gtd_no_expire();        fflush(stdout);
    test_wf7_non_gtd_with_expire();  fflush(stdout);
    test_wf8_market_gtc();           fflush(stdout);
    test_wf8_market_gtd();           fflush(stdout);
    test_wf8a_mtl_ioc();             fflush(stdout);
    test_wf8a_mtl_fok();             fflush(stdout);
    test_wf9_display_gt_qty();       fflush(stdout);
    test_wf10_iceberg_on_market();   fflush(stdout);
    test_wf13_postonly_on_market();  fflush(stdout);
    test_wf14_postonly_ioc();        fflush(stdout);
    test_wf14_postonly_fok();        fflush(stdout);
    test_wf15_mtl_postonly();        fflush(stdout);
    test_wf16_group_without_policy(); fflush(stdout);
    test_wf16_policy_without_group(); fflush(stdout);
    test_wf18_minqty_gt_qty();       fflush(stdout);
    test_wf19_minqty_with_postonly(); fflush(stdout);
    test_wf20_fok_with_minqty();     fflush(stdout);

    /* --- Invariants --- */
    printf("\n--- Invariants ---\n");
    test_inv_uncrossed_book();       fflush(stdout);
    test_inv_no_ghosts_on_book();    fflush(stdout);
    test_inv_no_market_on_book();    fflush(stdout);
    test_inv_no_mtl_on_book();       fflush(stdout);
    test_inv_minqty_cleared_on_book(); fflush(stdout);
    test_inv_passive_price_rule();   fflush(stdout);
    test_inv_stp_no_self_trade();    fflush(stdout);

    /* --- Event Ordering --- */
    printf("\n--- Event Ordering ---\n");
    test_event_order_accept_then_trade(); fflush(stdout);
    test_event_trades_best_price_first(); fflush(stdout);

    /* --- Appendix B --- */
    printf("\n--- Appendix B ---\n");
    test_appendix_b();               fflush(stdout);

    /* --- Complex Scenarios --- */
    printf("\n--- Complex Scenarios ---\n");
    test_many_levels_ascending_asks(); fflush(stdout);
    test_many_levels_descending_bids(); fflush(stdout);
    test_cancel_then_resubmit_same_id(); fflush(stdout);
    test_iceberg_with_multiple_aggressors(); fflush(stdout);
    test_partial_fill_then_expire(); fflush(stdout);
    test_rapid_insert_cancel_sequence(); fflush(stdout);
    test_amend_and_match_sequence(); fflush(stdout);
    test_book_depth_after_operations(); fflush(stdout);
    test_stp_decrement_then_match(); fflush(stdout);
    test_gtd_partial_fill_then_expire(); fflush(stdout);
    test_stop_converts_to_limit_and_matches(); fflush(stdout);
    test_stop_converts_and_rests();  fflush(stdout);

    /* --- From test_correctness.cpp --- */
    printf("\n--- Correctness (from test_correctness.cpp) ---\n");
    test_duplicate_id();             fflush(stdout);
    test_no_stale_index();           fflush(stdout);
    test_empty_level_cleanup();      fflush(stdout);
    test_iceberg_full_consume();     fflush(stdout);
    test_resource_lifecycle_fill();  fflush(stdout);

    /* --- Legacy / Bug regression --- */
    printf("\n--- Legacy / Bug regression ---\n");
    test_basic_limit_match();        fflush(stdout);
    test_market_sweep();             fflush(stdout);
    test_stop_trigger_cascade();     fflush(stdout);
    test_bug1_fifo_holds();          fflush(stdout);
    test_bug2_iceberg_decrement_reload(); fflush(stdout);
    test_resource_lifecycle();       fflush(stdout);

    printf("\nAll tests passed.\n"); fflush(stdout);

    benchmark();

    return 0;
}
