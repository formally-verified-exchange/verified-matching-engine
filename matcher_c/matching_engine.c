/*
 * matching_engine.c
 * Price-Time Priority (FIFO) Matching Engine — Implementation
 * C17, no exceptions, no RTTI, no malloc on hot path
 */

#include "matching_engine.h"

#include <string.h>
#include <stdio.h>

/* =========================================================================
 * Utility macros
 * ========================================================================= */

#define ME_LIKELY(x)   __builtin_expect(!!(x), 1)
#define ME_UNLIKELY(x) __builtin_expect(!!(x), 0)

static inline Quantity qty_min(Quantity a, Quantity b) { return a < b ? a : b; }

/* =========================================================================
 * Pool allocator implementations
 * ========================================================================= */

static void order_pool_init(OrderPool *p) {
    p->m_free_head = NULL;
    p->m_allocated = 0;
}

static Order *order_pool_alloc(OrderPool *p) {
    if (p->m_free_head) {
        Order *o = p->m_free_head;
        p->m_free_head = o->m_next;
        return o;
    }
    if (ME_UNLIKELY(p->m_allocated >= POOL_ORDER_CAPACITY)) return NULL;
    return &p->m_storage[p->m_allocated++];
}

static void order_pool_free(OrderPool *p, Order *o) {
    o->m_next = p->m_free_head;
    p->m_free_head = o;
}

static void level_pool_init(LevelPool *p) {
    p->m_free_head = NULL;
    p->m_allocated = 0;
}

static PriceLevel *level_pool_alloc(LevelPool *p) {
    if (p->m_free_head) {
        PriceLevel *l = p->m_free_head;
        p->m_free_head = l->m_next;
        return l;
    }
    if (ME_UNLIKELY(p->m_allocated >= POOL_LEVEL_CAPACITY)) return NULL;
    return &p->m_storage[p->m_allocated++];
}

static void level_pool_free(LevelPool *p, PriceLevel *l) {
    l->m_next = p->m_free_head;
    p->m_free_head = l;
}

/* =========================================================================
 * Trade buffer
 * ========================================================================= */

static void trade_buf_init(TradeBuffer *tb) {
    tb->m_head = tb->m_tail = tb->m_count = 0;
}

/* Returns pointer to next write slot; advances tail. Overwrites oldest on overflow. */
static Trade *trade_buf_push(TradeBuffer *tb) {
    Trade *t = &tb->m_trades[tb->m_tail % POOL_TRADE_CAPACITY];
    tb->m_tail++;
    tb->m_count++;
    return t;
}

/* =========================================================================
 * Event emission helpers
 * ========================================================================= */

static inline void emit(MatchingEngine *e, int type, const void *data) {
    if (ME_LIKELY(e->m_callback != NULL)) {
        e->m_callback(type, data, e->m_callback_ctx);
    }
}

/* =========================================================================
 * Price level helpers
 * ========================================================================= */

/* Append order to back of level queue (FIFO). */
static void level_push_back(PriceLevel *lvl, Order *o) {
    o->m_prev = lvl->m_tail;
    o->m_next = NULL;
    if (lvl->m_tail) lvl->m_tail->m_next = o;
    else             lvl->m_head = o;
    lvl->m_tail = o;
    lvl->m_count++;
    o->m_level = lvl;
}

/* Remove order from level queue (O(1) with prev/next). */
static void level_remove(PriceLevel *lvl, Order *o) {
    if (o->m_prev) o->m_prev->m_next = o->m_next;
    else           lvl->m_head = o->m_next;
    if (o->m_next) o->m_next->m_prev = o->m_prev;
    else           lvl->m_tail = o->m_prev;
    o->m_prev = o->m_next = NULL;
    o->m_level = NULL;
    lvl->m_count--;
}

/* Move order to back of level queue (iceberg reload / timestamp refresh). */
static void level_move_to_back(PriceLevel *lvl, Order *o) {
    if (lvl->m_tail == o) return; /* already at back */
    level_remove(lvl, o);
    level_push_back(lvl, o);
}

/* =========================================================================
 * Book-level helpers: insert / remove price levels
 * ========================================================================= */

/* Insert a new price level at the correct sorted position.
 * bids: descending (higher price closer to head)
 * asks: ascending  (lower price closer to head)
 * Returns inserted level.
 */
static PriceLevel *book_insert_level(MatchingEngine *e,
                                      PriceLevel **head_ptr,
                                      uint32_t *count_ptr,
                                      Price price,
                                      Side side) {
    PriceLevel *lvl = level_pool_alloc(&e->m_level_pool);
    if (ME_UNLIKELY(!lvl)) return NULL;

    lvl->m_price = price;
    lvl->m_head = lvl->m_tail = NULL;
    lvl->m_count = 0;
    lvl->m_prev = lvl->m_next = NULL;

    PriceLevel *cur = *head_ptr;
    PriceLevel *prev = NULL;

    /* Walk until we find the insertion point. */
    while (cur) {
        bool insert_before;
        if (side == SIDE_BUY) {
            /* bids descending: insert before first level with lower price */
            insert_before = (price > cur->m_price);
        } else {
            /* asks ascending: insert before first level with higher price */
            insert_before = (price < cur->m_price);
        }
        if (insert_before) break;
        prev = cur;
        cur = cur->m_next;
    }

    lvl->m_prev = prev;
    lvl->m_next = cur;
    if (prev) prev->m_next = lvl;
    else      *head_ptr = lvl;
    if (cur)  cur->m_prev = lvl;

    (*count_ptr)++;
    return lvl;
}

/* Remove a price level from the book (must be empty). */
static void book_remove_level(MatchingEngine *e,
                               PriceLevel **head_ptr,
                               uint32_t *count_ptr,
                               PriceLevel *lvl) {
    assert(lvl->m_count == 0);
    if (lvl->m_prev) lvl->m_prev->m_next = lvl->m_next;
    else             *head_ptr = lvl->m_next;
    if (lvl->m_next) lvl->m_next->m_prev = lvl->m_prev;
    level_pool_free(&e->m_level_pool, lvl);
    (*count_ptr)--;
}

/* Find the price level for a given price on a given side.
 * Returns NULL if not found. O(P) but P is typically small. */
static PriceLevel *book_find_level(PriceLevel *head, Price price) {
    for (PriceLevel *l = head; l; l = l->m_next) {
        if (l->m_price == price) return l;
        /* Since levels are sorted, we can break early */
    }
    return NULL;
}

/* Find or create price level. Returns NULL on pool exhaustion. */
static PriceLevel *book_find_or_create_level(MatchingEngine *e,
                                               PriceLevel **head_ptr,
                                               uint32_t *count_ptr,
                                               Price price,
                                               Side side) {
    PriceLevel *l = book_find_level(*head_ptr, price);
    if (l) return l;
    return book_insert_level(e, head_ptr, count_ptr, price, side);
}

/* =========================================================================
 * Order index helpers
 * ========================================================================= */

static inline void index_set(MatchingEngine *e, OrderId id, Order *o) {
    if (id > 0 && id <= MAX_ORDER_ID) e->m_order_index[id] = o;
}

static inline Order *index_get(const MatchingEngine *e, OrderId id) {
    if (id > 0 && id <= MAX_ORDER_ID) return e->m_order_index[id];
    return NULL;
}

static inline void index_clear(MatchingEngine *e, OrderId id) {
    if (id > 0 && id <= MAX_ORDER_ID) {
        e->m_order_index[id] = NULL;
        /* Recycle ID for O(1) auto-assign reuse */
        if (e->m_id_free_count < ID_FREE_STACK_CAP)
            e->m_id_free_stack[e->m_id_free_count++] = id;
    }
}

/* =========================================================================
 * Stop order management
 * ========================================================================= */

/* Insert stop order into the appropriate sorted list using m_prev/m_next.
 * BUY stops list: ascending order by stop_price (lowest stop_price at head,
 *   so we can break early when head->stop_price > last_trade_price).
 *   Wait — BUY stops trigger when price >= stop_price.
 *   For fast scan: sort descending so we can break when head->stop_price > trade_price.
 *   Actually: BUY triggers when trade >= stop_price. If we sort ascending (lowest first),
 *   we scan from head and stop when stop_price > trade_price.
 *   → Sort ascending by stop_price for BUY stops.
 * SELL stops list: sort descending by stop_price.
 *   SELL triggers when trade <= stop_price. Scan from head, stop when stop_price < trade_price.
 *   → Sort descending by stop_price for SELL stops.
 */
static ME_Result stops_add(MatchingEngine *e, Order *o) {
    /* O(1) prepend; maintain min/max for fast evaluate_stops skipping */
    if (o->m_side == SIDE_BUY) {
        o->m_prev = NULL;
        o->m_next = e->m_book.m_buy_stops_head;
        if (e->m_book.m_buy_stops_head)
            e->m_book.m_buy_stops_head->m_prev = o;
        e->m_book.m_buy_stops_head = o;
        if (e->m_book.m_min_buy_stop == PRICE_NULL ||
            o->m_stop_price < e->m_book.m_min_buy_stop)
            e->m_book.m_min_buy_stop = o->m_stop_price;
    } else {
        o->m_prev = NULL;
        o->m_next = e->m_book.m_sell_stops_head;
        if (e->m_book.m_sell_stops_head)
            e->m_book.m_sell_stops_head->m_prev = o;
        e->m_book.m_sell_stops_head = o;
        if (o->m_stop_price > e->m_book.m_max_sell_stop)
            e->m_book.m_max_sell_stop = o->m_stop_price;
    }
    e->m_book.m_stop_count++;
    return ME_OK;
}

/* Remove a stop order from its list. O(1) via m_prev/m_next.
 * Note: min/max hints may become stale; they are conservative (can cause
 * unnecessary scans but never miss triggered stops). */
static void stops_remove(MatchingEngine *e, Order *o) {
    Order **head_ptr = (o->m_side == SIDE_BUY)
                       ? &e->m_book.m_buy_stops_head
                       : &e->m_book.m_sell_stops_head;
    if (o->m_prev) o->m_prev->m_next = o->m_next;
    else           *head_ptr = o->m_next;
    if (o->m_next) o->m_next->m_prev = o->m_prev;
    o->m_prev = o->m_next = NULL;
    e->m_book.m_stop_count--;

    /* Lazy invalidation: widen the hint (never narrow).
     * Stale hints cause at most an unnecessary scan in evaluate_stops,
     * but never miss a triggered stop. Avoids the O(n) rescan that was
     * responsible for 95% of all L1 data-cache read misses. */
    if (o->m_side == SIDE_BUY) {
        if (e->m_book.m_buy_stops_head == NULL)
            e->m_book.m_min_buy_stop = PRICE_NULL;
        /* else: leave hint as-is; evaluate_stops recomputes after firing */
    } else {
        if (e->m_book.m_sell_stops_head == NULL)
            e->m_book.m_max_sell_stop = 0;
        /* else: leave hint as-is; evaluate_stops recomputes after firing */
    }
}

/* Find a stop order by ID (for cancel). Since stops are in the order_index,
 * this is just an index lookup. Returns NULL if not found or not a stop order. */


/* =========================================================================
 * Validation (WF checks)
 * ========================================================================= */

static RejectReason validate_order(const MatchingEngine *e, const OrderDesc *d) {
    /* WF-1 */
    if (d->quantity == 0) return REJECT_WF1;

    /* WF-2 */
    if (d->order_type == ORDER_TYPE_LIMIT &&
        (d->price == PRICE_NULL || d->price == 0))
        return REJECT_WF2;

    /* WF-2a */
    if (d->order_type == ORDER_TYPE_STOP_LIMIT &&
        (d->price == PRICE_NULL || d->price == 0))
        return REJECT_WF2A;

    /* WF-2b */
    if (d->order_type == ORDER_TYPE_MARKET_TO_LIMIT && d->price != PRICE_NULL)
        return REJECT_WF2B;

    /* WF-3 */
    if ((d->order_type == ORDER_TYPE_MARKET || d->order_type == ORDER_TYPE_STOP_MARKET) &&
        d->price != PRICE_NULL)
        return REJECT_WF3;

    /* WF-4 */
    if ((d->order_type == ORDER_TYPE_STOP_LIMIT || d->order_type == ORDER_TYPE_STOP_MARKET) &&
        (d->stop_price == PRICE_NULL || d->stop_price == 0))
        return REJECT_WF4;

    /* WF-5 */
    if ((d->order_type == ORDER_TYPE_LIMIT ||
         d->order_type == ORDER_TYPE_MARKET ||
         d->order_type == ORDER_TYPE_MARKET_TO_LIMIT) &&
        d->stop_price != PRICE_NULL)
        return REJECT_WF5;

    /* WF-6 */
    if (d->tif == TIF_GTD &&
        (d->expire_time == TIMESTAMP_NULL || d->expire_time <= e->m_clock))
        return REJECT_WF6;

    /* WF-7 */
    if (d->tif != TIF_GTD && d->expire_time != TIMESTAMP_NULL)
        return REJECT_WF7;

    /* WF-8 */
    if (d->order_type == ORDER_TYPE_MARKET &&
        d->tif != TIF_IOC && d->tif != TIF_FOK)
        return REJECT_WF8;

    /* WF-8a */
    if (d->order_type == ORDER_TYPE_MARKET_TO_LIMIT &&
        (d->tif == TIF_IOC || d->tif == TIF_FOK))
        return REJECT_WF8A;

    /* WF-9 */
    if (d->display_qty != QTY_NULL &&
        (d->display_qty == 0 || d->display_qty > d->quantity))
        return REJECT_WF9;

    /* WF-10 */
    if (d->display_qty != QTY_NULL && d->order_type != ORDER_TYPE_LIMIT)
        return REJECT_WF10;

    /* WF-11: remainingQty = quantity at creation — enforced by construction */
    /* WF-12: visibleQty set on construction */

    /* WF-13 */
    if (d->post_only && d->order_type != ORDER_TYPE_LIMIT)
        return REJECT_WF13;

    /* WF-14 */
    if (d->post_only && (d->tif == TIF_IOC || d->tif == TIF_FOK))
        return REJECT_WF14;

    /* WF-15 */
    if ((d->order_type == ORDER_TYPE_MARKET || d->order_type == ORDER_TYPE_MARKET_TO_LIMIT) &&
        d->post_only)
        return REJECT_WF15;

    /* WF-16 */
    if ((d->stp_group == STP_GROUP_NULL) != (d->stp_policy == STP_NONE))
        return REJECT_WF16;

    /* WF-17 */
    if (d->stp_policy != STP_NONE &&
        d->stp_policy != STP_CANCEL_NEWEST &&
        d->stp_policy != STP_CANCEL_OLDEST &&
        d->stp_policy != STP_CANCEL_BOTH &&
        d->stp_policy != STP_DECREMENT)
        return REJECT_WF17;

    /* WF-18 */
    if (d->min_qty != QTY_NULL &&
        (d->min_qty == 0 || d->min_qty > d->quantity))
        return REJECT_WF18;

    /* WF-19 */
    if (d->min_qty != QTY_NULL && d->post_only)
        return REJECT_WF19;

    /* WF-20 */
    if (d->tif == TIF_FOK && d->min_qty != QTY_NULL)
        return REJECT_WF20;

    return 0; /* 0 = valid */
}

/* =========================================================================
 * can_match predicate
 * ========================================================================= */

static inline bool can_match(const Order *incoming, Price resting_price) {
    if (incoming->m_order_type == ORDER_TYPE_MARKET ||
        incoming->m_order_type == ORDER_TYPE_MARKET_TO_LIMIT) {
        return true;
    }
    if (incoming->m_side == SIDE_BUY)  return incoming->m_price >= resting_price;
    return incoming->m_price <= resting_price;
}

/* =========================================================================
 * STP conflict detection
 * ========================================================================= */

static inline bool stp_conflict(const Order *incoming, const Order *resting) {
    return (incoming->m_stp_group != STP_GROUP_NULL) &&
           (resting->m_stp_group  != STP_GROUP_NULL) &&
           (incoming->m_stp_group == resting->m_stp_group);
}

/* =========================================================================
 * Forward declarations for recursive calls
 * ========================================================================= */

static void process_order_internal(MatchingEngine *e, Order *o);

/* =========================================================================
 * Remove order from book side (level) + optionally free
 * ========================================================================= */

static void remove_order_from_level(MatchingEngine *e, Order *o, bool free_it) {
    PriceLevel *lvl = (PriceLevel *)o->m_level;
    if (!lvl) return;

    bool is_bid = (o->m_side == SIDE_BUY);
    level_remove(lvl, o);

    if (lvl->m_count == 0) {
        if (is_bid)
            book_remove_level(e, &e->m_book.m_bids_head, &e->m_book.m_bid_levels, lvl);
        else
            book_remove_level(e, &e->m_book.m_asks_head, &e->m_book.m_ask_levels, lvl);
    }

    if (free_it) {
        index_clear(e, o->m_id);
        order_pool_free(&e->m_order_pool, o);
    }
}

/* =========================================================================
 * Insert order into book (after matching, as resting order)
 * ========================================================================= */

static ME_Result insert_into_book(MatchingEngine *e, Order *o) {
    bool is_bid = (o->m_side == SIDE_BUY);
    PriceLevel **head_ptr = is_bid ? &e->m_book.m_bids_head : &e->m_book.m_asks_head;
    uint32_t   *cnt_ptr   = is_bid ? &e->m_book.m_bid_levels : &e->m_book.m_ask_levels;

    PriceLevel *lvl = book_find_or_create_level(e, head_ptr, cnt_ptr, o->m_price, o->m_side);
    if (ME_UNLIKELY(!lvl)) return ME_ERR_POOL_FULL;

    /* Set visible quantity on insert */
    if (o->m_display_qty != QTY_NULL)
        o->m_visible_qty = qty_min(o->m_display_qty, o->m_remaining_qty);
    else
        o->m_visible_qty = o->m_remaining_qty;

    level_push_back(lvl, o);
    return ME_OK;
}

/* =========================================================================
 * FOK / min_qty pre-check (dry run — does NOT modify book)
 * ========================================================================= */

static bool qty_precheck(const MatchingEngine *e,
                          const Order *incoming,
                          Quantity threshold) {
    PriceLevel *contra_head;
    if (incoming->m_side == SIDE_BUY)
        contra_head = e->m_book.m_asks_head;
    else
        contra_head = e->m_book.m_bids_head;

    Quantity available = 0;
    for (PriceLevel *lvl = contra_head; lvl; lvl = lvl->m_next) {
        if (!can_match(incoming, lvl->m_price)) break;
        for (Order *r = lvl->m_head; r; r = r->m_next) {
            if (!stp_conflict(incoming, r)) {
                available += r->m_visible_qty;
                if (available >= threshold) return true;
            }
        }
    }
    return false;
}

/* =========================================================================
 * STP handler (called during matching loop)
 * Returns true if incoming order should stop matching (cancelled).
 * ========================================================================= */

static bool handle_stp(MatchingEngine *e,
                        Order *incoming,
                        Order *resting,
                        PriceLevel *lvl,
                        bool is_bid_resting __attribute__((unused))) {
    STPPolicy policy = incoming->m_stp_policy;

    switch (policy) {
    case STP_CANCEL_NEWEST: {
        incoming->m_status = STATUS_CANCELLED;
        EvtCancelled ev = { incoming, CANCEL_STP_NEWEST };
        emit(e, EVT_ORDER_CANCELLED, &ev);
        return true; /* stop matching */
    }
    case STP_CANCEL_OLDEST: {
        resting->m_status = STATUS_CANCELLED;
        EvtCancelled ev = { resting, CANCEL_STP_OLDEST };
        level_remove(lvl, resting);
        /* Note: do NOT remove empty level here — do_match handles cleanup */
        index_clear(e, resting->m_id);
        emit(e, EVT_ORDER_CANCELLED, &ev);
        order_pool_free(&e->m_order_pool, resting);
        return false; /* continue matching */
    }
    case STP_CANCEL_BOTH: {
        incoming->m_status = STATUS_CANCELLED;
        resting->m_status  = STATUS_CANCELLED;
        EvtCancelled ev_i  = { incoming, CANCEL_STP_BOTH };
        EvtCancelled ev_r  = { resting,  CANCEL_STP_BOTH };
        level_remove(lvl, resting);
        /* Note: do NOT remove empty level here — do_match handles cleanup */
        index_clear(e, resting->m_id);
        emit(e, EVT_ORDER_CANCELLED, &ev_i);
        emit(e, EVT_ORDER_CANCELLED, &ev_r);
        order_pool_free(&e->m_order_pool, resting);
        return true; /* stop matching */
    }
    case STP_DECREMENT: {
        Quantity reduce = qty_min(incoming->m_remaining_qty, resting->m_visible_qty);
        incoming->m_remaining_qty -= reduce;
        resting->m_remaining_qty  -= reduce;
        resting->m_visible_qty    -= reduce;

        EvtDecremented ev = { incoming, resting, reduce };
        emit(e, EVT_ORDER_DECREMENTED, &ev);

        if (incoming->m_remaining_qty == 0) {
            incoming->m_status = STATUS_CANCELLED;
        }
        if (resting->m_remaining_qty == 0) {
            resting->m_status = STATUS_CANCELLED;
            level_remove(lvl, resting);
            /* Note: do NOT remove empty level here — do_match handles cleanup */
            index_clear(e, resting->m_id);
            order_pool_free(&e->m_order_pool, resting);
        } else {
            /* BUG-2 fix: after STP DECREMENT, if resting is an iceberg with
             * visible_qty == 0 but remaining > 0, reload the visible slice,
             * refresh timestamp, move to back of queue. */
            if (resting->m_visible_qty == 0 &&
                resting->m_remaining_qty > 0 &&
                resting->m_display_qty != QTY_NULL) {
                resting->m_visible_qty = qty_min(resting->m_display_qty,
                                                  resting->m_remaining_qty);
                resting->m_timestamp = e->m_clock++;
                level_move_to_back(lvl, resting);
            }
        }

        /* Return true to stop matching if incoming is fully cancelled */
        return (incoming->m_remaining_qty == 0);
    }
    default:
        return false;
    }
}

/* =========================================================================
 * Trade emission helper (write into buffer + callback)
 * ========================================================================= */

static void emit_trade(MatchingEngine *e,
                        Price price,
                        Quantity qty,
                        OrderId aggressor_id,
                        OrderId passive_id,
                        Side aggressor_side) {
    Trade *t = trade_buf_push(&e->m_trade_buf);
    t->m_trade_id     = ++e->m_trade_id_seq;
    t->m_price        = price;
    t->m_quantity     = qty;
    t->m_aggressor_id = aggressor_id;
    t->m_passive_id   = passive_id;
    t->m_aggressor_side = aggressor_side;
    t->m_timestamp    = e->m_clock;
    emit(e, EVT_TRADE_EXECUTED, t);
}

/* =========================================================================
 * Stop triggering
 * ========================================================================= */

/* Temporary array for triggered stops (sorted by timestamp). */
#define MAX_TRIGGERED_STOPS 512

static void evaluate_stops(MatchingEngine *e, Price last_trade_price);

/* =========================================================================
 * Core MATCH procedure
 * Returns number of trades generated.
 * ========================================================================= */

__attribute__((hot))
static int do_match(MatchingEngine *restrict e, Order *restrict incoming) {
    PriceLevel **contra_head_ptr;
    uint32_t   *contra_cnt;
    bool        resting_is_bid;

    if (incoming->m_side == SIDE_BUY) {
        contra_head_ptr = &e->m_book.m_asks_head;
        contra_cnt      = &e->m_book.m_ask_levels;
        resting_is_bid  = false;
    } else {
        contra_head_ptr = &e->m_book.m_bids_head;
        contra_cnt      = &e->m_book.m_bid_levels;
        resting_is_bid  = true;
    }

    int trades_this_call = 0;

    while (incoming->m_remaining_qty > 0) {
        PriceLevel *lvl = *contra_head_ptr;
        if (!lvl) break;
        if (!can_match(incoming, lvl->m_price)) break;

        while (incoming->m_remaining_qty > 0 && lvl->m_head) {
            Order *resting = lvl->m_head;

            /* STP check */
            if (ME_UNLIKELY(stp_conflict(incoming, resting))) {
                bool stop_incoming = handle_stp(e, incoming, resting, lvl, resting_is_bid);
                /* lvl may have been removed from book if it became empty — re-fetch */
                if (stop_incoming) goto match_done;
                /* resting was removed; re-check head of this level */
                /* Note: if lvl was removed, *contra_head_ptr changed; outer while handles that */
                break; /* re-enter outer while to re-check head level */
            }

            Quantity fill = qty_min(incoming->m_remaining_qty, resting->m_visible_qty);

            /* Generate trade (EP-1: passive price) */
            emit_trade(e, resting->m_price, fill,
                       incoming->m_id, resting->m_id, incoming->m_side);
            trades_this_call++;

            incoming->m_remaining_qty -= fill;
            resting->m_visible_qty    -= fill;
            resting->m_remaining_qty  -= fill;

            /* Update resting status */
            if (resting->m_remaining_qty < resting->m_original_qty) {
                resting->m_status = STATUS_PARTIALLY_FILLED;
            }

            /* Handle iceberg reload */
            if (resting->m_visible_qty == 0 && resting->m_remaining_qty > 0) {
                if (resting->m_display_qty != QTY_NULL) {
                    /* Reload: lose time priority, move to back */
                    resting->m_visible_qty = qty_min(resting->m_display_qty,
                                                      resting->m_remaining_qty);
                    resting->m_timestamp = e->m_clock++;
                    level_move_to_back(lvl, resting);
                    /* Continue matching (resting is now at back; don't remove it) */
                } else {
                    /* Non-iceberg fully consumed visible = fully consumed */
                    /* This path should not happen (visible == remaining for non-iceberg) */
                }
            }

            /* Remove fully filled resting order */
            if (resting->m_remaining_qty == 0) {
                resting->m_status = STATUS_FILLED;
                level_remove(lvl, resting);
                index_clear(e, resting->m_id);
                order_pool_free(&e->m_order_pool, resting);
            }
        } /* inner while: orders within level */

        /* Clean up empty level */
        if (lvl->m_count == 0 && lvl == *contra_head_ptr) {
            book_remove_level(e, contra_head_ptr, contra_cnt, lvl);
        }
    } /* outer while: price levels */

match_done:
    /* Clean up any empty level at the contra head (e.g., after STP CANCEL_BOTH) */
    {
        PriceLevel *top = *contra_head_ptr;
        if (top && top->m_count == 0) {
            book_remove_level(e, contra_head_ptr, contra_cnt, top);
        }
    }
    return trades_this_call;
}

/* =========================================================================
 * DISPOSE: post-match remainder handling
 * ========================================================================= */

static void dispose(MatchingEngine *e, Order *o, bool had_trades) {
    /* If order was already cancelled/filled (e.g. by STP), don't override */
    if (o->m_status == STATUS_CANCELLED || o->m_status == STATUS_REJECTED) {
        return;
    }

    if (o->m_remaining_qty == 0) {
        o->m_status = STATUS_FILLED;
        return;
    }

    switch (o->m_tif) {
    case TIF_IOC: {
        o->m_status = STATUS_CANCELLED;
        EvtCancelled ev = { o, CANCEL_IOC_REMAINDER };
        emit(e, EVT_ORDER_CANCELLED, &ev);
        break;
    }
    case TIF_FOK:
        /* FOK remainder: should not reach here (pre-check ensures full fill or reject) */
        o->m_status = STATUS_CANCELLED;
        {
            EvtCancelled ev = { o, CANCEL_FOK_NOT_SATISFIABLE };
            emit(e, EVT_ORDER_CANCELLED, &ev);
        }
        break;

    case TIF_GTC:
    case TIF_GTD:
    case TIF_DAY:
        if (o->m_order_type == ORDER_TYPE_MARKET) {
            /* MARKET orders never rest */
            o->m_status = STATUS_CANCELLED;
            EvtCancelled ev = { o, CANCEL_MARKET_NO_FULL_FILL };
            emit(e, EVT_ORDER_CANCELLED, &ev);
        } else {
            insert_into_book(e, o);
            o->m_status = had_trades ? STATUS_PARTIALLY_FILLED : STATUS_NEW;
        }
        break;
    }
}

/* =========================================================================
 * Post-only check (REJECT policy as spec requires)
 * Returns true if order was rejected/cancelled (caller should not proceed).
 * ========================================================================= */

static bool post_only_check(MatchingEngine *e, Order *o) {
    PriceLevel *contra;
    if (o->m_side == SIDE_BUY)  contra = e->m_book.m_asks_head;
    else                         contra = e->m_book.m_bids_head;

    if (!contra) return false; /* no contra side; OK to proceed */

    bool would_cross;
    if (o->m_side == SIDE_BUY)  would_cross = (o->m_price >= contra->m_price);
    else                         would_cross = (o->m_price <= contra->m_price);

    if (would_cross) {
        o->m_status = STATUS_CANCELLED;
        EvtCancelled ev = { o, CANCEL_POST_ONLY_WOULD_CROSS };
        emit(e, EVT_ORDER_CANCELLED, &ev);
        return true;
    }
    return false;
}

/* =========================================================================
 * shouldTriggerImmediately: does a stop fire right now?
 * ========================================================================= */

/* =========================================================================
 * Evaluate and fire stops after each trade
 * ========================================================================= */

static void evaluate_stops(MatchingEngine *e, Price last_trade_price) {
    if (ME_LIKELY(e->m_book.m_stop_count == 0)) return;
    /* Fast path: check if trade price could trigger ANY stop */
    if (ME_LIKELY(last_trade_price < e->m_book.m_min_buy_stop &&
                  last_trade_price > e->m_book.m_max_sell_stop)) return;
    if (ME_UNLIKELY(e->m_cascade_depth >= MAX_CASCADE_DEPTH)) return;

    /* Collect triggered stops into a local array, then sort by timestamp.
     * Scan both unsorted lists fully — O(stop_count).
     * In practice stop lists are small (< few thousand).
     */
    Order *triggered[MAX_TRIGGERED_STOPS]; /* stack-allocated: safe for recursion */
    int n_triggered = 0;

    /* BUY stops: trigger when trade_price >= stop_price */
    {
        Order **pp = &e->m_book.m_buy_stops_head;
        while (*pp && n_triggered < MAX_TRIGGERED_STOPS) {
            Order *stop = *pp;
            if (last_trade_price >= stop->m_stop_price) {
                /* Remove from list */
                *pp = stop->m_next;
                if (stop->m_next) stop->m_next->m_prev = stop->m_prev;
                stop->m_prev = stop->m_next = NULL;
                e->m_book.m_stop_count--;
                triggered[n_triggered++] = stop;
            } else {
                pp = &stop->m_next;
            }
        }
    }

    /* SELL stops: trigger when trade_price <= stop_price */
    {
        Order **pp = &e->m_book.m_sell_stops_head;
        while (*pp && n_triggered < MAX_TRIGGERED_STOPS) {
            Order *stop = *pp;
            if (last_trade_price <= stop->m_stop_price) {
                *pp = stop->m_next;
                if (stop->m_next) stop->m_next->m_prev = stop->m_prev;
                stop->m_prev = stop->m_next = NULL;
                e->m_book.m_stop_count--;
                triggered[n_triggered++] = stop;
            } else {
                pp = &stop->m_next;
            }
        }
    }

    if (n_triggered == 0) return;

    /* Recompute min_buy_stop and max_sell_stop after removals */
    {
        Price min_b = PRICE_NULL;
        for (Order *s = e->m_book.m_buy_stops_head; s; s = s->m_next)
            if (s->m_stop_price < min_b) min_b = s->m_stop_price;
        e->m_book.m_min_buy_stop = min_b;

        Price max_s = 0;
        for (Order *s = e->m_book.m_sell_stops_head; s; s = s->m_next)
            if (s->m_stop_price > max_s) max_s = s->m_stop_price;
        e->m_book.m_max_sell_stop = max_s;
    }

    /* Sort triggered stops by arrival timestamp (insertion sort; n is typically tiny) */
    for (int i = 1; i < n_triggered; i++) {
        Order *key = triggered[i];
        int j = i - 1;
        while (j >= 0 && triggered[j]->m_timestamp > key->m_timestamp) {
            triggered[j + 1] = triggered[j];
            j--;
        }
        triggered[j + 1] = key;
    }

    e->m_cascade_depth++;
    for (int i = 0; i < n_triggered; i++) {
        Order *stop = triggered[i];
        stop->m_status = STATUS_TRIGGERED;
        emit(e, EVT_ORDER_TRIGGERED, stop);

        /* Convert to base type */
        if (stop->m_order_type == ORDER_TYPE_STOP_LIMIT) {
            stop->m_order_type = ORDER_TYPE_LIMIT;
        } else {
            stop->m_order_type = ORDER_TYPE_MARKET;
        }
        stop->m_stop_price = PRICE_NULL;

        /* BUG-1 fix: assign new timestamp before re-entering pipeline to preserve FIFO */
        stop->m_timestamp = e->m_clock++;

        /* Index is already set (stop orders remain in index while dormant) */

        process_order_internal(e, stop);
    }
    e->m_cascade_depth--;
}

/* =========================================================================
 * MTL (Market-to-Limit) processing
 * ========================================================================= */

static void process_mtl(MatchingEngine *e, Order *o) {
    /* Phase 1: match like MARKET (can_match always true for MTL) */
    int n = do_match(e, o);

    if (n == 0) {
        /* No trades: cancel */
        o->m_status = STATUS_CANCELLED;
        EvtCancelled ev = { o, CANCEL_MTL_NO_LIQUIDITY };
        emit(e, EVT_ORDER_CANCELLED, &ev);

        /* Emit stops for any trades (none here) */
        return;
    }

    /* Get the price of the first trade (last n trades are in ring buffer) */
    /* The first trade from this batch is at position tail - n */
    uint32_t first_idx = (e->m_trade_buf.m_tail - (uint32_t)n) % POOL_TRADE_CAPACITY;
    Price first_price = e->m_trade_buf.m_trades[first_idx].m_price;

    /* Convert to LIMIT at the locked price */
    o->m_price     = first_price;
    o->m_order_type = ORDER_TYPE_LIMIT;

    /* Clear minQty */
    o->m_min_qty = QTY_NULL;

    /* Match remainder at the locked price */
    if (o->m_remaining_qty > 0) {
        int n2 = do_match(e, o);
        n += n2;
    }

    /* Dispose remainder */
    dispose(e, o, n > 0);

    /* Emit trades and evaluate stops */
    uint32_t base_idx = (e->m_trade_buf.m_tail - (uint32_t)n) % POOL_TRADE_CAPACITY;
    for (int i = 0; i < n; i++) {
        uint32_t idx = (base_idx + (uint32_t)i) % POOL_TRADE_CAPACITY;
        evaluate_stops(e, e->m_trade_buf.m_trades[idx].m_price);
    }
}

/* =========================================================================
 * Internal PROCESS pipeline
 * ========================================================================= */

static void process_order_internal(MatchingEngine *e, Order *o) {
    /* Phase 1: Stop order routing */
    if (o->m_order_type == ORDER_TYPE_STOP_LIMIT ||
        o->m_order_type == ORDER_TYPE_STOP_MARKET) {
        /* Dormant stop orders remain in the main order_index so cancellation
         * is O(1). engine_find_order returns them while dormant. */
        ME_Result r = stops_add(e, o);
        (void)r;
        return;
    }

    /* Phase 2: Post-only check */
    if (o->m_post_only) {
        if (post_only_check(e, o)) {
            /* Order cancelled; release resources */
            index_clear(e, o->m_id);
            order_pool_free(&e->m_order_pool, o);
            return;
        }
        /* Post-only and no crossing: insert directly (no matching) */
        insert_into_book(e, o);
        o->m_status = STATUS_NEW;
        return;
    }

    /* Phase 3: FOK pre-check */
    if (o->m_tif == TIF_FOK) {
        if (!qty_precheck(e, o, o->m_original_qty)) {
            o->m_status = STATUS_CANCELLED;
            EvtCancelled ev = { o, CANCEL_FOK_NOT_SATISFIABLE };
            emit(e, EVT_ORDER_CANCELLED, &ev);
            index_clear(e, o->m_id);
            order_pool_free(&e->m_order_pool, o);
            return;
        }
    }

    /* min_qty pre-check */
    if (o->m_min_qty != QTY_NULL) {
        if (!qty_precheck(e, o, o->m_min_qty)) {
            o->m_status = STATUS_CANCELLED;
            EvtCancelled ev = { o, CANCEL_MIN_QTY };
            emit(e, EVT_ORDER_CANCELLED, &ev);
            index_clear(e, o->m_id);
            order_pool_free(&e->m_order_pool, o);
            return;
        }
    }

    /* Phase 4: MTL routing */
    if (o->m_order_type == ORDER_TYPE_MARKET_TO_LIMIT) {
        process_mtl(e, o);
        return;
    }

    /* Phase 5: MATCH */
    /* Record tail before matching to know how many trades were added */
    uint32_t tail_before = e->m_trade_buf.m_tail;
    int n = do_match(e, o);

    /* Phase 5a: Clear minQty after successful matching */
    if (o->m_min_qty != QTY_NULL && n > 0) {
        o->m_min_qty = QTY_NULL;
    }

    /* Phase 6: DISPOSE */
    dispose(e, o, n > 0);

    /* Phase 7: Emit stops for each trade */
    for (int i = 0; i < n; i++) {
        uint32_t idx = (tail_before + (uint32_t)i) % POOL_TRADE_CAPACITY;
        evaluate_stops(e, e->m_trade_buf.m_trades[idx].m_price);
    }

    /* Phase 8: book updates — we emit via EVT_BOOK_UPDATE (no-op in this impl,
     * actual book state is always current). */

    /* If order was cancelled/rejected during matching (e.g. STP), free it.
     * Orders that rest on the book are owned by the level queue. */
    if (o->m_status == STATUS_CANCELLED ||
        o->m_status == STATUS_REJECTED  ||
        o->m_status == STATUS_FILLED) {
        /* Only free if not already on book (m_level == NULL means not resting) */
        if (!o->m_level) {
            index_clear(e, o->m_id);
            order_pool_free(&e->m_order_pool, o);
        }
    }
}

/* =========================================================================
 * engine_init
 * ========================================================================= */

void engine_init(MatchingEngine *e, EventCallback cb, void *ctx) {
    /* Zero only the metadata, not the large pool storage arrays.
     * Callers are expected to either calloc the engine (heap) or
     * use a global/static that is zero-initialised.
     * We explicitly reset all hot-path state fields. */
    e->m_book.m_bids_head       = NULL;
    e->m_book.m_asks_head       = NULL;
    e->m_book.m_buy_stops_head  = NULL;
    e->m_book.m_sell_stops_head = NULL;
    e->m_book.m_min_buy_stop    = PRICE_NULL;
    e->m_book.m_max_sell_stop   = 0;
    e->m_book.m_bid_levels      = 0;
    e->m_book.m_ask_levels      = 0;
    e->m_book.m_stop_count      = 0;
    e->m_book.m_pad             = 0;

    /* Zero the order index (8 MB — fast) */
    memset(e->m_order_index, 0, sizeof(e->m_order_index));

    order_pool_init(&e->m_order_pool);
    level_pool_init(&e->m_level_pool);
    trade_buf_init(&e->m_trade_buf);

    e->m_clock          = 1;
    e->m_trade_id_seq   = 0;
    e->m_next_order_id  = 1;
    e->m_cascade_depth  = 0;
    e->m_callback       = cb;
    e->m_callback_ctx   = ctx;
}

/* =========================================================================
 * engine_process
 * ========================================================================= */

ME_Result engine_process(MatchingEngine *restrict e, const OrderDesc *restrict desc) {
    /* Phase 0: Validation */
    RejectReason rej = validate_order(e, desc);
    if (ME_UNLIKELY(rej != 0)) {
        /* We still need an Order to emit the rejection event.
         * Allocate a temporary one. */
        Order *tmp = order_pool_alloc(&e->m_order_pool);
        if (!tmp) return ME_ERR_POOL_FULL;
        memset(tmp, 0, sizeof(*tmp));
        tmp->m_id         = desc->id ? desc->id : e->m_next_order_id;
        tmp->m_side       = desc->side;
        tmp->m_order_type = desc->order_type;
        tmp->m_tif        = desc->tif;
        tmp->m_price      = desc->price;
        tmp->m_original_qty = desc->quantity;
        tmp->m_remaining_qty = desc->quantity;
        tmp->m_status     = STATUS_REJECTED;
        EvtRejected ev = { tmp, rej };
        emit(e, EVT_ORDER_REJECTED, &ev);
        order_pool_free(&e->m_order_pool, tmp);
        return ME_ERR_INVALID;
    }

    /* Allocate order */
    Order *o = order_pool_alloc(&e->m_order_pool);
    if (ME_UNLIKELY(!o)) return ME_ERR_POOL_FULL;

    /* Populate order from descriptor */
    OrderId assigned_id;
    if (desc->id) {
        assigned_id = desc->id;
        if (assigned_id > MAX_ORDER_ID || index_get(e, assigned_id) != NULL) {
            order_pool_free(&e->m_order_pool, o);
            return ME_ERR_INVALID;
        }
    } else {
        /* Auto-assign: try free-ID stack (O(1)), fall back to linear scan */
        if (e->m_id_free_count > 0) {
            assigned_id = e->m_id_free_stack[--e->m_id_free_count];
        } else {
            assigned_id = e->m_next_order_id;
            if (assigned_id > MAX_ORDER_ID) {
                /* Wrap and scan — should be rare with free-stack */
                assigned_id = 1;
                uint32_t tries = 0;
                while (index_get(e, assigned_id) != NULL) {
                    assigned_id++;
                    if (++tries > MAX_ORDER_ID) {
                        order_pool_free(&e->m_order_pool, o);
                        return ME_ERR_POOL_FULL;
                    }
                }
            }
            e->m_next_order_id = assigned_id + 1;
        }
    }

    /* Direct field init — avoids 128-byte memset that was causing
     * 19.8% of all LL write misses (756K per run). */
    o->m_price        = desc->price;
    o->m_side         = desc->side;
    o->m_order_type   = desc->order_type;
    o->m_stp_group    = desc->stp_group;
    o->m_stp_policy   = desc->stp_policy;
    o->m_status       = STATUS_NEW;
    o->m_remaining_qty = desc->quantity;
    o->m_display_qty  = desc->display_qty;
    o->m_next         = NULL;
    o->m_prev         = NULL;
    o->m_level        = NULL;
    o->m_stop_price   = desc->stop_price;
    o->m_original_qty = desc->quantity;
    o->m_min_qty      = desc->min_qty;
    o->m_timestamp    = e->m_clock++;
    o->m_expire_time  = desc->expire_time;
    o->m_id           = assigned_id;
    o->m_tif          = desc->tif;
    o->m_post_only    = desc->post_only;

    /* WF-12: initial visible qty */
    if (o->m_display_qty != QTY_NULL)
        o->m_visible_qty = qty_min(o->m_display_qty, o->m_remaining_qty);
    else
        o->m_visible_qty = o->m_remaining_qty;

    /* Register in index */
    index_set(e, assigned_id, o);

    emit(e, EVT_ORDER_ACCEPTED, o);

    /* Enter pipeline */
    process_order_internal(e, o);

    return ME_OK;
}

/* =========================================================================
 * engine_cancel
 * ========================================================================= */

ME_Result engine_cancel(MatchingEngine *restrict e, OrderId id) {
    Order *o = index_get(e, id);
    if (!o) return ME_ERR_NOT_FOUND;

    /* Handle dormant stop orders via intrusive list (O(1) removal) */
    if (o->m_order_type == ORDER_TYPE_STOP_LIMIT ||
        o->m_order_type == ORDER_TYPE_STOP_MARKET) {
        stops_remove(e, o);
        o->m_status = STATUS_CANCELLED;
        EvtCancelled ev = { o, CANCEL_USER_REQUESTED };
        emit(e, EVT_ORDER_CANCELLED, &ev);
        index_clear(e, id);
        order_pool_free(&e->m_order_pool, o);
        return ME_OK;
    }

    if (o->m_status != STATUS_NEW && o->m_status != STATUS_PARTIALLY_FILLED) {
        return ME_ERR_INVALID;
    }

    /* Remove from book level */
    remove_order_from_level(e, o, false);

    o->m_status = STATUS_CANCELLED;
    EvtCancelled ev = { o, CANCEL_USER_REQUESTED };
    emit(e, EVT_ORDER_CANCELLED, &ev);

    index_clear(e, id);
    order_pool_free(&e->m_order_pool, o);
    return ME_OK;
}

/* =========================================================================
 * engine_amend
 * ========================================================================= */

ME_Result engine_amend(MatchingEngine *restrict e, const AmendDesc *restrict desc) {
    Order *o = index_get(e, desc->id);
    if (!o) return ME_ERR_NOT_FOUND;

    if (o->m_status != STATUS_NEW && o->m_status != STATUS_PARTIALLY_FILLED) {
        return ME_ERR_INVALID;
    }

    bool is_stop = (o->m_order_type == ORDER_TYPE_STOP_LIMIT ||
                    o->m_order_type == ORDER_TYPE_STOP_MARKET);

    bool price_changed = (desc->new_price != PRICE_NULL && desc->new_price != o->m_price);
    bool qty_increased = (desc->new_qty != QTY_NULL && desc->new_qty > o->m_remaining_qty);
    bool qty_decreased = (desc->new_qty != QTY_NULL && desc->new_qty < o->m_remaining_qty);

    if (qty_decreased && !price_changed) {
        /* Keep priority: just reduce qty */
        o->m_remaining_qty = desc->new_qty;
        if (o->m_visible_qty > desc->new_qty)
            o->m_visible_qty = desc->new_qty;
        return ME_OK;
    }

    if (price_changed || qty_increased) {
        /* For dormant stop orders: remove from stop list before re-processing */
        if (is_stop) {
            stops_remove(e, o);
            o->m_prev = o->m_next = NULL;
        } else {
            /* Remove from price level */
            remove_order_from_level(e, o, false);
        }

        if (desc->new_price != PRICE_NULL) o->m_price = desc->new_price;
        if (desc->new_qty   != QTY_NULL)  {
            o->m_remaining_qty = desc->new_qty;
            o->m_original_qty  = desc->new_qty;
        }

        /* New timestamp — lose time priority */
        o->m_timestamp = e->m_clock++;

        /* Recalculate visible qty */
        if (o->m_display_qty != QTY_NULL)
            o->m_visible_qty = qty_min(o->m_display_qty, o->m_remaining_qty);
        else
            o->m_visible_qty = o->m_remaining_qty;

        o->m_status = STATUS_NEW;
        o->m_level  = NULL;

        /* Re-enter full pipeline */
        process_order_internal(e, o);
    }

    return ME_OK;
}

/* =========================================================================
 * engine_expire
 * ========================================================================= */

int engine_expire(MatchingEngine *restrict e, Timestamp now) {
    int count = 0;

    /* Expire bids */
    PriceLevel *lvl = e->m_book.m_bids_head;
    while (lvl) {
        PriceLevel *next_lvl = lvl->m_next;
        Order *o = lvl->m_head;
        while (o) {
            Order *next_o = o->m_next;
            bool should_expire = false;
            if (o->m_tif == TIF_GTD && now >= o->m_expire_time) should_expire = true;
            if (should_expire) {
                level_remove(lvl, o);
                o->m_status = STATUS_EXPIRED;
                emit(e, EVT_ORDER_EXPIRED, o);
                index_clear(e, o->m_id);
                order_pool_free(&e->m_order_pool, o);
                count++;
            }
            o = next_o;
        }
        if (lvl->m_count == 0) {
            book_remove_level(e, &e->m_book.m_bids_head, &e->m_book.m_bid_levels, lvl);
        }
        lvl = next_lvl;
    }

    /* Expire asks */
    lvl = e->m_book.m_asks_head;
    while (lvl) {
        PriceLevel *next_lvl = lvl->m_next;
        Order *o = lvl->m_head;
        while (o) {
            Order *next_o = o->m_next;
            bool should_expire = false;
            if (o->m_tif == TIF_GTD && now >= o->m_expire_time) should_expire = true;
            if (should_expire) {
                level_remove(lvl, o);
                o->m_status = STATUS_EXPIRED;
                emit(e, EVT_ORDER_EXPIRED, o);
                index_clear(e, o->m_id);
                order_pool_free(&e->m_order_pool, o);
                count++;
            }
            o = next_o;
        }
        if (lvl->m_count == 0) {
            book_remove_level(e, &e->m_book.m_asks_head, &e->m_book.m_ask_levels, lvl);
        }
        lvl = next_lvl;
    }

    return count;
}

/* =========================================================================
 * engine_find_order
 * ========================================================================= */

const Order *engine_find_order(const MatchingEngine *e, OrderId id) {
    return index_get(e, id);
}

/* =========================================================================
 * engine_best_bid / engine_best_ask
 * ========================================================================= */

Price engine_best_bid(const MatchingEngine *e) {
    return e->m_book.m_bids_head ? e->m_book.m_bids_head->m_price : PRICE_NULL;
}

Price engine_best_ask(const MatchingEngine *e) {
    return e->m_book.m_asks_head ? e->m_book.m_asks_head->m_price : PRICE_NULL;
}

/* =========================================================================
 * engine_check_invariants
 * ========================================================================= */

void engine_check_invariants(const MatchingEngine *e) {
#ifndef NDEBUG
    /* INV-1, INV-2: No empty bid levels; strictly descending */
    Price prev_bid = UINT64_MAX;
    for (PriceLevel *l = e->m_book.m_bids_head; l; l = l->m_next) {
        assert(l->m_count > 0 && "INV-1: empty bid level");
        assert(l->m_price < prev_bid && "INV-3: bids not strictly descending");
        prev_bid = l->m_price;

        /* INV-6, INV-7, INV-8 per order */
        Timestamp prev_ts = 0;
        for (Order *o = l->m_head; o; o = o->m_next) {
            assert(o->m_remaining_qty > 0 && "INV-6: zero remaining on book");
            assert((o->m_status == STATUS_NEW || o->m_status == STATUS_PARTIALLY_FILLED) &&
                   "INV-7: bad status on book");
            assert(o->m_order_type != ORDER_TYPE_MARKET && "INV-8: market on book");
            assert(o->m_timestamp >= prev_ts && "INV-8(FIFO): timestamp not monotone");
            prev_ts = o->m_timestamp;
            assert(o->m_min_qty == QTY_NULL && "INV-14: resting order has min_qty");
        }
    }

    /* INV-1 (asks), INV-3: strictly ascending */
    Price prev_ask = 0;
    for (PriceLevel *l = e->m_book.m_asks_head; l; l = l->m_next) {
        assert(l->m_count > 0 && "INV-2: empty ask level");
        assert(l->m_price > prev_ask && "INV-4: asks not strictly ascending");
        prev_ask = l->m_price;

        Timestamp prev_ts = 0;
        for (Order *o = l->m_head; o; o = o->m_next) {
            assert(o->m_remaining_qty > 0 && "INV-6: zero remaining on book");
            assert((o->m_status == STATUS_NEW || o->m_status == STATUS_PARTIALLY_FILLED) &&
                   "INV-7: bad status on book");
            assert(o->m_order_type != ORDER_TYPE_MARKET && "INV-8: market on book");
            assert(o->m_timestamp >= prev_ts && "INV-8(FIFO): timestamp not monotone");
            prev_ts = o->m_timestamp;
            assert(o->m_min_qty == QTY_NULL && "INV-14: resting order has min_qty");
        }
    }

    /* INV-5: no crossed book */
    if (e->m_book.m_bids_head && e->m_book.m_asks_head) {
        assert(e->m_book.m_bids_head->m_price < e->m_book.m_asks_head->m_price &&
               "INV-5: crossed book");
    }
#else
    (void)e;
#endif
}
