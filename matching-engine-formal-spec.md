# Formal Specification: Price-Time Priority Matching Engine

**Version:** 1.2.0
**Scope:** Generic asset-agnostic order matching with full order type suite
**Algorithm:** Price-Time Priority (FIFO)

---

## 1. Foundational Types & Domains

### 1.1 Primitive Domains

```
Price       ∈ ℚ⁺           -- Strictly positive rational number (represented as fixed-point decimal)
Quantity    ∈ ℤ⁺           -- Strictly positive integer (in lot units)
Timestamp  ∈ ℕ             -- Monotonically increasing, nanosecond-precision logical clock
OrderId    ∈ ℕ             -- Unique, monotonically increasing per engine instance
InstrumentId ∈ 𝕊           -- Opaque instrument identifier string
```

### 1.2 Enumerated Types

```
Side        = { BUY, SELL }
OrderType   = { LIMIT, MARKET, MARKET_TO_LIMIT, STOP_LIMIT, STOP_MARKET }
TimeInForce = { GTC, GTD, IOC, FOK, DAY }
OrderStatus = { NEW, PARTIALLY_FILLED, FILLED, CANCELLED, REJECTED, EXPIRED, TRIGGERED }
STPPolicy   = { CANCEL_NEWEST, CANCEL_OLDEST, CANCEL_BOTH, DECREMENT }
```

### 1.3 Derived Types

```
oppositeSide : Side → Side
oppositeSide(BUY)  = SELL
oppositeSide(SELL)  = BUY
```

---

## 2. Order Model

### 2.1 Order Definition

An Order is a tuple:

```
Order = (
    id            : OrderId,
    instrumentId  : InstrumentId,
    side          : Side,
    orderType     : OrderType,
    timeInForce   : TimeInForce,
    price         : Price ∪ {⊥},          -- ⊥ (null) for MARKET orders
    stopPrice     : Price ∪ {⊥},          -- ⊥ for non-stop orders
    quantity      : Quantity,              -- Original quantity
    remainingQty  : Quantity,              -- Unfilled quantity; remainingQty ≤ quantity
    minQty        : Quantity ∪ {⊥},        -- ⊥ if no minimum; applies to FIRST fill only
    displayQty    : Quantity ∪ {⊥},        -- ⊥ if not iceberg; displayQty ≤ quantity
    visibleQty    : Quantity,              -- Currently visible slice; visibleQty ≤ remainingQty
    postOnly      : bool,                  -- If true, order MUST NOT aggress (add liquidity only)
    status        : OrderStatus,
    timestamp     : Timestamp,             -- Arrival time (determines priority)
    expireTime    : Timestamp ∪ {⊥},       -- ⊥ if not GTD
    selfTradeGroup: SelfTradeGroup ∪ {⊥},  -- ⊥ if no self-trade prevention
    stpPolicy     : STPPolicy ∪ {⊥}       -- ⊥ if selfTradeGroup = ⊥; policy per-order
)
```

### 2.2 Order Validity Constraints (Preconditions for Acceptance)

An order `o` is **well-formed** iff ALL of the following hold:

```
WF-1:  o.quantity > 0
WF-2:  o.orderType = LIMIT ⟹ o.price ≠ ⊥ ∧ o.price > 0
WF-2a: o.orderType = STOP_LIMIT ⟹ o.price ≠ ⊥ ∧ o.price > 0
WF-2b: o.orderType = MARKET_TO_LIMIT ⟹ o.price = ⊥     -- Price derived from first fill
WF-3:  o.orderType ∈ {MARKET, STOP_MARKET} ⟹ o.price = ⊥
WF-4:  o.orderType ∈ {STOP_LIMIT, STOP_MARKET} ⟹ o.stopPrice ≠ ⊥ ∧ o.stopPrice > 0
WF-5:  o.orderType ∈ {LIMIT, MARKET, MARKET_TO_LIMIT} ⟹ o.stopPrice = ⊥
WF-6:  o.timeInForce = GTD ⟹ o.expireTime ≠ ⊥ ∧ o.expireTime > currentTime
WF-7:  o.timeInForce ≠ GTD ⟹ o.expireTime = ⊥
WF-8:  o.orderType = MARKET ⟹ o.timeInForce ∈ {IOC, FOK}
WF-8a: o.orderType = MARKET_TO_LIMIT ⟹ o.timeInForce ∈ {GTC, DAY}
        -- MTL must be able to rest; IOC/FOK incompatible with "convert remainder" semantics
        -- Note: GTD is excluded; expiry semantics are modeled only via DAY session close
WF-9:  o.displayQty ≠ ⊥ ⟹ o.displayQty > 0 ∧ o.displayQty ≤ o.quantity
WF-10: o.displayQty ≠ ⊥ ⟹ o.orderType = LIMIT    -- Icebergs must be LIMIT
WF-11: o.remainingQty = o.quantity                   -- At creation
WF-12: o.visibleQty = min(o.displayQty, o.quantity) if o.displayQty ≠ ⊥ else o.quantity

-- Post-Only constraints
WF-13: o.postOnly = true ⟹ o.orderType = LIMIT
        -- Post-only only makes sense for LIMIT orders (must have a price to rest at)
WF-14: o.postOnly = true ⟹ o.timeInForce ∉ {IOC, FOK}
        -- IOC/FOK are aggressor-only semantics; contradicts post-only
WF-15: o.orderType ∈ {MARKET, MARKET_TO_LIMIT} ⟹ o.postOnly = false
        -- MARKET and MTL are inherently aggressive

-- Self-Trade Prevention constraints
WF-16: o.selfTradeGroup = ⊥ ⟺ o.stpPolicy = ⊥
        -- Both must be present or both absent
WF-17: o.stpPolicy ≠ ⊥ ⟹ o.stpPolicy ∈ {CANCEL_NEWEST, CANCEL_OLDEST, CANCEL_BOTH, DECREMENT}

-- Minimum Quantity constraints
WF-18: o.minQty ≠ ⊥ ⟹ o.minQty > 0 ∧ o.minQty ≤ o.quantity
WF-19: o.minQty ≠ ⊥ ⟹ o.postOnly = false
        -- Post-only never fills as aggressor; minQty requires an initial fill
WF-20: o.timeInForce = FOK ⟹ o.minQty = ⊥
        -- FOK subsumes minQty (FOK ≡ minQty = quantity); redundant, so disallowed
```

**Rejection Rule:** If ¬WellFormed(o), emit `REJECT(o, reason)` and discard.

---

## 3. Order Book Model

### 3.1 Book Structure

For each instrument `i`, the Order Book is:

```
Book(i) = (
    bids : PriceLevel list,    -- Sorted DESCENDING by price (best bid first)
    asks : PriceLevel list,    -- Sorted ASCENDING by price (best ask first)
    stops: StopOrder set       -- Unordered collection of resting stop orders
)

PriceLevel = (
    price  : Price,
    orders : Order queue       -- FIFO queue; front = highest time priority
)
```

### 3.2 Book Accessor Functions

```
bestBid(Book)  = head(Book.bids).price   if Book.bids ≠ ∅, else ⊥
bestAsk(Book)  = head(Book.asks).price   if Book.asks ≠ ∅, else ⊥
spread(Book)   = bestAsk(Book) - bestBid(Book)   if both ≠ ⊥, else ⊥

-- Select the correct side of the book
sameSide(Book, BUY)  = Book.bids
sameSide(Book, SELL) = Book.asks
oppSide(Book, side)  = sameSide(Book, oppositeSide(side))
```

### 3.3 Book Invariants (must hold at ALL times)

```
INV-1:  ∀ level ∈ Book.bids ∪ Book.asks: level.orders ≠ ∅
        -- No empty price levels remain in the book
INV-2:  ∀ consecutive (L1, L2) ∈ Book.bids: L1.price > L2.price
        -- Strict descending order
INV-3:  ∀ consecutive (L1, L2) ∈ Book.asks: L1.price < L2.price
        -- Strict ascending order
INV-4:  bestBid(Book) < bestAsk(Book) ∨ bestBid(Book) = ⊥ ∨ bestAsk(Book) = ⊥
        -- No crossed book (after matching completes)
INV-5:  ∀ order ∈ Book: order.remainingQty > 0
        -- Fully filled orders never rest on the book
INV-6:  ∀ order ∈ Book: order.status ∈ {NEW, PARTIALLY_FILLED}
INV-7:  ∀ level ∈ Book.bids ∪ Book.asks,
        ∀ (o1, o2) consecutive in level.orders:
            o1.timestamp < o2.timestamp
        -- FIFO within price level
```

---

## 4. Execution Model

### 4.1 Trade / Fill

A Trade (also called Execution or Fill) is produced when an incoming (aggressor) order matches a resting (passive) order:

```
Trade = (
    tradeId       : TradeId,
    instrumentId  : InstrumentId,
    price         : Price,           -- Execution price (always the PASSIVE order's price)
    quantity      : Quantity,
    aggressorId   : OrderId,         -- The incoming order
    passiveId     : OrderId,         -- The resting order
    aggressorSide : Side,
    timestamp     : Timestamp
)
```

### 4.2 Execution Price Rule

**RULE EP-1 (Price Improvement / Passive Price):**

```
executionPrice(aggressor, passive) = passive.price
```

The resting (passive) order always determines the trade price. This guarantees price improvement for the aggressor when crossing a spread.

### 4.3 Event Emissions

The engine emits an ordered stream of events:

```
Event = OrderAccepted(Order)
      | OrderRejected(Order, Reason)
      | TradeExecuted(Trade)
      | OrderCancelled(Order, Reason)
      | OrderExpired(Order)
      | OrderTriggered(Order)          -- Stop order activated
      | OrderRepriced(Order, Price, Price)  -- Post-only slide (old, new price)
      | OrderDecremented(Order, Order, Quantity)  -- STP decrement (incoming, resting, qty)
      | BookUpdate(Side, PriceLevel)   -- Market data
```

**Event Ordering Guarantee:** Events for a single incoming order are emitted in causal order. TradeExecuted events are emitted in match sequence (best price first, then FIFO within price).

---

## 5. Matching Algorithm: Price-Time Priority (FIFO)

### 5.1 Core Matching Procedure

```
MATCH(Book, incomingOrder) → (Trade list, Book', Order')

Given:
    incoming = incomingOrder
    book     = Book
    trades   = []

Step 1 — Determine matchable side:
    contra = oppSide(book, incoming.side)

Step 2 — Price compatibility predicate:
    canMatch(incoming, resting) =
        CASE incoming.side OF
            BUY  → incoming.price ≥ resting.price   (if incoming has price)
            SELL → incoming.price ≤ resting.price   (if incoming has price)
        -- MARKET orders: canMatch = true (always matches, any price)
        -- LIMIT orders: canMatch uses the limit price

Step 3 — Iterate through contra levels (best price first):
    WHILE incoming.remainingQty > 0 AND contra ≠ ∅:
        level = head(contra)

        IF ¬canMatch(incoming, level.price):
            BREAK   -- No more matchable levels

        WHILE incoming.remainingQty > 0 AND level.orders ≠ ∅:
            resting = front(level.orders)

            -- Self-trade prevention check
            IF selfTradeConflict(incoming, resting):
                HANDLE_STP(incoming, resting, book)   -- See §8.3
                CONTINUE

            -- Determine fill quantity
            fillQty = min(incoming.remainingQty, resting.visibleQty)

            -- Generate trade
            trade = Trade(
                price    = resting.price,     -- EP-1: passive price
                quantity = fillQty,
                ...
            )
            APPEND trade TO trades

            -- Update quantities
            incoming.remainingQty -= fillQty
            resting.visibleQty   -= fillQty
            resting.remainingQty -= fillQty

            -- Handle iceberg reload
            IF resting.visibleQty = 0 AND resting.remainingQty > 0:
                IF resting.displayQty ≠ ⊥:
                    -- Iceberg: reload visible slice, LOSE time priority
                    resting.visibleQty = min(resting.displayQty, resting.remainingQty)
                    resting.timestamp  = currentTimestamp()   -- New priority!
                    MOVE resting TO back OF level.orders

            -- Remove fully filled resting order
            IF resting.remainingQty = 0:
                resting.status = FILLED
                REMOVE resting FROM level.orders

            -- Update resting status
            ELSE IF resting.remainingQty < resting.quantity:
                resting.status = PARTIALLY_FILLED

        -- Clean up empty level
        IF level.orders = ∅:
            REMOVE level FROM contra

    RETURN (trades, book, incoming)
```

### 5.2 Post-Match Disposition

After `MATCH` completes, the incoming order's fate depends on its TimeInForce:

```
DISPOSE(incoming, book, trades):

    IF incoming.remainingQty = 0:
        incoming.status = FILLED
        RETURN

    -- Remaining quantity exists; handle by TimeInForce:

    CASE incoming.timeInForce OF

        IOC →
            -- Immediate-Or-Cancel: cancel any remainder
            incoming.status = CANCELLED
            EMIT OrderCancelled(incoming, "IOC_REMAINDER")

        FOK →
            -- Fill-Or-Kill: this case should not arise here
            -- (FOK is handled BEFORE matching; see §5.3)
            UNREACHABLE

        GTC →
            -- Good-Till-Cancel: rest remainder on book
            IF incoming.orderType = MARKET:
                incoming.status = CANCELLED
                EMIT OrderCancelled(incoming, "MARKET_NO_FULL_FILL")
            ELSE:
                INSERT incoming INTO sameSide(book, incoming.side)
                incoming.status = if trades ≠ ∅ then PARTIALLY_FILLED else NEW

        GTD →
            -- Good-Till-Date: rest remainder, set expiry timer
            INSERT incoming INTO sameSide(book, incoming.side)
            incoming.status = if trades ≠ ∅ then PARTIALLY_FILLED else NEW
            REGISTER_EXPIRY(incoming, incoming.expireTime)

        DAY →
            -- Day order: rest remainder, expires at session close
            INSERT incoming INTO sameSide(book, incoming.side)
            incoming.status = if trades ≠ ∅ then PARTIALLY_FILLED else NEW
            REGISTER_EXPIRY(incoming, endOfSession())
```

### 5.3 Fill-Or-Kill (FOK) Pre-Check

FOK orders must be fully satisfiable or not executed at all. This requires a **dry run**:

```
FOK_CHECK(incoming, book) → bool:

    available = 0
    contra = oppSide(book, incoming.side)

    FOR EACH level IN contra:
        IF ¬canMatch(incoming, level.price):
            BREAK
        FOR EACH resting IN level.orders:
            IF ¬selfTradeConflict(incoming, resting):
                available += resting.visibleQty
                IF available ≥ incoming.quantity:
                    RETURN true

    RETURN false
```

**FOK Rule:** If `FOK_CHECK` returns false, REJECT the order immediately. Do not modify the book.

### 5.4 Minimum Quantity Pre-Check

```
MIN_QTY_CHECK(incoming, book) → bool:

    -- Identical scan to FOK_CHECK but threshold is minQty, not quantity
    available = 0
    contra = oppSide(book, incoming.side)

    FOR EACH level IN contra:
        IF ¬canMatch(incoming, level.price):
            BREAK
        FOR EACH resting IN level.orders:
            IF ¬selfTradeConflict(incoming, resting):
                available += resting.visibleQty
                IF available ≥ incoming.minQty:
                    RETURN true

    RETURN false
```

**Relationship to FOK:** FOK ≡ minQty where minQty = quantity. They are mutually
exclusive (WF-20) to avoid redundancy.

**Semantics:** If `MIN_QTY_CHECK` returns false, REJECT the order. If true, proceed
to MATCH. After matching, the filled quantity is guaranteed ≥ minQty. Any remainder
is handled by DISPOSE per TimeInForce (may rest on book).

**Resting behavior:** Once an order with minQty passes the pre-check and partially
fills, it rests on the book with its original minQty cleared:

```
    order.minQty = ⊥    -- Cleared after initial fill threshold is met
```

Subsequent fills against this resting order have no minimum constraint.

---

## 6. Order Insertion into Book

### 6.1 Insert Procedure

```
INSERT(order, bookSide):

    -- Find or create the price level
    level = FIND level IN bookSide WHERE level.price = order.price

    IF level = ⊥:
        level = PriceLevel(price = order.price, orders = [])
        INSERT level INTO bookSide at correct sorted position

    -- Set visible quantity
    IF order.displayQty ≠ ⊥:
        order.visibleQty = min(order.displayQty, order.remainingQty)
    ELSE:
        order.visibleQty = order.remainingQty

    -- Append to back of queue (FIFO: new orders get lowest priority)
    APPEND order TO level.orders
```

---

## 7. Order Types: Complete Semantics

### 7.1 LIMIT Order

```
Behavior:
    1. Attempt MATCH against contra side at limit price or better
    2. DISPOSE remainder per TimeInForce
    
Compatible TimeInForce: GTC, GTD, IOC, FOK, DAY
Rests on book: Yes (if GTC/GTD/DAY and not fully filled)
```

### 7.2 MARKET Order

```
Behavior:
    1. Attempt MATCH against contra side at ANY price
    2. If remainder exists: CANCEL (market orders never rest)

Compatible TimeInForce: IOC, FOK (enforced by WF-8)
Rests on book: Never
Price field: ⊥ (null)

Special: canMatch always returns true (no price constraint)
```

### 7.3 STOP_LIMIT Order

```
Behavior:
    Phase 1 — Dormant:
        Order rests in Book.stops, not visible on the book
        Activation condition:
            BUY  STOP_LIMIT: triggers when lastTradePrice ≥ stopPrice
            SELL STOP_LIMIT: triggers when lastTradePrice ≤ stopPrice

    Phase 2 — Triggered:
        Convert to LIMIT order with the specified price
        Process as a normal LIMIT order (enters matching cycle)
        order.status = TRIGGERED (transitional)
        
Compatible TimeInForce: GTC, GTD, IOC, FOK, DAY
```

### 7.4 STOP_MARKET Order

```
Behavior:
    Phase 1 — Dormant:
        Same activation rules as STOP_LIMIT
    
    Phase 2 — Triggered:
        Convert to MARKET order
        Process as a normal MARKET order
        
Compatible TimeInForce: IOC, FOK (inherits MARKET constraint)
```

### 7.5 Iceberg (Hidden Quantity) — Modifier, not a type

```
Applicability: LIMIT orders only (WF-10)
Parameters: displayQty (the visible slice size)

Behavior:
    - Only visibleQty is shown to the market
    - When visibleQty is fully consumed:
        1. Reload: visibleQty = min(displayQty, remainingQty)
        2. Lose time priority: timestamp = currentTimestamp()
        3. Move to BACK of queue at same price level
    - Total remainingQty participates in FOK_CHECK

Market Data:
    - Only visibleQty is published in book depth
    - remainingQty is hidden from market data feeds
```

### 7.6 Post-Only — Modifier, not a type

```
Applicability: LIMIT orders only (WF-13)
Parameters: postOnly = true
Constraint:  timeInForce ∉ {IOC, FOK} (WF-14)

Crossing predicate:
    wouldCross(incoming, book) =
        LET contra = oppSide(book, incoming.side) IN
        contra ≠ ∅ ∧ CASE incoming.side OF
            BUY  → incoming.price ≥ head(contra).price
            SELL → incoming.price ≤ head(contra).price

Post-Only policy (select exactly one per engine configuration):

    Policy REJECT:
        wouldCross(incoming, book) ⟹
            incoming.status = CANCELLED
            EMIT OrderCancelled(incoming, "POST_ONLY_WOULD_CROSS")

    Policy REPRICE:
        wouldCross(incoming, book) ⟹
            LET bestContra = head(oppSide(book, incoming.side)).price IN
            incoming.price = CASE incoming.side OF
                BUY  → bestContra - tickSize
                SELL → bestContra + tickSize
            EMIT OrderRepriced(incoming, oldPrice, incoming.price)
            INSERT incoming INTO sameSide(book, incoming.side)

    ¬wouldCross(incoming, book) ⟹
        INSERT incoming INTO sameSide(book, incoming.side)

Invariant: A post-only order NEVER generates a Trade as aggressor.
```

### 7.7 Market-to-Limit (MTL) Order

```
Behavior:
    Phase 1 — Aggressive:
        canMatch = true (no price constraint, identical to MARKET)
        Execute MATCH against contra side

        trades = ∅ ⟹
            order.status = CANCELLED
            EMIT OrderCancelled(order, "MTL_NO_LIQUIDITY")
            TERMINATE

    Phase 2 — Conversion:
        trades ≠ ∅ ⟹
            order.price     = trades[0].price    -- Lock at first execution price
            order.orderType = LIMIT
            -- Continue as LIMIT: MATCH remainder at locked price, then DISPOSE

    Price derivation:
        limitPrice = executionPrice of chronologically first trade
        (i.e., best contra price at time of entry)

Compatible TimeInForce: GTC, GTD, DAY (WF-8a)
Rests on book: Yes (after conversion, if remainder exists)
Price at submission: ⊥ (derived from first fill)
Post-Only: Incompatible (WF-15)
```

---

## 8. Self-Trade Prevention (STP)

### 8.1 Conflict Detection

```
selfTradeConflict(incoming, resting) =
    incoming.selfTradeGroup ≠ ⊥
    ∧ resting.selfTradeGroup ≠ ⊥
    ∧ incoming.selfTradeGroup = resting.selfTradeGroup
```

### 8.2 Policy Resolution

When both orders carry an `stpPolicy`, the **incoming** order's policy governs.

```
effectivePolicy(incoming, resting) = incoming.stpPolicy
```

### 8.3 STP Actions

```
HANDLE_STP(incoming, resting, book):

    policy = effectivePolicy(incoming, resting)

    CASE policy OF

        CANCEL_NEWEST →
            incoming.status = CANCELLED
            EMIT OrderCancelled(incoming, "STP_CANCEL_NEWEST")
            -- Resting order unchanged; matching halts for this incoming

        CANCEL_OLDEST →
            resting.status = CANCELLED
            REMOVE resting FROM its price level
            EMIT OrderCancelled(resting, "STP_CANCEL_OLDEST")
            -- Continue matching incoming against next resting order

        CANCEL_BOTH →
            incoming.status = CANCELLED
            resting.status  = CANCELLED
            REMOVE resting FROM its price level
            EMIT OrderCancelled(incoming, "STP_CANCEL_BOTH")
            EMIT OrderCancelled(resting, "STP_CANCEL_BOTH")

        DECREMENT →
            reduceQty = min(incoming.remainingQty, resting.visibleQty)
            incoming.remainingQty -= reduceQty
            resting.remainingQty  -= reduceQty
            resting.visibleQty    -= reduceQty
            IF incoming.remainingQty = 0: incoming.status = CANCELLED
            IF resting.remainingQty  = 0:
                resting.status = CANCELLED
                REMOVE resting FROM its price level
            EMIT OrderDecremented(incoming, resting, reduceQty)
```

### 8.4 STP Invariant

```
STP-INV: ∀ trade ∈ Trades:
    ¬selfTradeConflict(trade.aggressor, trade.passive)
    -- No trade is ever emitted between orders in the same selfTradeGroup
```

---

## 9. Cancel and Amend Operations

### 9.1 Cancel

```
CANCEL(orderId, book) → Result:

    order = FIND order IN book WHERE order.id = orderId

    IF order = ⊥:
        RETURN Error("ORDER_NOT_FOUND")

    IF order.status ∉ {NEW, PARTIALLY_FILLED}:
        RETURN Error("ORDER_NOT_CANCELLABLE")

    REMOVE order FROM its price level
    order.status = CANCELLED
    
    -- Clean up empty level (INV-1)
    IF level.orders = ∅:
        REMOVE level FROM bookSide

    EMIT OrderCancelled(order, "USER_REQUESTED")
    RETURN Ok
```

### 9.2 Cancel-Replace (Amend)

Amendment is modeled as atomic cancel-and-resubmit with specific rules:

```
AMEND(orderId, newPrice?, newQty?, book) → Result:

    order = FIND order IN book WHERE order.id = orderId

    IF order = ⊥:
        RETURN Error("ORDER_NOT_FOUND")

    -- Price change OR quantity increase → lose time priority
    IF newPrice ≠ ⊥ AND newPrice ≠ order.price:
        losePriority = true
    ELSE IF newQty ≠ ⊥ AND newQty > order.remainingQty:
        losePriority = true
    ELSE:
        losePriority = false

    -- Quantity decrease → keep time priority
    IF newQty ≠ ⊥ AND newQty < order.remainingQty:
        order.remainingQty = newQty
        order.visibleQty   = min(order.visibleQty, newQty)
        -- No priority change
        RETURN Ok

    -- Price change or quantity increase
    IF losePriority:
        REMOVE order FROM its level
        IF newPrice ≠ ⊥: order.price = newPrice
        IF newQty  ≠ ⊥: order.remainingQty = newQty
        order.timestamp = currentTimestamp()    -- New priority
        
        -- Re-enter matching cycle (price change might cross spread)
        PROCESS(order, book)   -- Full matching cycle as if new order
        RETURN Ok
```

---

## 10. Stop Order Triggering

### 10.1 Trigger Evaluation

After every trade, evaluate all stop orders:

```
EVALUATE_STOPS(lastTradePrice, book):

    triggered = []

    FOR EACH stop IN book.stops:
        shouldTrigger = CASE stop.side OF
            BUY  → lastTradePrice ≥ stop.stopPrice
            SELL → lastTradePrice ≤ stop.stopPrice

        IF shouldTrigger:
            APPEND stop TO triggered
            REMOVE stop FROM book.stops

    -- Sort triggered stops by arrival time (FIFO fairness)
    SORT triggered BY timestamp ASC

    -- Process each triggered stop as a new order
    FOR EACH stop IN triggered:
        stop.status = TRIGGERED
        EMIT OrderTriggered(stop)
        
        -- Convert to base type
        IF stop.orderType = STOP_LIMIT:
            stop.orderType = LIMIT
        ELSE:   -- STOP_MARKET
            stop.orderType = MARKET
            
        stop.stopPrice = ⊥
        PROCESS(stop, book)    -- Enter matching cycle
```

### 10.2 Cascading Triggers

Triggered stop orders may themselves generate trades, which may trigger further stops. This cascade continues until no more stops are triggered:

```
PROCESS_WITH_CASCADING_STOPS(incomingOrder, book):
    trades = MATCH(book, incomingOrder)
    DISPOSE(incomingOrder, book, trades)
    
    FOR EACH trade IN trades:
        EVALUATE_STOPS(trade.price, book)
        -- EVALUATE_STOPS internally calls PROCESS, which recurses
```

**Safeguard:** Implementations SHOULD impose a maximum cascade depth to prevent runaway chains.

---

## 11. Expiry Management

### 11.1 Time-Based Expiry

```
EXPIRE_CHECK(currentTime, book):

    FOR EACH order IN book (bids ∪ asks):
        shouldExpire = CASE order.timeInForce OF
            GTD → currentTime ≥ order.expireTime
            DAY → currentTime ≥ endOfSession()
            GTC → false
            _   → false   -- IOC/FOK never rest

        IF shouldExpire:
            REMOVE order FROM book
            order.status = EXPIRED
            EMIT OrderExpired(order)
```

---

## 12. Master Order Processing Pipeline

The complete lifecycle of an incoming order:

```
PROCESS(order, book):

    -- Phase 0: Validation
    IF ¬WellFormed(order):
        REJECT(order)
        RETURN

    EMIT OrderAccepted(order)

    -- Phase 1: Stop order handling
    IF order.orderType ∈ {STOP_LIMIT, STOP_MARKET}:
        IF shouldTriggerImmediately(order, lastTradePrice):
            order = convertStopToBase(order)
            EMIT OrderTriggered(order)
        ELSE:
            ADD order TO book.stops
            RETURN

    -- Phase 2: Post-only check (before any matching)
    IF order.postOnly:
        result = POST_ONLY_CHECK(order, book)    -- See §7.6
        IF result ∈ {REJECT, REPRICE}:
            RETURN    -- Order cancelled or repriced-and-inserted; no matching

    -- Phase 3: Quantity pre-checks (before any matching or routing)
    IF order.timeInForce = FOK:
        IF ¬FOK_CHECK(order, book):
            order.status = CANCELLED
            EMIT OrderCancelled(order, "FOK_NOT_SATISFIABLE")
            RETURN

    IF order.minQty ≠ ⊥:
        IF ¬MIN_QTY_CHECK(order, book):              -- See §5.4
            order.status = CANCELLED
            EMIT OrderCancelled(order, "MIN_QTY_NOT_SATISFIABLE")
            RETURN

    -- Phase 4: Market-to-Limit routing
    IF order.orderType = MARKET_TO_LIMIT:
        PROCESS_MTL(order, book)                 -- See §7.7
        IF order.minQty ≠ ⊥: order.minQty = ⊥   -- Clear after threshold met
        RETURN

    -- Phase 5: Matching
    trades = MATCH(book, order)

    -- Phase 5a: Clear minQty after successful matching
    IF order.minQty ≠ ⊥ AND trades ≠ ∅:
        order.minQty = ⊥    -- Threshold met; no constraint when resting

    -- Phase 6: Post-match disposition
    DISPOSE(order, book, trades)

    -- Phase 7: Emit trades and trigger stops
    FOR EACH trade IN trades:
        EMIT TradeExecuted(trade)
        EVALUATE_STOPS(trade.price, book)

    -- Phase 8: Emit book updates
    EMIT_BOOK_UPDATES(book)
```

---

## 13. Formal Invariant Summary

The following invariants MUST hold after every `PROCESS` call completes:

| ID | Invariant | Description |
|------|---------------------------------------------|----------------------------------------------|
| INV-1 | ∀ level: level.orders ≠ ∅ | No empty price levels |
| INV-2 | Bids strictly descending | Price ordering |
| INV-3 | Asks strictly ascending | Price ordering |
| INV-4 | bestBid < bestAsk (or either ⊥) | Uncrossed book |
| INV-5 | ∀ order on book: remainingQty > 0 | No ghosts |
| INV-6 | ∀ order on book: status ∈ {NEW, PARTIAL} | Status consistency |
| INV-7 | FIFO within price level | Time priority |
| INV-8 | No MARKET orders on book | Markets never rest |
| INV-9 | ∀ trade: trade.price = passive.price | Passive price rule |
| INV-10 | Events emitted in causal order | Determinism |
| INV-11 | ∀ order on book: ¬(order.postOnly ∧ order generated trades as aggressor) | Post-only guarantee |
| INV-12 | ∀ trade: ¬selfTradeConflict(trade.aggressor, trade.passive) | STP guarantee |
| INV-13 | No MARKET_TO_LIMIT orders on book (converted to LIMIT before resting) | MTL never rests as MTL |
| INV-14 | ∀ order on book: order.minQty = ⊥ | Resting orders have no min constraint |

---

## 14. Complexity Guarantees

For a book with `P` price levels and `N` total orders:

| Operation | Time Complexity | Notes |
|-----------|----------------|-------|
| Insert (no match) | O(log P) | Binary search for price level |
| Match (single fill) | O(1) | Front of best level |
| Match (sweeping K levels) | O(K) | K levels consumed |
| Cancel by ID | O(1) | With order ID → level index |
| FOK check | O(N) worst case | Must scan available qty |
| Best bid/ask | O(1) | Head of sorted structure |

---

## 15. Glossary

| Term | Definition |
|------|-----------|
| **Aggressor** | The incoming order that initiates matching |
| **Passive** | A resting order on the book that gets matched against |
| **Price level** | All orders at the same price, maintained in FIFO order |
| **Visible quantity** | The portion of an iceberg order currently exposed to the market |
| **Spread** | The difference between best ask and best bid |
| **Crossed book** | An invalid state where best bid ≥ best ask |
| **Sweep** | When an aggressive order matches through multiple price levels |
| **Self-trade** | When both sides of a potential trade belong to the same entity |
| **Cascade** | When a trade triggers stop orders, which cause more trades |
| **Time priority** | Earlier orders at the same price level are filled first |
| **Post-only** | Order modifier guaranteeing the order only adds liquidity (never aggresses) |
| **Market-to-Limit** | Order that sweeps like a MARKET then converts remainder to LIMIT at first fill price |
| **Self-trade prevention** | Mechanism preventing two orders from the same entity from matching |
| **Tick size** | Minimum price increment for an instrument (required for post-only REPRICE policy) |
| **Minimum quantity** | Minimum fill threshold on first execution; order cancelled if unavailable, cleared once met |

---

## Appendix A: State Transition Diagram for Order Lifecycle

```
                    ┌──────────┐
        ┌───────────│ REJECTED │
        │           └──────────┘
        │ (validation
        │  failure)
        │
   ┌────┴────┐        ┌───────────┐
   │ INCOMING │───────▶│    NEW     │──────────────────────┐
   └─────────┘  rest   └───────────┘                       │
        │               │         │                        │
        │               │ partial │ cancel/                │
        │               │ fill    │ expire                 │
        │               ▼         ▼                        │
        │        ┌──────────────┐  ┌───────────┐           │
        │        │PARTIALLY_    │  │ CANCELLED │           │
        │        │FILLED        │  └───────────┘           │
        │        └──────────────┘  ┌───────────┐           │
        │               │         │  EXPIRED   │           │
        │               │ final   └───────────┘           │
        │               │ fill          ▲                  │
        │               ▼              │                  │
        │         ┌──────────┐         │                  │
        └────────▶│  FILLED  │         │                  │
         instant  └──────────┘         │                  │
         fill                          │                  │
                                       └──────────────────┘
                                         cancel/expire

   Stop orders: INCOMING → (stops book) → TRIGGERED → re-enter as LIMIT/MARKET
```

---

## Appendix B: Matching Walk-Through Example

**Setup:** Empty book for instrument XYZ.

**Sequence of events:**

```
1. LIMIT BUY  100 @ $10.00 GTC  → Rests on bid side.  Book: Bid[$10.00: 100]
2. LIMIT BUY   50 @ $10.00 GTC  → Rests behind #1.    Book: Bid[$10.00: 100, 50]
3. LIMIT BUY   75 @ $10.05 GTC  → New best bid.        Book: Bid[$10.05: 75][$10.00: 100, 50]
4. LIMIT SELL  30 @ $9.95  GTC  → Crosses! Matches:
     - Fill 30 from order #3 @ $10.05 (passive price!)
     - Order #3 now has 45 remaining
     - Aggressive SELL gets price improvement ($10.05 > $9.95)
     Book: Bid[$10.05: 45][$10.00: 100, 50]
5. MARKET SELL 200 IOC           → Sweeps:
     - Fill 45 from order #3 @ $10.05 → order #3 FILLED
     - Fill 100 from order #1 @ $10.00 → order #1 FILLED
     - Fill 50 from order #2 @ $10.00  → order #2 FILLED
     - Remaining 5: cancelled (IOC, MARKET never rests)
     Book: empty
```
