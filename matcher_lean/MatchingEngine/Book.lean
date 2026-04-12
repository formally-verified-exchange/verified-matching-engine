import MatchingEngine.Order

/-!
# Matching Engine — Order Book Model

Book structure with sorted price levels and FIFO order queues (§3).
Includes sorted insertion and book accessors.
-/

-- §3.1 Book structure
structure PriceLevel where
  price  : Price
  orders : List Order     -- FIFO queue: head = highest priority
  deriving Repr, BEq, Inhabited

-- Main book state
structure BookState where
  bids           : List PriceLevel   -- Sorted DESCENDING by price (best bid first)
  asks           : List PriceLevel   -- Sorted ASCENDING by price (best ask first)
  stops          : List Order        -- Dormant stop orders
  lastTradePrice : Option Price
  nextId         : OrderId
  clock          : Timestamp
  deriving Repr, Inhabited

-- Empty book constructor
def BookState.empty : BookState :=
  { bids := [], asks := [], stops := [],
    lastTradePrice := none, nextId := 1, clock := 1 }

-- §3.2 Book accessor functions
def bestBidPrice (b : BookState) : Option Price :=
  b.bids.head?.map (·.price)

def bestAskPrice (b : BookState) : Option Price :=
  b.asks.head?.map (·.price)

-- §6.1 Insert order into correct price level on a book side
-- For bids: sorted descending (insert at correct position)
-- For asks: sorted ascending (insert at correct position)

/-- Insert an order into a list of price levels sorted ascending by price.
    Creates a new level if none exists at the order's price. -/
def insertAsc (levels : List PriceLevel) (o : Order) (p : Price) : List PriceLevel :=
  match levels with
  | [] => [{ price := p, orders := [o] }]
  | l :: rest =>
    if p < l.price then
      { price := p, orders := [o] } :: l :: rest
    else if p == l.price then
      { l with orders := l.orders ++ [o] } :: rest
    else
      l :: insertAsc rest o p

/-- Insert an order into a list of price levels sorted descending by price.
    Creates a new level if none exists at the order's price. -/
def insertDesc (levels : List PriceLevel) (o : Order) (p : Price) : List PriceLevel :=
  match levels with
  | [] => [{ price := p, orders := [o] }]
  | l :: rest =>
    if p > l.price then
      { price := p, orders := [o] } :: l :: rest
    else if p == l.price then
      { l with orders := l.orders ++ [o] } :: rest
    else
      l :: insertDesc rest o p

/-- Insert order into the correct side of the book (§6.1).
    Sets visibleQty and status before insertion. -/
def insertOrder (b : BookState) (o : Order) (hasTrades : Bool) : BookState :=
  let visQ := match o.displayQty with
    | some d => min d o.remainingQty
    | none   => o.remainingQty
  let st := if hasTrades then OrderStatus.partiallyFilled else OrderStatus.new_
  let o' := { o with visibleQty := visQ, status := st, minQty := none }
  match o.side with
  | .buy  => { b with bids := insertDesc b.bids o' (o.price.getD 0) }
  | .sell => { b with asks := insertAsc  b.asks o' (o.price.getD 0) }

/-- Remove an order by ID from a list of price levels.
    Also removes the price level if it becomes empty (INV-1). -/
def removeLevels (levels : List PriceLevel) (oid : OrderId) : List PriceLevel :=
  levels.filterMap fun l =>
    let orders' := l.orders.filter (·.id != oid)
    if orders'.isEmpty then none
    else some { l with orders := orders' }

/-- Remove an order by ID from the book (either side). -/
def removeOrder (b : BookState) (oid : OrderId) : BookState :=
  { b with
    bids := removeLevels b.bids oid,
    asks := removeLevels b.asks oid }

/-- Get all orders on the book (both sides). -/
def allBookOrders (b : BookState) : List Order :=
  (b.bids.flatMap (·.orders)) ++ (b.asks.flatMap (·.orders))

/-- Get the contra side levels for matching. -/
def contraLevels (b : BookState) (s : Side) : List PriceLevel :=
  match s with
  | .buy  => b.asks
  | .sell => b.bids

/-- Set the contra side levels. -/
def setContraLevels (b : BookState) (s : Side) (levels : List PriceLevel) : BookState :=
  match s with
  | .buy  => { b with asks := levels }
  | .sell => { b with bids := levels }
