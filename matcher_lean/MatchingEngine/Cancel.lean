import MatchingEngine.Book

/-!
# Matching Engine — Cancel and Amend (§9)
-/

/-- Find an order on the book by ID. Returns (side, order). -/
def findOrderOnBook (b : BookState) (oid : OrderId) : Option (Side × Order) :=
  let searchSide (side : Side) (levels : List PriceLevel) : Option (Side × Order) :=
    levels.findSome? fun level =>
      level.orders.findSome? fun order =>
        if order.id == oid then some (side, order) else none
  match searchSide .buy b.bids with
  | some r => some r
  | none => searchSide .sell b.asks

/-- Remove an order by ID from a list of price levels.
    Removes empty levels (INV-1). -/
def removeLevelOrder (levels : List PriceLevel) (oid : OrderId) : List PriceLevel :=
  levels.filterMap fun l =>
    let orders' := l.orders.filter (·.id != oid)
    if orders'.isEmpty then none
    else some { l with orders := orders' }

/-- Cancel a resting order (§9.1). -/
def cancelOrder (b : BookState) (oid : OrderId) : Option BookState :=
  match findOrderOnBook b oid with
  | none => none
  | some (side, _) =>
    match side with
    | .buy  => some { b with bids := removeLevelOrder b.bids oid }
    | .sell => some { b with asks := removeLevelOrder b.asks oid }

/-- Amend: quantity decrease only (keeps priority) (§9.2). -/
def amendQtyDecrease (b : BookState) (oid : OrderId) (newQty : Quantity) : Option BookState :=
  match findOrderOnBook b oid with
  | none => none
  | some (side, order) =>
    if newQty >= order.remainingQty || newQty == 0 then none
    else
      let updateLevels (levels : List PriceLevel) :=
        levels.map fun l =>
          { l with orders := l.orders.map fun o =>
              if o.id == oid then
                { o with remainingQty := newQty,
                         visibleQty := min o.visibleQty newQty }
              else o }
      match side with
      | .buy  => some { b with bids := updateLevels b.bids }
      | .sell => some { b with asks := updateLevels b.asks }
