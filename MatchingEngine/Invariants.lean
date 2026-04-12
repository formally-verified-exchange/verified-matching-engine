import MatchingEngine.Book

/-!
# Matching Engine — Invariant Definitions

All invariants from §13 as both decidable (Bool) and propositional (Prop) forms.
-/

-- §13 INV-4: Book is uncrossed
def bookUncrossedB (b : BookState) : Bool :=
  match bestBidPrice b, bestAskPrice b with
  | some bid, some ask => bid < ask
  | _, _ => true

def BookUncrossed (b : BookState) : Prop :=
  match bestBidPrice b, bestAskPrice b with
  | some bid, some ask => bid < ask
  | _, _ => True

instance : Decidable (BookUncrossed b) := by
  unfold BookUncrossed
  cases bestBidPrice b <;> cases bestAskPrice b <;> simp <;> exact inferInstance

-- §13 INV-5: No ghost orders (remainingQty > 0)
def noGhostsB (b : BookState) : Bool :=
  (b.bids.all fun l => l.orders.all fun o => o.remainingQty > 0) &&
  (b.asks.all fun l => l.orders.all fun o => o.remainingQty > 0)

def NoGhosts (b : BookState) : Prop :=
  (∀ l ∈ b.bids, ∀ o ∈ l.orders, o.remainingQty > 0) ∧
  (∀ l ∈ b.asks, ∀ o ∈ l.orders, o.remainingQty > 0)

-- §13 INV-6: Status consistency
def statusConsistencyB (b : BookState) : Bool :=
  (b.bids.all fun l => l.orders.all fun o =>
    o.status == .new_ || o.status == .partiallyFilled) &&
  (b.asks.all fun l => l.orders.all fun o =>
    o.status == .new_ || o.status == .partiallyFilled)

-- §13 INV-7: FIFO within price level (timestamps strictly increasing)
def fifoLevelB (orders : List Order) : Bool :=
  match orders with
  | [] | [_] => true
  | o1 :: o2 :: rest => o1.timestamp < o2.timestamp && fifoLevelB (o2 :: rest)

def fifoWithinLevelB (b : BookState) : Bool :=
  (b.bids.all fun l => fifoLevelB l.orders) &&
  (b.asks.all fun l => fifoLevelB l.orders)

def FIFOLevel (orders : List Order) : Prop :=
  orders.Pairwise (fun o1 o2 => o1.timestamp < o2.timestamp)

def FIFOWithinLevel (b : BookState) : Prop :=
  (∀ l ∈ b.bids, FIFOLevel l.orders) ∧
  (∀ l ∈ b.asks, FIFOLevel l.orders)

-- §13 INV-8/INV-13: No MARKET or MTL orders on book
def noRestingMarketsB (b : BookState) : Bool :=
  (b.bids.all fun l => l.orders.all fun o =>
    o.orderType != .market && o.orderType != .marketToLimit) &&
  (b.asks.all fun l => l.orders.all fun o =>
    o.orderType != .market && o.orderType != .marketToLimit)

def NoRestingMarkets (b : BookState) : Prop :=
  (∀ l ∈ b.bids, ∀ o ∈ l.orders, o.orderType ≠ .market ∧ o.orderType ≠ .marketToLimit) ∧
  (∀ l ∈ b.asks, ∀ o ∈ l.orders, o.orderType ≠ .market ∧ o.orderType ≠ .marketToLimit)

-- §13 INV-14: No resting minQty
def noRestingMinQtyB (b : BookState) : Bool :=
  (b.bids.all fun l => l.orders.all fun o => o.minQty.isNone) &&
  (b.asks.all fun l => l.orders.all fun o => o.minQty.isNone)

def NoRestingMinQty (b : BookState) : Prop :=
  (∀ l ∈ b.bids, ∀ o ∈ l.orders, o.minQty = none) ∧
  (∀ l ∈ b.asks, ∀ o ∈ l.orders, o.minQty = none)

-- §13 INV-1: No empty price levels
def noEmptyLevelsB (b : BookState) : Bool :=
  (b.bids.all fun l => !l.orders.isEmpty) &&
  (b.asks.all fun l => !l.orders.isEmpty)

def NoEmptyLevels (b : BookState) : Prop :=
  (∀ l ∈ b.bids, l.orders ≠ []) ∧
  (∀ l ∈ b.asks, l.orders ≠ [])

-- §13 INV-2 (bids), INV-3 (asks): Price level sorting
def bidsSortedDescB (levels : List PriceLevel) : Bool :=
  match levels with
  | [] | [_] => true
  | l1 :: l2 :: rest => l1.price > l2.price && bidsSortedDescB (l2 :: rest)

def asksSortedAscB (levels : List PriceLevel) : Bool :=
  match levels with
  | [] | [_] => true
  | l1 :: l2 :: rest => l1.price < l2.price && asksSortedAscB (l2 :: rest)

-- §8.4 STP invariant: no trade between same group
def stpGuaranteeB (trades : List Trade) : Bool :=
  trades.all fun t =>
    match t.aggStpGroup, t.pasStpGroup with
    | some g1, some g2 => g1 != g2
    | _, _ => true

-- INV-11: Post-only guarantee
def postOnlyGuaranteeB (trades : List Trade) : Bool :=
  trades.all fun t => !t.aggPostOnly

-- Combined book invariant (Bool version for #eval)
def bookInvariantB (b : BookState) : Bool :=
  bookUncrossedB b &&
  noGhostsB b &&
  statusConsistencyB b &&
  fifoWithinLevelB b &&
  noRestingMarketsB b &&
  noRestingMinQtyB b &&
  noEmptyLevelsB b

-- Combined book invariant (Prop version for theorems)
def BookInvariant (b : BookState) : Prop :=
  BookUncrossed b ∧
  NoGhosts b ∧
  NoRestingMarkets b ∧
  NoRestingMinQty b ∧
  NoEmptyLevels b ∧
  FIFOWithinLevel b
