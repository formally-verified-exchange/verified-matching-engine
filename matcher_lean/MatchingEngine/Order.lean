import MatchingEngine.Basic

/-!
# Matching Engine — Order Model

Order structure and well-formedness predicate (§2).
Covers WF-1 through WF-20 with deliberate omissions:
- WF-6/7 omitted (GTD expiry not modeled)
- WF-11 included, WF-12 omitted (of the initialization pair, only
  remainingQty = qty is checked; visibleQty initialization is not)
- WF-17 omitted (enum validation, handled by the type system)
-/

-- §2.1 Order definition
structure Order where
  id            : OrderId
  side          : Side
  orderType     : OrderType
  tif           : TimeInForce
  price         : Option Price        -- none for MARKET orders
  stopPrice     : Option Price        -- none for non-stop orders
  qty           : Quantity            -- Original quantity
  remainingQty  : Quantity            -- Unfilled quantity
  minQty        : Option Quantity     -- none if no minimum
  displayQty    : Option Quantity     -- none if not iceberg
  visibleQty    : Quantity            -- Currently visible slice
  postOnly      : Bool
  status        : OrderStatus
  timestamp     : Timestamp
  stpGroup      : Option StpGroup
  stpPolicy     : Option STPPolicy
  deriving DecidableEq, Repr, BEq, Inhabited

-- §4.1 Trade / Fill
structure Trade where
  price         : Price               -- Execution price (passive order's price)
  qty           : Quantity
  aggressorId   : OrderId
  passiveId     : OrderId
  aggressorSide : Side
  aggPostOnly   : Bool                -- For INV-11 checking
  aggStpGroup   : Option StpGroup     -- For INV-12 checking
  pasStpGroup   : Option StpGroup     -- For INV-12 checking
  deriving Repr, BEq, Inhabited

-- §2.2 Well-formedness predicate (WF-1..20, minus WF-6/7, WF-12, WF-17)
def Order.wellFormed (o : Order) : Bool :=
  -- WF-1: quantity > 0
  (o.qty > 0) &&
  -- WF-2: LIMIT => price is some positive
  (o.orderType != .limit || (o.price.isSome && o.price.any (· > 0))) &&
  -- WF-2a: STOP_LIMIT => price is some positive
  (o.orderType != .stopLimit || (o.price.isSome && o.price.any (· > 0))) &&
  -- WF-2b: MTL => price is none
  (o.orderType != .marketToLimit || o.price.isNone) &&
  -- WF-3: MARKET/STOP_MARKET => price is none
  (o.orderType != .market || o.price.isNone) &&
  (o.orderType != .stopMarket || o.price.isNone) &&
  -- WF-4: STOP_LIMIT/STOP_MARKET => stopPrice is some positive
  (o.orderType != .stopLimit || (o.stopPrice.isSome && o.stopPrice.any (· > 0))) &&
  (o.orderType != .stopMarket || (o.stopPrice.isSome && o.stopPrice.any (· > 0))) &&
  -- WF-5: LIMIT/MARKET/MTL => stopPrice is none
  (o.orderType != .limit || o.stopPrice.isNone) &&
  (o.orderType != .market || o.stopPrice.isNone) &&
  (o.orderType != .marketToLimit || o.stopPrice.isNone) &&
  -- WF-8: MARKET => tif ∈ {IOC, FOK}
  (o.orderType != .market || (o.tif == .ioc || o.tif == .fok)) &&
  -- WF-8a: MTL => tif ∈ {GTC, DAY}
  (o.orderType != .marketToLimit || (o.tif == .gtc || o.tif == .day)) &&
  -- WF-9: displayQty => displayQty > 0 ∧ displayQty ≤ qty
  (o.displayQty.isNone || o.displayQty.any (fun d => d > 0 && d <= o.qty)) &&
  -- WF-10: displayQty => LIMIT
  (o.displayQty.isNone || o.orderType == .limit) &&
  -- WF-13: postOnly => LIMIT
  (!o.postOnly || o.orderType == .limit) &&
  -- WF-14: postOnly => tif ∉ {IOC, FOK}
  (!o.postOnly || (o.tif != .ioc && o.tif != .fok)) &&
  -- WF-15: MARKET/MTL => ¬postOnly
  (o.orderType != .market || !o.postOnly) &&
  (o.orderType != .marketToLimit || !o.postOnly) &&
  -- WF-16: stpGroup = none ↔ stpPolicy = none
  (o.stpGroup.isNone == o.stpPolicy.isNone) &&
  -- WF-18: minQty => minQty > 0 ∧ minQty ≤ qty
  (o.minQty.isNone || o.minQty.any (fun m => m > 0 && m <= o.qty)) &&
  -- WF-19: minQty => ¬postOnly
  (o.minQty.isNone || !o.postOnly) &&
  -- WF-20: FOK => minQty = none
  (o.tif != .fok || o.minQty.isNone) &&
  -- WF-11: remainingQty = qty (at creation)
  (o.remainingQty == o.qty)

-- Propositional version for theorem statements
def Order.WellFormed (o : Order) : Prop :=
  o.qty > 0 ∧
  (o.orderType = .limit → o.price.isSome ∧ ∀ p, o.price = some p → p > 0) ∧
  (o.orderType = .stopLimit → o.price.isSome ∧ ∀ p, o.price = some p → p > 0) ∧
  (o.orderType = .marketToLimit → o.price = none) ∧
  (o.orderType = .market → o.price = none) ∧
  (o.orderType = .stopMarket → o.price = none) ∧
  (o.orderType = .stopLimit → o.stopPrice.isSome ∧ ∀ p, o.stopPrice = some p → p > 0) ∧
  (o.orderType = .stopMarket → o.stopPrice.isSome ∧ ∀ p, o.stopPrice = some p → p > 0) ∧
  (o.orderType = .limit → o.stopPrice = none) ∧
  (o.orderType = .market → o.stopPrice = none) ∧
  (o.orderType = .marketToLimit → o.stopPrice = none) ∧
  (o.orderType = .market → o.tif = .ioc ∨ o.tif = .fok) ∧
  (o.orderType = .marketToLimit → o.tif = .gtc ∨ o.tif = .day) ∧
  (o.displayQty.isSome → ∀ d, o.displayQty = some d → d > 0 ∧ d ≤ o.qty) ∧
  (o.displayQty.isSome → o.orderType = .limit) ∧
  (o.postOnly = true → o.orderType = .limit) ∧
  (o.postOnly = true → o.tif ≠ .ioc ∧ o.tif ≠ .fok) ∧
  (o.orderType = .market → o.postOnly = false) ∧
  (o.orderType = .marketToLimit → o.postOnly = false) ∧
  (o.stpGroup = none ↔ o.stpPolicy = none) ∧
  (o.minQty.isSome → ∀ m, o.minQty = some m → m > 0 ∧ m ≤ o.qty) ∧
  (o.minQty.isSome → o.postOnly = false) ∧
  (o.tif = .fok → o.minQty = none) ∧
  o.remainingQty = o.qty
