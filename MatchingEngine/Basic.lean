/-!
# Matching Engine — Basic Types

Primitive types for the matching engine formalization.
All types are kept simple (Nat-based) for decidability and computability.
-/

-- §1.1 Primitive domains
abbrev Price := Nat       -- Strictly positive (enforced by well-formedness)
abbrev Quantity := Nat    -- Strictly positive (enforced by well-formedness)
abbrev Timestamp := Nat   -- Monotonically increasing logical clock
abbrev OrderId := Nat     -- Unique, monotonically increasing
abbrev StpGroup := Nat    -- Self-trade prevention group identifier

-- §1.2 Enumerated types
inductive Side where
  | buy
  | sell
  deriving DecidableEq, Repr, BEq, Inhabited

inductive OrderType where
  | limit
  | market
  | marketToLimit
  | stopLimit
  | stopMarket
  deriving DecidableEq, Repr, BEq, Inhabited

inductive TimeInForce where
  | gtc    -- Good-Till-Cancel
  | ioc    -- Immediate-Or-Cancel
  | fok    -- Fill-Or-Kill
  | day    -- Day order
  deriving DecidableEq, Repr, BEq, Inhabited

inductive OrderStatus where
  | new_
  | partiallyFilled
  | filled
  | cancelled
  | rejected
  deriving DecidableEq, Repr, BEq, Inhabited

inductive STPPolicy where
  | cancelNewest
  | cancelOldest
  | cancelBoth
  | decrement
  deriving DecidableEq, Repr, BEq, Inhabited

-- §1.3 Derived types
def Side.opposite : Side → Side
  | .buy  => .sell
  | .sell => .buy
