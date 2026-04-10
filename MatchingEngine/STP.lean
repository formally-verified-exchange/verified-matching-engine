import MatchingEngine.Order

/-!
# Matching Engine — Self-Trade Prevention (§8)

Conflict detection and all four STP policies.
-/

-- §8.1 Conflict detection
def selfTradeConflict (inc rest : Order) : Bool :=
  match inc.stpGroup, rest.stpGroup with
  | some g1, some g2 => g1 == g2
  | _, _ => false
