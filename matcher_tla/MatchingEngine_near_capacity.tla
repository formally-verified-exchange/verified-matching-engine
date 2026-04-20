---- MODULE MatchingEngine_near_capacity ----
(***************************************************************************)
(* Auto-generated from scenarios/near_capacity.json. Do not edit by hand.         *)
(*                                                                         *)
(* EXTENDS MatchingEngine and replaces Init with a seeded predicate that   *)
(* pre-fills the book (and optionally the stops set) before TLC starts     *)
(* exploring.                                                              *)
(***************************************************************************)
EXTENDS MatchingEngine

Init_Seeded ==
    /\ bidQ = [p \in PRICES |->
          CASE p = 1 -> <<MakeOrder(1, "BUY", "LIMIT", "GTC", 1, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 1)>>
            [] p = 2 -> <<MakeOrder(2, "BUY", "LIMIT", "GTC", 2, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 2)>>
            [] p = 3 -> <<MakeOrder(3, "BUY", "LIMIT", "GTC", 3, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 3)>>
            [] OTHER -> <<>>]
    /\ askQ = [p \in PRICES |->
          CASE p = 5 -> <<MakeOrder(4, "SELL", "LIMIT", "GTC", 5, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 4)>>
            [] p = 6 -> <<MakeOrder(5, "SELL", "LIMIT", "GTC", 6, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 5)>>
            [] OTHER -> <<>>]
    /\ stops = {}
    /\ lastTradePrice = NULL
    /\ postOnlyOK = TRUE
    /\ stpOK = TRUE
    /\ nextId = 6
    /\ clock = 6
    /\ lastAction = [type |-> "SeedInit"]

=============================================================================
