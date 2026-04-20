---- MODULE MatchingEngine_stacked_level ----
(***************************************************************************)
(* Auto-generated from scenarios/stacked_level.json. Do not edit by hand.         *)
(*                                                                         *)
(* EXTENDS MatchingEngine and replaces Init with a seeded predicate that   *)
(* pre-fills the book (and optionally the stops set) before TLC starts     *)
(* exploring.                                                              *)
(***************************************************************************)
EXTENDS MatchingEngine

Init_Seeded ==
    /\ bidQ = [p \in PRICES |->
          CASE p = 2 -> <<MakeOrder(1, "BUY", "LIMIT", "GTC", 2, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 1), MakeOrder(2, "BUY", "LIMIT", "GTC", 2, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 2), MakeOrder(3, "BUY", "LIMIT", "GTC", 2, NULL, 2, NULL, FALSE, NULL, NULL, NULL, 3)>>
            [] OTHER -> <<>>]
    /\ askQ = [p \in PRICES |->
          CASE p = 4 -> <<MakeOrder(4, "SELL", "LIMIT", "GTC", 4, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 4)>>
            [] OTHER -> <<>>]
    /\ stops = {}
    /\ lastTradePrice = NULL
    /\ postOnlyOK = TRUE
    /\ stpOK = TRUE
    /\ nextId = 5
    /\ clock = 5
    /\ lastAction = [type |-> "SeedInit"]

=============================================================================
