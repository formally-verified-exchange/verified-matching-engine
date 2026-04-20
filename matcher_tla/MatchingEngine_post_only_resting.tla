---- MODULE MatchingEngine_post_only_resting ----
(***************************************************************************)
(* Auto-generated from scenarios/post_only_resting.json. Do not edit by hand.         *)
(*                                                                         *)
(* EXTENDS MatchingEngine and replaces Init with a seeded predicate that   *)
(* pre-fills the book (and optionally the stops set) before TLC starts     *)
(* exploring.                                                              *)
(***************************************************************************)
EXTENDS MatchingEngine

Init_Seeded ==
    /\ bidQ = [p \in PRICES |->
          CASE p = 2 -> <<MakeOrder(1, "BUY", "LIMIT", "GTC", 2, NULL, 1, NULL, TRUE, NULL, NULL, NULL, 1)>>
            [] OTHER -> <<>>]
    /\ askQ = [p \in PRICES |->
          CASE p = 4 -> <<MakeOrder(2, "SELL", "LIMIT", "GTC", 4, NULL, 1, NULL, TRUE, NULL, NULL, NULL, 2)>>
            [] OTHER -> <<>>]
    /\ stops = {}
    /\ lastTradePrice = NULL
    /\ postOnlyOK = TRUE
    /\ stpOK = TRUE
    /\ nextId = 3
    /\ clock = 3
    /\ lastAction = [type |-> "SeedInit"]

=============================================================================
