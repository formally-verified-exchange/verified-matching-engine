---- MODULE MatchingEngine_shallow_symmetric ----
(***************************************************************************)
(* Auto-generated from scenarios/shallow_symmetric.json. Do not edit by hand.         *)
(*                                                                         *)
(* EXTENDS MatchingEngine and replaces Init with a seeded predicate that   *)
(* pre-fills the book (and optionally the stops set) before TLC starts     *)
(* exploring.                                                              *)
(***************************************************************************)
EXTENDS MatchingEngine

Init_Seeded ==
    /\ bidQ = [p \in PRICES |->
          CASE p = 1 -> <<MakeOrder(1, "BUY", "LIMIT", "GTC", 1, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 1)>>
            [] OTHER -> <<>>]
    /\ askQ = [p \in PRICES |->
          CASE p = 3 -> <<MakeOrder(2, "SELL", "LIMIT", "GTC", 3, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 2)>>
            [] OTHER -> <<>>]
    /\ stops = {}
    /\ lastTradePrice = NULL
    /\ postOnlyOK = TRUE
    /\ stpOK = TRUE
    /\ nextId = 3
    /\ clock = 3
    /\ lastAction = [type |-> "SeedInit"]

=============================================================================
