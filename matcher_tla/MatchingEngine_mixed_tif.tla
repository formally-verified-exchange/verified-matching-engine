---- MODULE MatchingEngine_mixed_tif ----
(***************************************************************************)
(* Auto-generated from scenarios/mixed_tif.json. Do not edit by hand.         *)
(*                                                                         *)
(* EXTENDS MatchingEngine and replaces Init with a seeded predicate that   *)
(* pre-fills the book (and optionally the stops set) before TLC starts     *)
(* exploring.                                                              *)
(***************************************************************************)
EXTENDS MatchingEngine

Init_Seeded ==
    /\ bidQ = [p \in PRICES |->
          CASE p = 1 -> <<MakeOrder(2, "BUY", "LIMIT", "DAY", 1, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 2)>>
            [] p = 2 -> <<MakeOrder(1, "BUY", "LIMIT", "GTC", 2, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 1)>>
            [] OTHER -> <<>>]
    /\ askQ = [p \in PRICES |->
          CASE p = 4 -> <<MakeOrder(3, "SELL", "LIMIT", "GTC", 4, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 3)>>
            [] p = 5 -> <<MakeOrder(4, "SELL", "LIMIT", "DAY", 5, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 4)>>
            [] OTHER -> <<>>]
    /\ stops = {}
    /\ lastTradePrice = NULL
    /\ postOnlyOK = TRUE
    /\ stpOK = TRUE
    /\ nextId = 5
    /\ clock = 5
    /\ lastAction = [type |-> "SeedInit"]

=============================================================================
