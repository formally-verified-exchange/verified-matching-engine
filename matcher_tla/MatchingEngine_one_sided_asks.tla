---- MODULE MatchingEngine_one_sided_asks ----
(***************************************************************************)
(* Auto-generated from scenarios/one_sided_asks.json. Do not edit by hand.         *)
(*                                                                         *)
(* EXTENDS MatchingEngine and replaces Init with a seeded predicate that   *)
(* pre-fills the book (and optionally the stops set) before TLC starts     *)
(* exploring.                                                              *)
(***************************************************************************)
EXTENDS MatchingEngine

Init_Seeded ==
    /\ bidQ = [p \in PRICES |-> <<>>]
    /\ askQ = [p \in PRICES |->
          CASE p = 2 -> <<MakeOrder(1, "SELL", "LIMIT", "GTC", 2, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 1)>>
            [] p = 3 -> <<MakeOrder(2, "SELL", "LIMIT", "GTC", 3, NULL, 2, NULL, FALSE, NULL, NULL, NULL, 2)>>
            [] p = 4 -> <<MakeOrder(3, "SELL", "LIMIT", "GTC", 4, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 3)>>
            [] OTHER -> <<>>]
    /\ stops = {}
    /\ lastTradePrice = NULL
    /\ postOnlyOK = TRUE
    /\ stpOK = TRUE
    /\ nextId = 4
    /\ clock = 4
    /\ lastAction = [type |-> "SeedInit"]

=============================================================================
