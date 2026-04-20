---- MODULE MatchingEngine_stops_pending ----
(***************************************************************************)
(* Auto-generated from scenarios/stops_pending.json. Do not edit by hand.         *)
(*                                                                         *)
(* EXTENDS MatchingEngine and replaces Init with a seeded predicate that   *)
(* pre-fills the book (and optionally the stops set) before TLC starts     *)
(* exploring.                                                              *)
(***************************************************************************)
EXTENDS MatchingEngine

Init_Seeded ==
    /\ bidQ = [p \in PRICES |->
          CASE p = 2 -> <<MakeOrder(1, "BUY", "LIMIT", "GTC", 2, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 1)>>
            [] OTHER -> <<>>]
    /\ askQ = [p \in PRICES |->
          CASE p = 4 -> <<MakeOrder(2, "SELL", "LIMIT", "GTC", 4, NULL, 1, NULL, FALSE, NULL, NULL, NULL, 2)>>
            [] OTHER -> <<>>]
    /\ stops = {MakeOrder(3, "SELL", "STOP_LIMIT", "GTC", 1, 2, 1, NULL, FALSE, NULL, NULL, NULL, 3), MakeOrder(4, "BUY", "STOP_LIMIT", "GTC", 5, 4, 1, NULL, FALSE, NULL, NULL, NULL, 4)}
    /\ lastTradePrice = NULL
    /\ postOnlyOK = TRUE
    /\ stpOK = TRUE
    /\ nextId = 5
    /\ clock = 5
    /\ lastAction = [type |-> "SeedInit"]

=============================================================================
