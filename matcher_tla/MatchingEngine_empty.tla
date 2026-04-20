---- MODULE MatchingEngine_empty ----
(***************************************************************************)
(* Auto-generated from scenarios/empty.json. Do not edit by hand.         *)
(*                                                                         *)
(* EXTENDS MatchingEngine and replaces Init with a seeded predicate that   *)
(* pre-fills the book (and optionally the stops set) before TLC starts     *)
(* exploring.                                                              *)
(***************************************************************************)
EXTENDS MatchingEngine

Init_Seeded ==
    /\ bidQ = [p \in PRICES |-> <<>>]
    /\ askQ = [p \in PRICES |-> <<>>]
    /\ stops = {}
    /\ lastTradePrice = NULL
    /\ postOnlyOK = TRUE
    /\ stpOK = TRUE
    /\ nextId = 1
    /\ clock = 1
    /\ lastAction = [type |-> "SeedInit"]

=============================================================================
