---- MODULE WFEmit ----
EXTENDS MatchingEngine

\* WFShapes, OrderShapes and ShapeToOrder are defined once, in
\* MatchingEngine.tla (hoisted out of SubmitOrder). This module only prints
\* the inherited set for the Lean/TLA+ well-formedness differential -- it
\* must not re-derive its own copy, or the two copies can silently drift
\* apart from each other as well as from Lean's.

ASSUME PrintT("BEGIN_WF")
ASSUME PrintT(WFShapes)
ASSUME PrintT("END_WF")
====
