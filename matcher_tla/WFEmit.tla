---- MODULE WFEmit ----
EXTENDS MatchingEngine

Shapes ==
    { <<sd, ot, tf, pr, sp, qt, dq, po, mq, sg, sl>> :
        sd \in Sides, ot \in OrderTypes, tf \in TIFs,
        pr \in PRICES \cup {NULL}, sp \in PRICES \cup {NULL},
        qt \in 1..MAX_QTY, dq \in (1..MAX_QTY) \cup {NULL},
        po \in BOOLEAN, mq \in (1..MAX_QTY) \cup {NULL},
        sg \in {NULL, "G1"}, sl \in STPPolicies \cup {NULL} }

Ord(s) == MakeOrder(1, s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8], s[9], s[10], s[11], 0)
WFShapes == { s \in Shapes : WellFormed(Ord(s)) }

ASSUME PrintT("BEGIN_WF")
ASSUME PrintT(WFShapes)
ASSUME PrintT("END_WF")
====
