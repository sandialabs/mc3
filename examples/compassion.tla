---- MODULE compassion ----

VARIABLE st

A == 1
B == 2
C == 3

TypeInv == st \in {A, B, C}

Init == st = A

AB == st = A /\ st' = B
BA == st = B /\ st' = A
AC == st = A /\ st' = C
CC == st = C /\ st' = C

Spec == Init /\ [][AB \/ BA \/ AC \/ CC]_st /\ WF_st(BA) /\ SF_st(AC)

EventuallyC == <>(st = C)

=====================
