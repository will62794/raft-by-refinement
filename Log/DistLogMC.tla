---- MODULE DistLogMC ----
EXTENDS Sequences, FiniteSets, DistLog, TLC

CONSTANT MaxLogLen

EventuallyChosen == <>(Cardinality(chosen) > 0)

Constraint == \A s \in Server : Len(log[s]) <= MaxLogLen

L == INSTANCE Log WITH Value <- Value, chosen <- AllChosen

IsRefinement == L!Spec

====