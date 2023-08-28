---- MODULE DistLogMC ----
EXTENDS Sequences, FiniteSets, DistLog, TLC

CONSTANT MaxLogLen

\* State constraint.
Constraint == \A s \in Server : Len(log[s]) <= MaxLogLen

EventuallyChosen == <>(Cardinality(AllChosen) > 0)

\* Instantiate the higher level spec.
L == INSTANCE Log WITH Value <- Value, chosen <- AllChosen

ChosenSafety == L!ChosenSafety

IsRefinement == L!Spec


====