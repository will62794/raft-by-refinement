---- MODULE Log ----
\*
\* A very abstract specification of an operation log.
\*

EXTENDS Sequences, Naturals, FiniteSets

\* The set of all values that can be written in the log.
CONSTANT Value

\* The operation log, which is represented abstractly as a set of <<index, value>> elements, that
\* represent the value chosen at each index of the log.
VARIABLE chosen

\* The log is initially empty.
Init == chosen = {}

\* Choose some arbitrary next value to write in the log.
Next == \E v \in Value : chosen' = chosen \cup {<<(Cardinality(chosen)+1), v>>}
    
Spec == Init /\ [][Next]_<<chosen>>

Constraint == Cardinality(chosen) < 4
====
