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

\* Choose some arbitrary next value to write in the log. A value cannot be chosen at an index
\* that already has a chosen value.
Next == 
    \E v \in Value : 
    \E i \in Nat :
    /\ ~(\E e \in chosen : e[1] = i)
    /\ chosen' = chosen \cup {<<i, v>>}
    
Spec == Init /\ [][Next]_<<chosen>>

\* You can never mark two different values as "chosen" for the same log index.
ChosenSafety == \A i,j \in chosen : i[1] = j[1] => i = j

====
