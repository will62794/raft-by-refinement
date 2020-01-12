---- MODULE Log ----
\*
\* A very abstract specification of an operation log.
\*

EXTENDS Sequences, Naturals

\* The set of all values that can be written in the log.
CONSTANT Value

\* The operation log.
VARIABLE log

\* The log is initially empty.
Init == log = <<>>

\* Choose some arbitrary next value to write in the log.
Next == \E v \in Value : log' = Append(log, v)
    
Spec == Init /\ [][Next]_<<log>>

Constraint == Len(log) < 4
====
