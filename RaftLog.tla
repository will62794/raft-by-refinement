--------------------------------- MODULE RaftLog ---------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* 
\* Highest level abstract model of Raft that views the whole system as a single global, append-only log.
\* of committed/durable entries.
\* 

CONSTANT Value

CONSTANT Term

\* Global log of Raft.
VARIABLE log

vars == <<log>>

\* Log is initially empty.
Init == log = <<>>

Next == 
    \E t \in Term, v \in Value : 
        /\ \/ log = <<>>
           \/ log # <<>> /\ t >= log[Len(log)][1]
        /\ log' = Append(log, <<t, v>>)

Spec == Init /\ [][Next]_vars

===============================================================================
