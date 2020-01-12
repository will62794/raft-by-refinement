---- MODULE DistLog ----
\*
\* A very abstract specification of a distributed operation log.
\*

EXTENDS Sequences, Naturals, TLC, FiniteSets

\* The set of all servers.
CONSTANT Server

\* The set of all values a node can write down.
CONSTANT Value

\* The operation log of each server.
VARIABLE log

\* The chosen set of values, each stored as an <<index, value>> tuple.
VARIABLE chosen

Range(f) == {f[i] : i \in DOMAIN f}
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

\* Is a value chosen at log index 'i'. All nodes must contain the same
\* value at that index in order for it to be considered "chosen".
ChosenAt(ind) == \A s,t \in Server : 
    \E i \in DOMAIN log[s] :
    \E j \in DOMAIN log[t] :
    /\ i = ind
    /\ i = j
    /\ log[s][i] = log[t][j]

\* Append a new value to your log. You are allowed to append any value
\* if one is not already "chosen" at the slot you are going to write to i.e.
\* the next empty slot in your log.
WriteNewEntry(s, v) ==
    \* If all servers currently have the same log, then you should pick the 
    \* next value to write down.
    /\ ~ChosenAt(Len(log[s])+1)
    \* /\ \A i, j \in Server : log[i] = log[j]
    /\ log' = [log EXCEPT ![s] = Append(@, v)]
    /\ UNCHANGED <<chosen>>

\* Copy a new value from another server to your log.
AppendEntry(s, t) == 
    /\ Len(log[t]) > Len(log[s]) 
    \* copy the next entry to your log.
    /\ log' = [log EXCEPT ![s] = Append(@, log[t][Len(@) + 1])]
    /\ UNCHANGED <<chosen>>

\* If your last log value is not yet chosen, then it's always safe to delete it.    
RemoveEntry(s) == 
    /\ ~ChosenAt(Len(log[s]))
    /\ log' = [log EXCEPT ![s] = SubSeq(@, 1, Len(@)-1)]
    /\ UNCHANGED <<chosen>>

\* A server marks its last log entry as chosen.
MarkChosen(s) == 
    LET ind == Len(log[s]) IN
    /\ ChosenAt(Len(log[s]))
    \* All logs should have a chosen entry, so any one will do.
    /\ chosen' = chosen \cup {<<ind, log[s][ind]>>}
    /\ UNCHANGED <<log>>

Init == 
    /\ log = [s \in Server |-> <<>>]
    /\ chosen = {}
 
WriteNewEntryAction == \E s \in Server : \E v \in Value : WriteNewEntry(s, v)
AppendEntryAction == \E s,t \in Server : AppendEntry(s, t)
RemoveEntryAction == \E s \in Server : RemoveEntry(s)
MarkChosenAction == \E s \in Server : MarkChosen(s)
    
Next == 
    \/ WriteNewEntryAction
    \/ AppendEntryAction
    \/ RemoveEntryAction
    \/ MarkChosenAction

Liveness == 
    /\ SF_<<log, chosen>>(WriteNewEntryAction)
    /\ SF_<<log, chosen>>(AppendEntryAction)
    /\ WF_<<log, chosen>>(RemoveEntryAction)
    /\ WF_<<log, chosen>>(MarkChosenAction)

Spec == Init /\ [][Next]_<<log, chosen>> /\ Liveness

\* You can never mark two different values as "chosen" for the same log index.
ChosenSafety == \A i,j \in chosen : i[1] = j[1] => i = j

====