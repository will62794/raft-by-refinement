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

\* The sets of servers that can act to "choose" a value. Once a value exists on 
\* every server in one of these groups, it is considered "chosen". The simplest 
\* such group would be all servers, which we use as the default here. Less servers
\* could be used, though.
Choosers == { s \in SUBSET Server : Cardinality(s) = Cardinality(Server)}

\* Is a value chosen at log index 'i'. All nodes in some chooser group must contain the same
\* value at that index in order for it to be considered "chosen".
ChosenAt(ind) == 
    \E chooseGroup \in Choosers :
    \A s,t \in chooseGroup : 
        \E i \in DOMAIN log[s] :
        \E j \in DOMAIN log[t] :
        /\ i = ind
        /\ i = j
        /\ log[s][i] = log[t][j]
    
\* The set of all indices/entries in the log of a given server.
ChosenIndices(s) == { i \in DOMAIN log[s] : ChosenAt(i) } 
ChosenEntries(s) == { <<i, log[s][i]>> : i \in ChosenIndices(s) } 

\* The set of all chosen log entries.
AllChosen == UNION { ChosenEntries(s) : s \in Server }

\* Append a new value to your log. You are allowed to append any value
\* if one is not already "chosen" at the slot you are going to write to i.e.
\* the next empty slot in your log.
WriteNewEntry(s, v) ==
    \* If all servers currently have the same log, then you should pick the 
    \* next value to write down.
    /\ ~ChosenAt(Len(log[s])+1)
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

Init == 
    /\ log = [s \in Server |-> <<>>]
    /\ chosen = {}
 
WriteNewEntryAction == \E s \in Server : \E v \in Value : WriteNewEntry(s, v)
AppendEntryAction == \E s,t \in Server : AppendEntry(s, t)
RemoveEntryAction == \E s \in Server : RemoveEntry(s)
    
Next == 
    \/ WriteNewEntryAction
    \/ AppendEntryAction
    \/ RemoveEntryAction

Liveness == 
    /\ SF_<<log, chosen>>(WriteNewEntryAction)
    /\ SF_<<log, chosen>>(AppendEntryAction)
    /\ WF_<<log, chosen>>(RemoveEntryAction)

Spec == Init /\ [][Next]_<<log, chosen>> /\ Liveness

\* You can never mark two different values as "chosen" for the same log index.
ChosenSafety == \A i,j \in chosen : i[1] = j[1] => i = j

====