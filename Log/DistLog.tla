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

Range(f) == {f[i] : i \in DOMAIN f}
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

\* The sets of servers that can act to "choose" a value. Once a value exists on 
\* every server in one of these groups, it is considered "chosen". The simplest 
\* such group would be all servers, which we use as the default here. Less servers
\* could be used, though.
Choosers == { s \in SUBSET Server : Cardinality(s) = Cardinality(Server)}

\* Is a value chosen at log index 'i'. All nodes in some chooser group must contain the same
\* value at that index in order for it to be considered "chosen".
ChosenAt(ind, v) == 
    \E chooseGroup \in Choosers :
    \A s,t \in chooseGroup : 
        \E i \in DOMAIN log[s] :
        \E j \in DOMAIN log[t] :
        /\ i = ind
        /\ i = j
        /\ log[s][i] = log[t][j]
        /\ log[s][i] = v
    
\* The set of all chosen log entries.
AllChosen == { <<i, v>> \in (Nat \times Value) : ChosenAt(i, v) }
    
\* Append a new value to your log. You are allowed to append any value
\* if one is not already "chosen" at the slot you are going to write to i.e.
\* the next empty slot in your log.
WriteNewEntry(s, v) ==
    \* If all servers currently have the same log, then you should pick the 
    \* next value to write down.
    /\ ~\E c \in Value : ChosenAt(Len(log[s])+1, c)
    /\ log' = [log EXCEPT ![s] = Append(@, v)]

\* Copy a new value from another server to your log.
AppendEntry(s, t) == 
    /\ Len(log[t]) > Len(log[s]) 
    \* copy the next entry to your log.
    /\ log' = [log EXCEPT ![s] = Append(@, log[t][Len(@) + 1])]

\* If your last log value is not yet chosen, then it's always safe to delete it.    
RemoveEntry(s) == 
    /\ ~\E c \in Value : ChosenAt(Len(log[s]), c)
    /\ log' = [log EXCEPT ![s] = SubSeq(@, 1, Len(@)-1)]

Init == 
    /\ log = [s \in Server |-> <<>>]
 
WriteNewEntryAction == \E s \in Server : \E v \in Value : WriteNewEntry(s, v)
AppendEntryAction == \E s,t \in Server : AppendEntry(s, t)
RemoveEntryAction == \E s \in Server : RemoveEntry(s)
    
Next == 
    \/ WriteNewEntryAction
    \/ AppendEntryAction
    \/ RemoveEntryAction

Liveness == 
    /\ WF_<<log>>(WriteNewEntryAction)
    /\ WF_<<log>>(AppendEntryAction)
    /\ WF_<<log>>(RemoveEntryAction)

Spec == Init /\ [][Next]_<<log>> /\ Liveness

====