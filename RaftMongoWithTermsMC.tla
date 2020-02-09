----------------------------- MODULE RaftMongoWithTermsMC -----------------------------
EXTENDS RaftMongoWithTerms

\* State Constraint. Used for model checking only.
CONSTANTS MaxTerm, MaxLogLen

\* Sequence of all events that occur in the system.
VARIABLE events

MCInit == Init /\ events = <<>>

\* Record all events as they occur.
MCNext ==
    \/ \E s \in Server : BecomeLeader(s)            /\ events' = Append(events, <<"BecomeLeader", s>>)
    \/ \E s \in Server : ClientRequest(s)           /\ events' = Append(events, <<"ClientRequest", s>>)
    \/ \E s, t \in Server : GetEntries(s, t)        /\ events' = Append(events, <<"GetEntries", s, t>>)
    \/ \E s, t \in Server : RollbackEntries(s, t)   /\ events' = Append(events, <<"RollbackEntries", s, t>>)
    \/ \E s \in Server : CommitEntry(s)             /\ events' = Append(events, <<"CommitEntry", s>>)
    
MCSpec == MCInit /\ [][MCNext]_<<vars,events>> \*/\ Liveness

\*
\* Define the refinement mapping.
\*

\* Produce a state based on the sequence of events that have occurred up to the current state. 
\* The resulting state should be equivalent to the state we would get by "executing" each event in sequence.
\*
\* The variables we need to re-construct.
\* VARIABLE immediatelyCommitted
\* VARIABLE currentTerm
\* VARIABLE state
\* VARIABLE log

\* Reconstruct the log of each node
ApplyLogEvents(evs) == <<>>
    \* Look for all ClientRequest events.
    \* Look for all GetEntries events.
    \* Look for all RollbackEntries events.

ApplyEvents(evs) == [log |-> [s \in Server |-> <<>>]]
    

\* If you're the highest leader, you are the "real" leader.
MaxLeader == [s \in Server |-> IF /\ currentTerm[s] = Max(Range(currentTerm))
                                   /\ state[s] = Leader 
                                   THEN Leader ELSE Follower]
\* The highest of all terms.
MaxGlobalTerm == Max(Range(currentTerm))

\* Define refinement mapping.
RM == INSTANCE RaftMongo WITH Leader <- Leader,
                              Follower <- Follower,
                              globalCurrentTerm <- MaxGlobalTerm,
                              state <- MaxLeader,
                              log <- LogsWithoutPrefixCommitted

\*
\* Invariants and properties to check.
\*

\* Inv == \E s \in Server : Len(log[s]) < 1
\* Inv == Cardinality(prefixCommitted) < 1
Inv == Len(events) <  6
IsRefinement == RM!Spec

\*
\* Model checking helpers.
\*

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

ServerSymmetry == Permutations(Server)

=============================================================================