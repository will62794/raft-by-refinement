----------------------------- MODULE RaftMongoWithTermsMC -----------------------------
EXTENDS RaftMongoWithTerms

\* State Constraint. Used for model checking only.
CONSTANTS MaxTerm, MaxLogLen

\* Sequence of all events that occur in the system.
VARIABLE events

MCInit == Init /\ events = <<>>

\* Record pre and post state with each event.
StateCurr == [log |-> log, currentTerm |-> currentTerm, state |-> state, immediatelyCommitted |-> immediatelyCommitted]
StateNext == [log |-> log', currentTerm |-> currentTerm', state |-> state', immediatelyCommitted |-> immediatelyCommitted']

BecomeLeaderEvent(s) == [name |-> "BecomeLeader", server |-> s, curr |-> StateCurr, next |-> StateNext]
ClientRequestEvent(s) == [name |-> "ClientRequest", server |-> s, curr |-> StateCurr, next |-> StateNext]
GetEntriesEvent(s, t) == [name |-> "GetEntries", from |-> s, to |-> t, curr |-> StateCurr, next |-> StateNext]
RollbackEntriesEvent(s, t) == [name |-> "RollbackEntries", from |-> s, to |-> t, curr |-> StateCurr, next |-> StateNext]
CommitEntryEvent(s) == [name |-> "CommitEntry", server |-> s, curr |-> StateCurr, next |-> StateNext]

\* Record all events as they occur.
MCNext ==
    \/ \E s \in Server : BecomeLeader(s)            /\ events' = Append(events, BecomeLeaderEvent(s))
    \/ \E s \in Server : ClientRequest(s)           /\ events' = Append(events, ClientRequestEvent(s))
    \/ \E s, t \in Server : GetEntries(s, t)        /\ events' = Append(events, GetEntriesEvent(s, t))
    \/ \E s, t \in Server : RollbackEntries(s, t)   /\ events' = Append(events, RollbackEntriesEvent(s, t))
    \/ \E s \in Server : CommitEntry(s)             /\ events' = Append(events, CommitEntryEvent(s))
    
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

\* Apply a single event to a given state.
ApplyEvent(ev, s) == 
    CASE 
       ev.name = "ClientRequest" ->
        LET leaderTerm == s.currentTerm[ev.server] IN
        [s EXCEPT !.log[ev.server] = <<leaderTerm>>] 
    [] ev.name = "BecomeLeader" ->
        \* TODO: Update the terms of all voters in this step, too.
        [s EXCEPT !.state[ev.server] = <<Leader>>,
                  !.currentTerm[ev.server] = s.currentTerm[ev.server] + 1 ] 
    [] OTHER -> s

\* Reconstruct the state based on a sequence of events.
RECURSIVE ApplyEvents(_,_)
ApplyEvents(evs, initState) == 
    IF Len(evs) = 0 
    THEN initState 
    ELSE ApplyEvents(Tail(evs), ApplyEvent(Head(evs), initState))

\* ApplyEvents(evs) == [log |-> [s \in Server |-> <<>>]]

\* Example initial state.
iState ==  [ currentTerm |-> (0 :> 0 @@ 1 :> 0 @@ 2 :> 0),
             immediatelyCommitted |-> {},
             log |-> (0 :> <<>> @@ 1 :> <<>> @@ 2 :> <<>>),
             state |-> (0 :> Follower @@ 1 :> Follower @@ 2 :> Follower) ]



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