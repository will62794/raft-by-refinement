----------------------------- MODULE RaftMongoWithTermsMC -----------------------------
EXTENDS RaftMongoWithTerms

\* State Constraint. Used for model checking only.
CONSTANTS MaxTerm, MaxLogLen

\* The highest of all terms.
MaxGlobalTerm == Max(Range(currentTerm))

\* If you're the highest leader, you are the "real" leader.
MaxLeader == [s \in Server |-> IF /\ currentTerm[s] = Max(Range(currentTerm))
                                   /\ state[s] = Leader 
                                   THEN Leader ELSE Follower]

MCInit == Init

\* If there is a stale primary who can do a write, prefer that action over any other.

StalePrimaryExists == 
    \E s,t \in Server : 
        /\ state[s] = Leader
        /\ state[t] = Leader
        /\ currentTerm[s] < currentTerm[t]

\* Client request that is executed on a stale primary.        
ClientRequestOnStalePrimary(s) == 
    /\ \E t \in Server : state[t] = Leader /\ currentTerm[t] > currentTerm[s]
    /\ ClientRequest(s)

\* A client request action that always defers to writes on stale primaries i.e. it lets
\* them go first. The correctness argument is that a client request i.e. a write on a stale primary
\* has no causal relationship with any client request in a newer term. That is, the stale write
\* is completely concurrent with the rest of the system. So, it should be safe to execute
\* these operations in either order, which means it's fine to just pick one of the orderings, since
\* both are effectively equivalent.
ClientRequestCommuted(s) == ~StalePrimaryExists  /\ ClientRequest(s)

\* If the election of a new leader while there is still a stale primary around would garner votes from a 
\* quorum of nodes that don't include the stale primary, then there is no causal relationship between
\* writes done on a stale primary and the new election. So, it should be fine to just pick an ordering i.e.
\* we let the stale primary go first.
BecomeLeaderCommuted(s) == 
    /\ ~(\E t \in Server : s # t /\ state[t] = Leader)
    /\ BecomeLeader(s)

MCNext ==
    \/ \E s \in Server : BecomeLeaderCommuted(s)       
    \/ \E s, t \in Server : GetEntries(s, t)        
    \/ \E s, t \in Server : RollbackEntries(s, t)   
    \/ \E s \in Server : CommitEntry(s)     
    \/ \E s \in Server : ClientRequestCommuted(s)
    \/ \E s \in Server : ClientRequestOnStalePrimary(s)
        
MCSpec == MCInit /\ [][MCNext]_<<vars>> \*/\ Liveness

\* Define refinement mapping.
RM == INSTANCE RaftMongo WITH Leader <- Leader,
                              Follower <- Follower,
                              globalCurrentTerm <- MaxGlobalTerm,
                              state <- MaxLeader,
                              log <- log

\*
\* Invariants and properties to check.
\*

\* Inv == \E s \in Server : Len(log[s]) < 1
\* Inv == Cardinality(prefixCommitted) < 1
IsRefinement == RM!Spec

\*
\* Model checking helpers.
\*

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

ServerSymmetry == Permutations(Server)

=============================================================================