----------------------------- MODULE RaftMongoWithTermsMC -----------------------------
EXTENDS RaftMongoWithTerms

\* State Constraint. Used for model checking only.
CONSTANTS MaxTerm, MaxLogLen

MCInit == Init

\* Record all events as they occur.
MCNext ==
    \/ \E s \in Server : BecomeLeader(s)            
    \/ \E s \in Server : ClientRequest(s)           
    \/ \E s, t \in Server : GetEntries(s, t)        
    \/ \E s, t \in Server : RollbackEntries(s, t)   
    \/ \E s \in Server : CommitEntry(s)             
    
MCSpec == MCInit /\ [][MCNext]_<<vars>> \*/\ Liveness

\* Define refinement mapping.
RM == INSTANCE RaftMongo WITH Leader <- Leader,
                              Follower <- Follower,
                              globalCurrentTerm <- 0,
                              state <- Leader,
                              log <- LogsWithoutPrefixCommitted

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