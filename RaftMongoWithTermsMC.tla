----------------------------- MODULE RaftMongoWithTermsMC -----------------------------
EXTENDS RaftMongoWithTerms

\* State Constraint. Used for model checking only.
CONSTANTS MaxTerm, MaxLogLen

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

ServerSymmetry == Permutations(Server)

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
                              log <- log

Inv == \E s \in Server : Len(log[s]) < 1
IsRefinement == RM!Spec

=============================================================================