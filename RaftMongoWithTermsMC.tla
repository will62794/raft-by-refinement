----------------------------- MODULE RaftMongoWithTermsMC -----------------------------
EXTENDS RaftMongoWithTerms

\* State Constraint. Used for model checking only.
CONSTANTS MaxTerm, MaxLogLen

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

ServerSymmetry == Permutations(Server)

\* TODO: Define refinement mapping.
RM == INSTANCE RaftMongo WITH Leader <- Leader,
                              Follower <- Follower,
                              globalCurrentTerm <- Max(Range(currentTerm)),
                              state <- [s \in Server |-> 
                                            \* If you're the highest leader, you are the "real" leader.
                                            IF /\ currentTerm[s] = Max(Range(currentTerm))
                                               /\ state[s] = Leader 
                                            THEN Leader
                                            ELSE Follower
                                        ],
                              log <- log

IsRefinement == RM!Spec

=============================================================================