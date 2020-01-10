----------------------------- MODULE RaftMongoWithTermsMC -----------------------------
EXTENDS RaftMongoWithTerms

\* State Constraint. Used for model checking only.
CONSTANTS MaxTerm, MaxLogLen

StateConstraint == \A s \in Server :
                    /\ currentTerm[s] <= MaxTerm
                    /\ Len(log[s]) <= MaxLogLen

ServerSymmetry == Permutations(Server)

\* TODO: Define refinement mapping.
\* RM == INSTANCE RaftMongo WITH Leader <- Primary,
\*                               Follower <- Secondary,
\*                               globalCurrentTerm <- 5

=============================================================================