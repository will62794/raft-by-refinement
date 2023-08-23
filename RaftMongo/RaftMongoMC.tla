--------------------------------- MODULE RaftMongoMC ---------------------------------
EXTENDS RaftMongo

\* State constraint for model checking only.
StateConstraint == 
    /\ \A s \in Server : Len(log[s]) <= 3
    /\ globalCurrentTerm <= 3

Inv == ~(\E i \in Server : Len(log[i]) > 2)

\* Define refinement mapping.
RM == INSTANCE RaftMongoWithTerms WITH 
                                Server <- Server,
                                Leader <- Leader,
                                Follower <- Follower,
                                currentTerm <- [s \in Server |-> globalCurrentTerm],
                                state <- state,
                                log <- log,
                                immediatelyCommitted <- {},
                                prefixCommitted <- {}

\* Does every behavior of 'RaftMongo' satisfy 'RaftMongoWithTerms' under the refinement mapping defined above.
IsRefinement == RM!Spec

===============================================================================