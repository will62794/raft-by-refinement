--------------------------------- MODULE RaftMongoMC ---------------------------------
EXTENDS RaftMongo

\* State constraint for model checking only.
StateConstraint == 
    /\ \A s \in Server : Len(log[s]) <= 3
    /\ globalCurrentTerm <= 3

Inv == ~(\E i \in Server : Len(log[i]) > 2)

===============================================================================