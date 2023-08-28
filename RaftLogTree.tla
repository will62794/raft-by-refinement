--------------------------------- MODULE RaftLogTree ---------------------------------
EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

\* 
\* Abstract model of Raft that represents the global system as a single log "tree".
\* This allows for representing the notions of concurrent terms, divergent branches of 
\* log history, and rollbacks of "stale"/uncommitted branches of history.
\* 
\* It is not, however, concerned with how such a log tree is implemented in a 
\* lower level (i.e. message passing) distributed system.
\* 

\* The set of all possible values.
CONSTANT Value

\* Set of all terms.
CONSTANT Term

\* An empty value.
CONSTANT None


\* Global log tree of Raft.
VARIABLE logTree

\* Entry (<<index, term>>) in the tree up to which 
\* everything prior is considered committed.
VARIABLE commitPoint

vars == <<logTree>>

\* Set of all log "chunks".
LogSection == Seq(Nat \X Term)

\* Represent an edge in the tree as a log section and its corresponding 
\* set of "children" log sections.
TreeEdge == [
    log : LogSection, 
    \* Children are pointers to the beginning of log sections.
    children: SUBSET (Nat \X Term)
]

\* Create an initial branch, starting from an empty log tree.
InitBranch(newTerm, v) ==
    /\ logTree = {}
    /\ logTree' = {[entry |-> <<1, newTerm, v>>, children |-> {}]}
    /\ UNCHANGED commitPoint

\* Create a new branch in term 'newTerm', starting from
\* the log section that ends at <<index, term>>.
CreateBranch(parent, newTerm, v) == 
    \* New branches can only be created in terms newer than the parent branch.
    /\ newTerm > parent.entry[2]
    \* You cannot create a branch that would start in the same term as a sibling
    \* branch. When we create a new branch, we start it in a newer term than the
    \* current branch, so to enforce this it is sufficient to require that the
    \* new term is also distinct from any existing term in the tree.
    /\ ~\E s \in logTree : s.entry[2] = newTerm
    \* Append the start of the new branch to the tree.
    /\ (logTree' = 
        (logTree \ {parent}) \cup {
            \* Add the entry on the new branch and a pointer to it.
            [parent EXCEPT !.children = @ \cup {<<parent.entry[1] + 1, newTerm>>}],
            [entry |-> <<parent.entry[1]+1, newTerm, v>>, children |-> {}]
        })
    /\ UNCHANGED commitPoint

\* Extend a branch in its own term. Note that it should be sufficient to uniquely identify
\* a branch by its term, since there should never be sibling branches that end in the
\* same term.
ExtendBranch(parent, v) == 
    \* Cannot extend a branch from an entry that already has a child in its own term.
    /\ ~\E c \in parent.children : c[2] = parent.entry[2]
    \* Append a new entry to this branch in the same term.
    /\ logTree' = (logTree \ {parent}) \cup {
        \* Add edge pointing to new child and new entry.
        [parent EXCEPT !.children = @ \cup {<<parent.entry[1]+1, parent.entry[2]>>}],
        [entry |-> <<parent.entry[1]+1, parent.entry[2],v>>, children |-> {}]
       }
    /\ UNCHANGED commitPoint

\* Advance the commit point to <<index, term>> on the given branch.
AdvanceCommitPoint(branch, index, term) ==
    \* TODO: other preconditions on valid commit point advancement (?).
    \* The commit point cannot move backwards.
    /\ index >= commitPoint[1]
    \* The commit point cannot move to a sibling branch. It can either advance on
    \* this branch or advance to some child of this branch.
    \* /\ \/ \E i \in DOMAIN branch.log : branch.log[i][1] = index /\ branch.log[i][2] = term
    \*    \/ \E c \in branch.children : c = <<index, term>>
    /\ commitPoint' = <<index, term>>
    /\ UNCHANGED logTree

\* 
\* The overall log structure is initially empty.
\* 
\* We represent the log tree as a set of edges, where each nodes represents a single 
\* log entry.
\* 
Init == 
    /\ logTree = {}
    /\ commitPoint = <<-1,-1>>

CreateBranchAction == \E parent \in logTree, nt \in Term, v \in Value : CreateBranch(parent, nt, v)
ExtendBranchAction == \E branch \in logTree, v \in Value : ExtendBranch(branch, v)

Next == 
    \/ \E nt \in Term, v \in Value : InitBranch(nt, v)
    \/ CreateBranchAction
    \/ ExtendBranchAction
    \* \/ \E branch \in logTree : \E i \in DOMAIN branch.log : AdvanceCommitPoint(branch, branch.log[i][1], branch.log[i][2])

Spec == Init /\ [][Next]_vars

\* 
\* Some invariants of the log tree.
\* 

\* Checks if one edge ep is a parent of ec.
Parent(ep,ec) == <<ec.entry[1],ec.entry[2]>> \in ep.children

\* Check if an edge is a root i.e. has no parents.
IsRoot(e) == \A p \in logTree : ~Parent(p,e)

\* At any branch point, the children on all branches should have distinct terms.
BranchTermInv == 
    \A e \in logTree :
    \A ci,cj \in e.children : 
        ci # cj => ci[2] # cj[2]

\* Paths through the log tree should increase monotonically in terms.
AllPathsMonotonic == 
    \A e \in logTree : 
    \A c \in e.children :
        c[2] >= e.entry[2]

\* For any two sibling entries (i.e. neither is a descendant of the other)
\* they cannot have the same terms.
\* TODO: This may not hold yet in the above model.
DirectSiblingsHaveDistinctTerms == 
    \A ei,ej \in logTree : 
        (/\ ei # ej
         /\ ei.entry = ej.entry 
         /\ ei.child # None 
         /\ ej.child # None) =>
            ei.child[2] # ej.child[2]

\* Check that a non-empty log tree structure is actually a valid tree.
NonEmptyTreeInv ==
    \* There should be a unique root. 
    \E root \in logTree :
        /\ IsRoot(root)
        /\ \A e \in logTree \ {root} : ~IsRoot(e) 
        \* Parent validity for each non-root edge.
        /\ \A b \in logTree \ {root} :
            \* For each non root branch, there exists a parent.
            /\ \E par \in logTree : Parent(par, b)
            \* Parents are unique.
            /\ \A par1,par2 \in logTree : 
                (Parent(par1, b) /\ Parent(par2, b)) => par1 = par2

TreeInv == (logTree # {}) => NonEmptyTreeInv


\* 
\* Model checking constraint.
\* 
StateConstraint == 
    /\ Cardinality(logTree) <= 6

Check == Cardinality(logTree) < 5

===============================================================================
