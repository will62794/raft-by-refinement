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
    /\ logTree' = {[log |-> <<<<1, newTerm, v>>>>, children |-> {}, root |-> TRUE]}
    /\ UNCHANGED commitPoint

\* Create a new branch in term 'newTerm', starting from
\* the log section that ends at <<index, term>>.
CreateBranch(parent, newTerm, v) == 
    \* You cannot create a branch that starts in the same term as the starting term
    \* of one of your other child branches.
    /\ ~(\E c \in parent.children : c[2] = newTerm)
    \* New branches can only be created in terms newer than the parent branch.
    /\ newTerm > parent.log[Len(parent.log)][2]
    \* Append the start of the new branch to the tree.
    /\ (logTree' = (logTree \ {parent}) \cup {
            \* Add the new branch.
            [log |-> <<<<parent.log[Len(parent.log)][1] + 1, newTerm, v>>>>, children |-> {}],
            \* Update children pointers of the parent.
            [parent EXCEPT !.children = @ \cup {<<parent.log[Len(parent.log)][1] + 1, newTerm>>}]
        })
    /\ UNCHANGED commitPoint

\* Extend a branch in its own term. Note that it should be sufficient to uniquely identify
\* a branch by its term, since there should never be sibling branches that end in the
\* same term.
ExtendBranch(branch, v) == 
    \* Append a new entry to this branch in the same term.
    /\ logTree' = (logTree \ {branch}) \cup {
        [branch EXCEPT !.log = 
            Append(branch.log, <<branch.log[Len(branch.log)][1]+1, branch.log[Len(branch.log)][2], v>>)]
       }
    /\ UNCHANGED commitPoint

\* Advance the commit point to <<index, term>> on the given branch.
AdvanceCommitPoint(branch, index, term) ==
    \* The commit point cannot move backwards.
    /\ index >= commitPoint[1]
    \* The commit point cannot move to a sibling branch. It can either advance on
    \* this branch or advance to some child of this branch.
    /\ \/ \E i \in DOMAIN branch.log : branch.log[i][1] = index /\ branch.log[i][2] = term
       \/ \E c \in branch.children : c = <<index, term>>
    \* TODO: other preconditions on valid commit point advancement (?).
    /\ commitPoint' = <<index, term>>
    /\ UNCHANGED logTree

\* Log is initially empty.
\* We represent the log tree as a set of edges, where each edge is represented
\* as a "section" of log entries along with a set of child log sections.
Init == 
    /\ logTree = {}
    /\ commitPoint = <<-1,-1>>

CreateBranchAction == \E parent \in logTree, nt \in Term, v \in Value : CreateBranch(parent, nt, v)

Next == 
    \/ \E nt \in Term, v \in Value : InitBranch(nt, v)
    \/ CreateBranchAction
    \/ \E branch \in logTree, v \in Value : ExtendBranch(branch, v)
    \/ \E branch \in logTree : \E i \in DOMAIN branch.log : AdvanceCommitPoint(branch, branch.log[i][1], branch.log[i][2])

Spec == Init /\ [][Next]_vars

\* 
\* Some invariants of the log tree.
\* 

\* At any branch point, the children on all branches should have distinct terms.
BranchTermInv == 
    \A e \in logTree : \A ci,cj \in e.children : (ci[2] = cj[2]) => ci = cj

\* Paths through the log tree should increase monotonically in terms.
AllPathsMonotonic == 
    /\ \A e \in logTree : 
        /\ \A i,j \in DOMAIN e.log : j > i => e.log[i][2] >= e.log[j][2]
        /\ \A c \in e.children : c[2] >= e.log[Len(e.log)][2]

\* For any two sibling entries (i.e. neither is a descendant of the other)
\* they cannot have the same terms.
\* TODO: This may not hold yet in the above model.
DirectSiblingsHaveDistinctTerms == 
    \A branch,cbranchi,cbranchj \in logTree : 
        ( /\ cbranchi # cbranchj
          /\ <<cbranchi.log[1][1],cbranchi.log[1][2]>> \in branch.children
          /\ <<cbranchj.log[1][1],cbranchj.log[1][2]>> \in branch.children) =>
            \A i \in DOMAIN cbranchi.log :
            \A j \in DOMAIN cbranchj.log :
                \* Terms must differ.
                cbranchi.log[i][2] # cbranchj.log[j][2]
    

\* Model checking constraint.
StateConstraint == 
    /\ Cardinality(logTree) <= 3
    /\ \A e \in logTree : Len(e.log) <= 2

===============================================================================
