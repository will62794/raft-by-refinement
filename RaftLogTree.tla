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
    /\ logTree' = logTree \cup {
         [log |-> <<<<1, newTerm, v>>>>, children |-> {}, root |-> TRUE]
       }
    /\ UNCHANGED commitPoint

\* Create a new branch in term 'newTerm', starting from
\* the log section that ends at <<index, term>>.
CreateBranch(parent, newTerm, v) == 
    \* You cannot create a branch that starts in the same term as the starting term
    \* of one of your other child branches.
    /\ ~\E c \in parent.children : c[2] = newTerm
    \* New branches can only be created in terms newer than the parent branch.
    /\ newTerm > parent.log[Len(parent.log)][2]
    \* Append the start of the new branch to the tree.
    /\ (logTree' = (logTree \ {parent}) \cup {
            \* Add the new branch.
            [log |-> <<<<Len(parent.log) + 1, newTerm>>>>, children |-> {}],
            \* Update children pointers of the parent.
            [parent EXCEPT !.children = @ \cup {<<Len(parent.log)+1, newTerm>>}]
        })
    /\ UNCHANGED commitPoint

\* Extend the branch in term 'term'. It should be sufficient to uniquely identify
\* a branch by its term, since there should never be sibling branches that end in the
\* same term.
ExtendBranch(branch, term, v) == 
    \* Exists a section of the log that terminates in the given <<index, term>>
    /\ branch.log[Len(branch.log)][2] = term
    \* Append a new entry to this branch.
    /\ logTree' = (logTree \ {branch}) \cup {
        [branch EXCEPT !.log = Append(branch.log, <<branch.log[Len(branch.log)][1]+1, term, v>>)]
       }
    /\ UNCHANGED commitPoint

\* Advance the commit point to <<index, term>> on the given branch.
AdvanceCommitPoint(branch, index, term) ==
    \* The commit point cannot move backwards.
    /\ index >= commitPoint[1]
    \* TODO: other preconditions on valid commit point advancement.
    /\ commitPoint' = <<index, term>>
    /\ UNCHANGED logTree

\* Log is initially empty.
\* We represent the log tree as a set of edges, where each edge is represented
\* as a "section" of log entries along with a set of child log sections.
Init == 
    /\ logTree = {}
    /\ commitPoint = <<-1,-1>>

Next == 
    \/ \E nt \in Term, v \in Value : InitBranch(nt, v)
    \/ \E parent \in logTree, nt \in Term, v \in Value : CreateBranch(parent, nt, v)
    \/ \E branch \in logTree, t \in Term, v \in Value : ExtendBranch(branch, t, v)
    \/ \E branch \in logTree : \E i \in DOMAIN branch.log : AdvanceCommitPoint(branch, branch.log[i][1], branch.log[i][2])

Spec == Init /\ [][Next]_vars


\* At any branch point, the children on all branches should have distinct terms.
BranchTermInv == 
    \A e \in logTree : \A ci,cj \in e.children : ci[2] = cj[2] => ci = cj


StateConstraint == 
    /\ Cardinality(logTree) <= 3
    /\ \A e \in logTree : Len(e.log) <= 2

===============================================================================
