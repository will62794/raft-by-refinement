---- MODULE MCRaftLogTree ----
EXTENDS RaftLogTree, TLC 

\* Branch that starts at this (index,term)
BranchForStartEntry(index, term) == <<>>
\* CHOOSE e \in logTree : e.log[1][1] = index /\ e.log[1][2] = term 
EdgesForBranch(branch) == {<<branch.log,BranchForStartEntry(c[1], c[2])>> : c \in branch.children}

\* G ==  [node |-> {e.log : e \in logTree}, 
\*        edge |-> UNION {EdgesForBranch(e) : e \in logTree}]

Last(seq) == seq[Len(seq)]
BranchEdges(b) == {<<<<b.log[i][1],b.log[i][2]>>,<<b.log[i+1][1],b.log[i+1][2]>>>> : i \in 1..(Len(b.log)-1)}
BranchToChildrenEdges(b) == {<<<<Last(b.log)[1],Last(b.log)[2]>>, c>> : c \in b.children}

TreeNodes == UNION {{<<branch.log[i][1],branch.log[i][2]>> : i \in DOMAIN branch.log} : branch \in logTree}
TreeEdges == UNION {BranchToChildrenEdges(b) \cup BranchEdges(b) : b \in logTree}


Alias == [
    logTree |-> logTree,
    treeNodes |-> TreeNodes,
    treeEdges |-> TreeEdges
]


====