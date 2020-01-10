----------------------------- MODULE RaftMongoWithTerms -----------------------------
\*
\* A lower level specification of the MongoDB replication protocol.
\*


EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* Server states.
CONSTANTS Follower, Leader

\* An empty value.
CONSTANTS Nil

(**************************************************************************************************)
(* Global variables                                                                               *)
(**************************************************************************************************)

\* Set of all immediately committed entries. 
\* Each element of the set is a record e.g. [index |-> ..., term |-> ...]
\* This set does not include "prefix committed" entries.
VARIABLE immediatelyCommitted

(**************************************************************************************************)
(* Per server variables.                                                                          *)
(*                                                                                                *)
(* These are all functions with domain Server.                                                    *)
(**************************************************************************************************)

\* The server's term number.
VARIABLE currentTerm

\* The server's state (Follower or Leader).
VARIABLE state

serverVars == <<currentTerm, state>>

\* A sequence of log entries. The index into this sequence is the index of the
\* log entry
VARIABLE log

vars == <<serverVars, log, immediatelyCommitted>>

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Generic helper operators                                                                       *)
(**************************************************************************************************)

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* Return the minimum/maximum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* Return the range of a given function.
Range(f) == {f[x] : x \in DOMAIN f}

\* Is a sequence empty.
Empty(s) == Len(s) = 0

-------------------------------------------------------------------------------------------

(******************************************************************************)
(* Next state actions.                                                        *)
(*                                                                            *)
(* This section defines the core steps of the algorithm, along with some      *)
(* related helper definitions/operators.  We annotate the main actions with   *)
(* an [ACTION] specifier to disinguish them from auxiliary, helper operators. *)
(******************************************************************************)

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term
GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index].term
LogTerm(i, index) == GetTerm(log[i], index)

\* Is it possible for log 'i' to roll back against log 'j'. 
\* If this is true, it implies that log 'i' should remove entries from the end of its log.
CanRollback(i, j) ==
    /\ Len(log[i]) > 0
    /\ \* The log with later term is more up-to-date.
       LastTerm(log[i]) < LastTerm(log[j])
    /\ \/ Len(log[i]) > Len(log[j])
       \* There seems no short-cut of OR clauses, so we specify the negative case.
       \/ /\ Len(log[i]) <= Len(log[j])
          /\ LastTerm(log[i]) /= LogTerm(j, Len(log[i]))

\* Exchange terms between two nodes and step down the Leader if needed.
UpdateTerms(i, j) ==
    \* Update terms of sender and receiver i.e. to simulate an RPC request and response (heartbeat).
    /\ currentTerm' = [currentTerm EXCEPT ![i] = Max({currentTerm[i], currentTerm[j]}),
                                          ![j] = Max({currentTerm[i], currentTerm[j]})]
    \* May update state of sender or receiver.
    /\ state' = [state EXCEPT ![j] = IF currentTerm[j] < currentTerm[i] THEN Follower ELSE state[j],
                              ![i] = IF currentTerm[i] < currentTerm[j] THEN Follower ELSE state[i] ]

UpdateTermsOnNodes(i, j) == /\ UpdateTerms(i, j)
                            /\ UNCHANGED <<log, immediatelyCommitted>>
(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Node 'i' rolls back against the log of node 'j'.                           *)
(******************************************************************************)
RollbackEntries(i, j) ==
    /\ CanRollback(i, j)
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ UpdateTerms(i, j)
    /\ UNCHANGED <<immediatelyCommitted>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Node 'i' gets a new log entry from node 'j'.                               *)
(******************************************************************************)
GetEntries(i, j) ==
    /\ state[i] = Follower
    \* Node j must have more entries than node i.
    /\ Len(log[j]) > Len(log[i])
       \* Ensure that the entry at the last index of node i's log must match the entry at
       \* the same index in node j's log. If the log of node i is empty, then the check
       \* trivially passes. This is the essential 'log consistency check'.
    /\ LET logOk == IF Empty(log[i])
                        THEN TRUE
                        ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
       /\ logOk \* log consistency check
       \* If the log of node i is empty, then take the first entry from node j's log.
       \* Otherwise take the entry following the last index of node i.
       /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE Len(log[i]) + 1
              newEntry      == log[j][newEntryIndex]
              newLog        == Append(log[i], newEntry) IN
              /\ log' = [log EXCEPT ![i] = newLog]
    /\ UpdateTerms(i, j)
    /\ UNCHANGED <<immediatelyCommitted>>
(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* A leader i commits its newest log entry.                                   *)
(******************************************************************************)
CommitEntry(i) ==
    LET ind == Len(log[i]) IN
    \E quorum \in Quorum :
        \* Must have some entries to commit.
        /\ ind > 0
        \* This node is leader.
        /\ state[i] = Leader
        \* The entry was written by this leader.
        /\ log[i][ind].term = currentTerm[i]
        \* all nodes have this log entry and are in the term of the leader.
        /\ \A s \in quorum :
            /\ Len(log[s]) >= ind
            /\ log[s][ind] = log[i][ind]        \* they have the entry.
            /\ currentTerm[s] = currentTerm[i]  \* they are in the same term.
        /\ immediatelyCommitted' = immediatelyCommitted \cup {[index |->ind, term |-> currentTerm[i]]}
        /\ UNCHANGED <<serverVars, log>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Node 'i' automatically becomes a leader, if eligible.                      *)
(******************************************************************************)

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteFor(i, j, term) ==
    LET logOk ==
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    \* Nodes can only vote once per term, and they will never
    \* vote for someone with a lesser term than their own.
    /\ currentTerm[i] < term
    /\ logOk

BecomeLeader(i) ==
    LET newTerm == currentTerm[i] + 1 IN
    \E voteQuorum \in Quorum :
        /\ i \in voteQuorum \* The new leader should vote for itself.
        /\ \A v \in voteQuorum : CanVoteFor(v, i, newTerm)
        \* Update the terms of each voter.
        /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
        /\ state' = [s \in Server |->
                        IF s = i THEN Leader
                        ELSE IF s \in voteQuorum THEN Follower \* All voters should revert to secondary state.
                        ELSE state[s]]
        /\ UNCHANGED <<log, immediatelyCommitted>>

(******************************************************************************)
(* [ACTION]                                                                   *)
(*                                                                            *)
(* Node 'i', a Leader, handles a new client request and places the entry in  *)
(* its log.                                                                   *)
(******************************************************************************)
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i]]
       newLog == Append(log[i], entry) IN
       /\ log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars, immediatelyCommitted>>

-------------------------------------------------------------------------------------------

(**************************************************************************************************)
(* Miscellaneous properties for exploring/understanding the spec.                                 *)
(**************************************************************************************************)

\* Are there two primaries in the current state.
TwoPrimaries == \E s, t \in Server : s # t /\ state[s] = Leader /\ state[s] = state[t]

NPrimaries(n) ==
    \E prims \in SUBSET Server :
        /\ \A s \in prims : state[s] = Leader
        /\ Cardinality(prims) = n

(**************************************************************************************************)
(* Correctness Properties                                                                         *)
(**************************************************************************************************)

\* The set of all log entries in a given log i.e. the set of all <<index, term>>
\* pairs that appear in the log.
LogEntries(xlog) == {<<i, xlog[i].term>> : i \in DOMAIN xlog}

\* Is <<index, term>> in the given log.
EntryInLog(xlog, index, term) == <<index, term>> \in LogEntries(xlog)

\* Is 'xlog' a prefix of 'ylog'.
IsPrefix(xlog, ylog) ==
    /\ Len(xlog) <= Len(ylog)
    /\ xlog = SubSeq(ylog, 1, Len(xlog))

\* There should be at most one leader per term.
TwoPrimariesInSameTerm ==
    \E i, j \in Server :
        /\ i # j
        /\ currentTerm[i] = currentTerm[j]
        /\ state[i] = Leader
        /\ state[j] = Leader

NoTwoPrimariesInSameTerm == ~TwoPrimariesInSameTerm
ElectionSafety == NoTwoPrimariesInSameTerm

\* Only uncommitted entries are allowed to be deleted from logs.
RollbackCommitted == \E s \in Server :
                     \E e \in immediatelyCommitted :
                        /\ EntryInLog(log[s], e.index, e.term)
                        \* And the entry got rolled back.
                        /\ Len(log'[s]) < e.index

NeverRollbackCommitted == [][~RollbackCommitted]_vars

\* At any time, some node can always become a leader.
ElectableNodeExists == \E s \in Server : ENABLED BecomeLeader(s)

(**************************************************************************************************)
(* Spec definition                                                                                *)
(**************************************************************************************************)
Init ==
    \* Server variables.
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Follower]
    \* The set of terms that each node has voted in, if any. Every node can only vote 'yes' once in a given term.
    \* Log variables.
    /\ log          = [i \in Server |-> << >>]
    /\ immediatelyCommitted = {}

BecomeLeaderAction      ==  \E s \in Server : BecomeLeader(s)
ClientRequestAction     ==  \E s \in Server : ClientRequest(s)
GetEntriesAction        ==  \E s, t \in Server : GetEntries(s, t)
RollbackEntriesAction   ==  \E s, t \in Server : RollbackEntries(s, t)
CommitEntryAction       ==  \E s \in Server : CommitEntry(s)
UpdateTermsAction       ==  \E s, t \in Server : UpdateTermsOnNodes(s, t)

Next ==
    \/ BecomeLeaderAction
    \/ ClientRequestAction
    \/ GetEntriesAction
    \/ RollbackEntriesAction
    \/ CommitEntryAction
    \* \/ UpdateTermsAction

Liveness ==
    /\ WF_vars(BecomeLeaderAction)
    \* /\ WF_vars(UpdateTermsAction)
    /\ WF_vars(GetEntriesAction)
    /\ WF_vars(RollbackEntriesAction)
    /\ WF_vars(CommitEntryAction)

Spec == Init /\ [][Next]_vars /\ Liveness

=============================================================================
\* Modification History
\* Last modified Mon Dec 02 09:00:03 EST 2019 by williamschultz
\* Last modified Sun Jul 29 20:32:12 EDT 2018 by willyschultz
\* Created Mon Apr 16 20:56:44 EDT 2018 by willyschultz
