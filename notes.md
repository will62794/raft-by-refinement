## January 10, 2020

Reproduced a simple case of refinement violation.

```
<Init>
/\ RM!ClientWrite(n1) = FALSE
/\ MaxLeader = (n1 :> Follower @@ n2 :> Follower @@ n3 :> Follower)
/\ MaxGlobalTerm = 0
/\ RM!Next = TRUE
/\  currentTerm = (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)
/\  immediatelyCommitted = {}
/\  log = (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>)
/\  state = (n1 :> Follower @@ n2 :> Follower @@ n3 :> Follower)

<BecomeLeader>
/\ RM!ClientWrite(n1) = FALSE
/\ MaxLeader = (n1 :> Leader @@ n2 :> Follower @@ n3 :> Follower)
/\ MaxGlobalTerm = 1
/\ RM!Next = TRUE
/\  currentTerm = (n1 :> 1 @@ n2 :> 1 @@ n3 :> 0)
/\  immediatelyCommitted = {}
/\  log = (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>)
/\  state = (n1 :> Leader @@ n2 :> Follower @@ n3 :> Follower)

<BecomeLeader>
/\ RM!ClientWrite(n1) = FALSE
/\ MaxLeader = (n1 :> Follower @@ n2 :> Leader @@ n3 :> Follower)
/\ MaxGlobalTerm = 2
/\ RM!Next = FALSE
/\  currentTerm = (n1 :> 1 @@ n2 :> 2 @@ n3 :> 2)
/\  immediatelyCommitted = {}
/\  log = (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>)
/\  state = (n1 :> Leader @@ n2 :> Leader @@ n3 :> Follower)

<ClientRequest>
/\ RM!ClientWrite(n1) = "--"
/\ MaxLeader = (n1 :> Follower @@ n2 :> Leader @@ n3 :> Follower)
/\ MaxGlobalTerm = 2
/\ RM!Next = "--"
/\  currentTerm = (n1 :> 1 @@ n2 :> 2 @@ n3 :> 2)
/\  immediatelyCommitted = {}
/\  log = (n1 :> <<[term |-> 1]>> @@ n2 :> <<>> @@ n3 :> <<>>)
/\  state = (n1 :> Leader @@ n2 :> Leader @@ n3 :> Follower)
```

It is the case I expected to see i.e. a leader writing down an entry in a stale term when there is a newer leader. Plan to update the refinement mapping to try to handle this case. TLA+ Toolbox Trace Explorer is very helpful for debugging refinement checking violations.

## January 12, 2020

Exploring a basic refinement example of an operation log in the `Log/` directory. Intention is for `DistLog` to be a refinement of `Log`, a very abstract spec of an operation log where unique values are atomically chosen for each log slot.

Can now "choose" i.e. commit log values out of order in `Log.tla` so I think `DistLog` should be a valid refinement of `Log`.

TODO: I would like to get rid of the separate `MarkChosen` action inside DistLog and just define the current chosen set as a function of the `log` variable. 

## January 20, 2020

Goals:

 - Demonstrate refinement between very high level consensus log protocol and a lower level distributed, synchronous implementation. 
 - Demonstrate refinement mapping between distributed, synchronous consensus log and a distributed message passing implemention

Design by refinement strategy: specify things at a level so abstract that the hard parts become trivial. For example, reading a global state of a distributed system. Then, refine the spec by figuring out how to "implement" the things that you judge wouldn't actually be possible in real system. This perhaps takes judgement on the part of the designer to know what things can actually be implemented in reality and those which can't. That seems to be a combination of algorithm design and engineering. Moving slowly down the abstraction layers might make this process much easier, though, as opposed to trying to come up with a distributed algorithm out of thin air, without thinking first about the very high level, abstract structure of such a protocol. In some ways, this is similar to a technique of "start with the simplest possible design first", and then figure out where it's *too* simple and work out how to fill in those details.

For example, I've currently defined `WriteNewEntry` in `DistLog.tla` as :

```tla
\* Append a new value to your log. You are allowed to append any value
\* if one is not already "chosen" at the slot you are going to write to i.e.
\* the next empty slot in your log.
WriteNewEntry(s, v) ==
    /\ ~ChosenAt(Len(log[s])+1)
    /\ log' = [log EXCEPT ![s] = Append(@, v)]
    /\ UNCHANGED <<chosen>>
```

The first pre-condition in that action is very powerful, which is part of why the action definition is so simple. It isn't possible to check that pre-condition atomically in a real system, though, because it examines the global state of the system. So, in a refined version of this spec, we need to figure out how to map that into a real "implementation". The essential part of the pre-condition has to do with the fact that we are checking which values are already chosen. If a value hasn't been chosen at a particular log slot, then we're free to write down a new entry there.

### How to Derive Consensus Log Protocol

Part of the design constraints for coming up with a distributed operation log are based around fault tolerance. If you have multiple nodes that each maintain a log and you want each of them to always write down the same log entries in the same order, one of the simplest ways to ensure this is to just pick some leader process that chooses each entry and then tells the other nodes as it writes them down. This works fine, and its correctness is probably trivial to verify. Its flaw, though, is that it doesn't meet the constraint of "no single point of failure". So, while that is a valid approach to solve log consensus, it doesn't satisfy all the properties we want for such a protocol. Such a protocol must be able to somehow "recover" and make progress if a leader process goes down, for example. So, the single leader approach doesn't work. We could instead allow every node to act as a potential "leader" concurrently, with some way to handle potential conflicts between the nodes. It's clear to see how this can immediately lead to some problems, though, depending on how we designed the protocol. For example, if two nodes concurrently write down different entries at the same slot

```
n1: <<v1, v2>>
n2: <<v1, v3>>
```
we may have a safety violation, if they apply these entries immediately. Maybe we can still allow concurrent leaders, as long as we have some way to carefully manage when we decide that an entry at a particular slot is actually "chosen". Note that we may also run into liveness issues if there are concurrent leaders and we have no way to delete log entries. If, for example, we require a log entry to reach all nodes to be "chosen", then conflicting entries may indefinitely prevent entries from becoming chosen, halting progress.

In the original protocol with only a single, fixed leader, it was easy to say that an entry was "chosen" as soon as the leader wrote it down, since we knew there would never be anything to conflict with that entry. If we allow multiple leaders concurrently, can we come up with some way to resolve the conflict issue shown in the example above? Well, we can always resolve conflicts by arbitrarily choosing some winner. So, in the above example, we could say that `v3` is the "winning" value, for whatever reason, and we force `n1` to abide by that and remove its last log entry:
```
state 0:
n1: <<v1, v2>>
n2: <<v1, v3>>

state 1:
n1: <<v1>>
n2: <<v1, v3>>
```
So, how would we decide which entries get to "win" a conflict? If values are assigned some arbitrary total ordering, we could decide winners based on that ordering i.e. higher ordered values win.

This gets us closer to our goal, but we also have the remaining issue of how to define when a log entry is "chosen". We need some definition such that once an entry becomes "chosen", no other entry can become chosen at the same log slot. If we are going to give some arbitrary total order (let's call this ordering the "priority" of the log value) to values in the log, then one thing we need to be careful of is to not write down a log value with a higher priority into a slot that has already been chosen, since, in that case, we may decide to choose this new entry as the conflict winner against an already chosen value at some slot. 

Summarizing some of the key design constraints:

- Multiple nodes can act as leader to provide necessary fault tolerance properties.
- Since we can have multiple leaders, we need a way to resolve conflicts between concurrent log entries.
- Must ensure that leaders don't choose a value with a higher priority than some already chosen value at a particular slot.

Note 1: None of these design constraints say anything about a distributed system. We might want to implement a distributed protocol that satisfies these constraints, but the protocol doesn't fundamentally need to be distributed.

Note 2: As an alternative to having multiple "concurrent" leaders, we could also try to still have only a single leader, but allow that leader to change over time. Every new leader could pick up where the last leader "left off". If a current leader fails, we need some protocol to select the next leader. This seems to bring its own challenges. Defaulting to many concurrent leaders may be the more natural, initial approach.

So, we now have a protocol where we can have multiple, concurrent leaders that can each write down potentially different log entries. If two logs have differing values at the same index, then we break the conflict by looking at the value priority, which is some arbitrary ordering. Because of this conflict resolution strategy, we need to make sure that we "choose" values safely. If, for example, we say that a value is "chosen" at a particular log slot once it is present on two servers in that slot, then we need to make sure that any leader who is going to subsequently write down a new log entry must not clobber that entry with a higher priority value. How can we prevent this? Well, we need to make sure that nodes do some checks before unconditionally writing down a new log entry in a particular slot. They can check to see what entries are presently committed, by asking other nodes. If they ask around and see that a log entry is present on two nodes at a particular slot, then they can't write down any entry in that slot. They can only write down the entry that was already committed. 

In a distributed system, how might we do the "asking around" phase? If they ask two separate nodes, `n1` and `n2`, what log entry they have at index `i`, for example, and both nodes respond with some answer, can we be sure that the responses have told us that a value is committed or not? Well, it's possible that at the time `n1` responded it did not have some value, but subsequently received it. Similarly for `n2`. So, we need a better way to check on "committed" values, since messages returned to us might always reflect stale data.

TODO: `DistLog` is not a refinement of `Log` after recent changes since it is possible for `DistLog` to add multiple entries to the "chosen" set in a single step, which `Log` doesn't allow. I could alter `Log` so that it can write down an arbitrary number of log entries in a single action. 

Altered `Log.tla` to be more general so that it can write any number of entries down in its log atomically. This now allows `DistLog` to be a refinement of `Log`.

## February 5, 2020

More thoughts about Paxos and how it is able to "implement" a protocol that satisfies the right high level properties. One of the things it needs to do is "read" any previously chosen value before proposing a new value. In a very abstract view, we can imagine that a node/process knows what other values are 
instantaneously, by inspecting the global state. For example, if a value is chosen when every node has accepted it, we won't write down a new conflicting value if everyone has already accepted a different value. In a real distributed system, though, you can't do this kind of operation atomically i.e. you can't read global state atomically. So, how do you implement this check so that it appears "as if" it were atomic? Well, in most concurrent programs we use locking to provide atomicity. That is, you protect a critical section of reads/writes with a lock and it makes this section of code appear as if it happens atomically to other threads/processes. Could we use a lock for a Paxos like protocol? When you want to check if any value has been previously chosen, this involves reading from some subset of nodes. After you do this read you then write down your new proposal. At the time of writing it down, you are sure that no previous, conflicting value was chosen because the read and write were atomic. To ensure this in a real system, you could go around and take out a lock on the subset of nodes you are reading from, then check if they have accepted a value, then write your new value if now previous value was chosen, and then go around and release your locks on each node. I think this approach can work, but it runs into the same old liveness issues when failure is thrown into the mix i.e. if a process fails while its locks are held, how do the locks ever get released to allow other nodes to make progress? This is how such a protocol can get stuck. 

Instead of using locks, directly, though, can we use an alternate mechanism that gives the same guarantees as a lock, but without the downsides when nodes fail? If we think more about what a lock does, it is partially about controlling visibility. For example, if reads and writes are the primitive operations of a system, and we protect the reads and writes of one process P's critical section with a lock, we are guaranteeing that (1) all reads by subsequent holders of the lock see the effects of P's writes and (2) P observes the effects of the writes of any prior processes. Note that this depends on the notion of a total ordering between processes, which is what a lock provides to you i.e. only 1 process gets access to the critical section at any one time, which gives a total order on processes. In the abstract, though, we can also consider a lock as a mechanism for enforcing such an ordering, but one that might be stricter than necessary. For example, if we have 2 processes, P1 and P2, and we say that P1 gets to execute its critical section first followed by P2, a lock would order all the operations of P1 strictly before the operations of P2. To satisfy the requirements of (1) and (2) above, though, we could allow some interleaving in some cases, though. For example, If P1 writes key K1 once and then reads K2, P2 should be allowed to read K1 in its process as soon as the write from P1 finished, since it will never be changed by P1 again. This is just like the idea of serializable transactions i.e. we can re-order the operations from each process in such a way that is equivalent to some serialized execution even if in practice they weren't actually serialized.

Other separate thoughts on how to think about "globalCurrentTerm" as an abstraction of "term per node" spec. Log entries in Raft that are written down by a primary node in a stale term (i.e. after a newer primary has been elected) can never become immediately committed in the future. They can only be prefix committed. That is, they may survive to future terms by "chance", but there's no guarantee of their survival. So, could we consider an abstraction of the spec where we just "delete" all log entries that are prefix committed and only look at the log entries that were "immediately" committed? We could record any log entries that were written on a node not in the newest global term, and remove those from all logs via our abstraction function/refinement mapping. This is one thought on how to think about how "globalCurrentTerm" is an abstraction of "term per node". And "prefix committed" nodes are arguably less interesting from a safety persppective, because the protocol doesn't actually need to make any guarantee that they survive.

Also, what does spec look like if we are allowed to re-order events in accordance with their partial ordering? For example, a stale primary doing a write concurrently with a different primary writing log entries. We should be free to re-order these events since they are logically concurrent.

---

Attempted to update refinement mapping between `RaftMongoWithTerms` and `RaftMongo` by tracking the set of 'prefixCommitted' entries explicitly in `RaftMongoWithTerms` and deleting them from the logs of all nodes in the refinement mapping. Ran into some early violations of refinement in cases where a newer log entry (in term 2, for example) causes log entries in term 1 to roll back even though the log entry in term 2 in not committed in its own term and only has the potential to become prefix committed. Need to think more on this. My approach might be going in the wrong direction here.

## February 8, 2020

When trying to define a mapping between 'RaftMongo' and 'RaftMongoWithTerms', what are the main differences? In 'RaftMongo', once a leader has been elected in a new term, a stale leader in an older term cannot continue to write down log entries in its older term. It is as if everyone voted for the new leader and all older leaders stepped down atomically with the new election succeeding. So, any transition in the low level spec where a primary writes down a log entry in an older term, after a new primary has been elected, would not map to any transition in the abstract spec, since the globalCurrentTerm should have already advanced. So, how can we potentially define a refinement mapping that takes this into account? Well, one thing to note is that entries written down by a stale leader are concurrent with actions taken by nodes or leaders in a newer term. So, it is acceptable to re-order these events in such a way to make them appear as if they occurred strictly before the actions in the new term i.e. we can re-order them to make it appear they happened before the election in a newer term.

All the events executed by a stale leader can be ordered before the events in the newer term until that node communicates with some other node that knows about the newer term. At this point its subsequent events then need to be ordered after the events of the new term. By the normal rules of Raft, once an old leader communicates with a node in a newer term, though, it will necessarily step down, so after it communicates, it won't be able to write any new log entries in the older term. In normal Raft, it also isn't allowed for a node with a lower term to send a log entry to a node with a higher term. So, logs can't cross term boundaries in that way.

How to "dynamically" re-order events in spec/model in a way that satisfies the partial order of events but might be a different sequence of global states i.e. a different behavior?

## February 9, 2020

Started an attempt to implement refinement mapping based on re-ordering partially ordered events. My first, brute force attempt is to record all events during execution and have a way to virtually "execute" them after some re-ordering of my choosing. The refinement mapping will then do this re-ordering and "virtual execution" to map each state in the lower level spec to a state in the higher level spec.

## May 3, 2020

After reading some of [Reduction in TLA](https://www.microsoft.com/en-us/research/publication/reduction-in-tla/) paper and this Google Groups thread on "[Invariance under transition order](https://groups.google.com/forum/#!searchin/tlaplus/invarianceunder%7Csort:date/tlaplus/jQysUDDZaAI/joxCp7xnDwAJ)", this gave me some ideas for how to show some kind of "equivalence" between high level RaftMongo and lower level spec that models terms. Roughly, the idea is to first re-order actions in the behavior that commute until you have moved all actions that occur in the same term to be contiguous. Then, once you have done this re-ordering, you can somehow show that it is "valid" to execute all actions of a single term as if they were a single atomic step. My thought now is that if we have an even more abstract spec that executes all events of a single term in an atomic step, then we can demonstrate a "reduction" of the lower level RaftMongoWithTerms spec to this higher level one, by the action re-ordering and compaction techniques. Started working on such a spec [here](https://gist.github.com/will62794/04cf79cd4dfc26ca239cc3f1e39ce428).
