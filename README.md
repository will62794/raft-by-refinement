# Refinement-based Raft Specifications

Experimental, refinement-based specifications of Raft consensus, with the following initial abstraction levels:

- **RaftLog** - highest level of abstraction, modeling a Raft system as a single, append only log of committed entries, each associated with a value and a term.
- **RaftLogTree** - intermediate abstraction which models all logs in a Raft system as a global "log tree" abstraction, along with a commit point which represents a particular node in this tree. The idea is that the local logs of nodes in any lower level Raft implementation will map to some path in this tree, and entries are committed if they exist along a path from the root to the current commit point marker in this tree.
- **RaftAbstractStatic** - lower level but still abstract version of Raft that excludes details of message passing but that models terms, node state, local logs per node, and the set of committed entries.

## Visualizing Raft Log Trees

If you set up the `RaftLogTree.cfg` config to check an invariant that is expected to fail, you can visualize the resulting Raft log tree structure in the final state of the error trace with the following commands:
```bash
$ java -cp lib/tla2tools.jar tlc2.TLC -noGenerateSpecTE -dumpTrace json trace.json -simulate RaftLogTree
$ python3 logtree.py # will output rendered log tree to 'logtree.pdf'.
```
