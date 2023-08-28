# Refinement-based Raft Specifications

Exploring refinement based specifications of Raft consensus and log replication.

Initial abstraction levels:

- `RaftLog` - highest level of abstraction, modeling a Raft system as a single, append only log of committed entries, each associated with a value and a term.
- `RaftLogTree` - intermediate abstraction which models all logs in a Raft system as a global "log tree" abstraction, along with a commit point which represents a particular node in this tree. The idea is that the local logs of nodes in any lower level Raft implementation will map to some path in this tree, and entries are committed if they exist along a path from the root to the current commit point marker in this tree.
- `RaftAbstractStatic` - lower level but still abstract version of Raft that excludes details of message passing but that models terms, node state, local logs per node, and the set of committed entries.
