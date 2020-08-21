State database maintenance. Handles canonicalization and pruning in the database. The input to
this module is a `ChangeSet` which is basically a list of key-value pairs (trie nodes) that
were added or deleted during block execution.

# Canonicalization.
Canonicalization window tracks a tree of blocks identified by header hash. The in-memory
overlay allows to get any node that was inserted in any of the blocks within the window.
The tree is journaled to the backing database and rebuilt on startup.
Canonicalization function selects one root from the top of the tree and discards all other roots and
their subtrees.

# Pruning.
See `RefWindow` for pruning algorithm details. `StateDb` prunes on each canonicalization until pruning
constraints are satisfied.

License: GPL-3.0-or-later WITH Classpath-exception-2.0