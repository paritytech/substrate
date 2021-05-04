# Proof-of-Capacity (PoC) Consensus

PoC is a slot-based block production mechanism which uses a Proof-of-Capacity to
randomly perform the slot allocation. On every slot, all the farmers evaluate
their disk-based plot. If they have a tag (reflecting a commitment to a valid
encoding) that it is lower than a given threshold (which is proportional to
the total space pledged by the network) they may produce a new block. The
proof of the PoR function execution will be used by other peers to validate
the legitimacy of the slot claim.

The engine is also responsible for collecting entropy on-chain which will be
used to seed the given PoR challenge. An epoch is a contiguous number of slots
under which we will be using the same base PoC challenge. During an epoch all PoR
outputs produced as a result of block production will be collected into an
on-chain randomness pool. Epoch changes are announced one epoch in advance,
i.e. when ending epoch N, we announce the parameters (i.e, new randomness)
for epoch N+2.

Since the slot assignment is randomized, it is possible that a slot is
claimed by multiple farmers, in which case we will have a temporary fork,
or that a slot is not claimed by any farmer, in which case no block is
produced. This means that block times are probabalistic.

The protocol has a parameter `c` [0, 1] for which `1 - c` is the probability
of a slot being empty. The choice of this parameter affects the security of
the protocol relating to maximum tolerable network delays.

The fork choice rule is weight-based, where weight equals the number of
primary blocks in the chain. We will pick the heaviest chain (more
blocks) and will go with the longest one in case of a tie.

This module is based on a fork of `sc_consensus_babe`.  An in-depth description and analysis of the BABE protocol, can be found here:
<https://research.web3.foundation/en/latest/polkadot/block-production/Babe.html>

For a more in-depth analysis of Subspace PoR consensus can be found in our [technical whitepaper](https://drive.google.com/file/d/1v847u_XeVf0SBz7Y7LEMXi72QfqirstL/view)

License: GPL-3.0-or-later WITH Classpath-exception-2.0