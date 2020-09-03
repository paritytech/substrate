# BABE (Blind Assignment for Blockchain Extension)

BABE is a slot-based block production mechanism which uses a VRF PRNG to
randomly perform the slot allocation. On every slot, all the authorities
generate a new random number with the VRF function and if it is lower than a
given threshold (which is proportional to their weight/stake) they have a
right to produce a block. The proof of the VRF function execution will be
used by other peer to validate the legitimacy of the slot claim.

The engine is also responsible for collecting entropy on-chain which will be
used to seed the given VRF PRNG. An epoch is a contiguous number of slots
under which we will be using the same authority set. During an epoch all VRF
outputs produced as a result of block production will be collected on an
on-chain randomness pool. Epoch changes are announced one epoch in advance,
i.e. when ending epoch N, we announce the parameters (randomness,
authorities, etc.) for epoch N+2.

Since the slot assignment is randomized, it is possible that a slot is
assigned to multiple validators in which case we will have a temporary fork,
or that a slot is assigned to no validator in which case no block is
produced. Which means that block times are not deterministic.

The protocol has a parameter `c` [0, 1] for which `1 - c` is the probability
of a slot being empty. The choice of this parameter affects the security of
the protocol relating to maximum tolerable network delays.

In addition to the VRF-based slot assignment described above, which we will
call primary slots, the engine also supports a deterministic secondary slot
assignment. Primary slots take precedence over secondary slots, when
authoring the node starts by trying to claim a primary slot and falls back
to a secondary slot claim attempt. The secondary slot assignment is done
by picking the authority at index:

`blake2_256(epoch_randomness ++ slot_number) % authorities_len`.

The secondary slots supports either a `SecondaryPlain` or `SecondaryVRF`
variant. Comparing with `SecondaryPlain` variant, the `SecondaryVRF` variant
generates an additional VRF output. The output is not included in beacon
randomness, but can be consumed by parachains.

The fork choice rule is weight-based, where weight equals the number of
primary blocks in the chain. We will pick the heaviest chain (more primary
blocks) and will go with the longest one in case of a tie.

An in-depth description and analysis of the protocol can be found here:
<https://research.web3.foundation/en/latest/polkadot/BABE/Babe.html>

License: GPL-3.0-or-later WITH Classpath-exception-2.0