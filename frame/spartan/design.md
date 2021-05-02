## Spartan Design Document

### Overview

This repository contains an implementation of Spartan Proof-of-Capacity (PoC) consensus for the Substrate framework, organized as Substrate pallet and several dependencies. It is largely based on a fork of `pallet_babe`, with which it shares many similarities.

Spartan is a simple and secure PoC consensus protocol, which replaces 'one-cpu-one-vote' with 'one-disk-one-vote'. This allows for mass participation in consensus by ordinary users with commodity hardware.
Since PoC consensus is energy-efficient, widespread adoption is also environmentally sustainable.
Spartan retains several key features of Nakamoto Consensus, including: the longest-chain fork-choice rule, dynamic availability (i.e., it is permissionless), and the honest majority assumption.
Similar to proof-of-stake protocols, there is no mining delay, so we instead employ a round based notion of time, which is almost identical to the Ouroborous family of protocols and BABE.

Spartan is not intended to be deployed in a production setting, as it is not actually incentive compatible for a decentralized network.
This is due to several subtle mechanism design challenges inherent to PoC consensus, which we refer to as the farmer's dilemma.
Instead, Spartan is intended to be an extensible stepping stone towards Subspace, a PoC consensus design which does resolve the farmer's dilemma.
For more details, please refer to our technical whitepaper: [Subspace: A solution to the farmer's dilemma]().

#### A note on terminology

We define PoC loosely as a catch-all term for proofs of space/storage/space-time/replication/retrievability.
These can broadly be categorized as either proofs-of-useless-space (i.e, wasting a disk with random data) or proofs-of-useful-storage (i.e. storing some real-world data).
Spartan and Subspace are both based on an underlying Proof-of-Replication, in which a farmer (PoC name for a miner) stores a replica of some actual data. Spartan is a proof-of-space style PoC protocol, in which farmers store replicas of some random data generated from a short seed.
In contrast, Subspace is a proof-of-storage style PoC protocol, in which farmers store replicas of the history of the blockchain itself.
Both protocols have much in common, and they are both implementations of an abstract notion of a PoC which employ an abstract notion of a PoR.
We have therefore attempted to construct the dependencies of `pallet_spartan` such that they may be shared with `pallet_subspace`.

### The Spartan Protocol

At a high level, all PoC protocols follow two distinct phases.
Initially a farmer will create a plot using some persistent storage (i.e. HDD or SSD).
This is typically a compute-intensive task that could take several days.
Once plotting is complete, the farmer may participate in consensus, by querying its plot against each new block challenge.
If a solution is found that is within solution range (difficulty threshold), the farmer may construct a proof and forge the next block.
The trick is to design the protocol such that it is either computationally infeasible or economically irrational to attempt to plot on-demand, in-response to the challenge, by substituting CPU for storage.

#### Public Parameters

An overview of the required cryptographic primitives and constants all nodes must agree on in order to arrive at consensus.

##### Digital Signature Scheme
Similar to all blockchains, public keys serve as the basis for distributing rewards to block producers (i.e. farmers).
The PoR is ultimately derived from a signature of the `tag` used as the basis for a valid `Solution`.
To prevent grinding on `randomness`, a canonical signature scheme such as BLS or a VRF should be employed.

##### Cryptographic Hash Function
Required to derive the `randomness` for an epoch and the local `challenge` for each farmer.

##### Hash Based Message Authentication Code (HMAC)
Required to derive a valid commitment or `tag` for each `encoding` and a dynamic `Salt`.

##### Pseudorandom Permutation (PRP)
Required to generate and verify each `encoding`, derived from the `public_key_hash`, `nonce`, and `GENESIS_PIECE` for some number of `ENCODE_ROUNDS`.
We employ a time-asymmetric permutation based on Sloth (Slow timed hash function), parameterized by a `PRIME_SIZE` and `PIECE_SIZE`.
This has the advantage of allowing decoding (and verification) to be completed much faster than encoding.
Concretely, the `public_key_hash` serves as a public encoding key, the `nonce` serves as an Initialization Vector, and the `ENCODE_ROUNDS` specifies the number of depth-first iterations, or layers of the CBC block cipher (parameterizing the encoding delay).

##### Genesis Piece
A string of random bits of length `PIECE_SIZE` which is deterministically derived from a short seed.
This serves as the basis for every encoding across the network.

##### Genesis Time
A UNIX Timestamp reflecting the time at which the first block is produced.

##### Initial Solution Range
The maximum XOR distance between a valid `tag` and the block `challenge`.
Derived from the `PLOT_SIZE` of the genesis farmer.

##### Initial Salt
A 32 byte hash derived from a short seed. Used as an input to generate tags for genesis farmers.

##### Slot Duration
The slot interval in milliseconds.

##### Epoch Duration
A security parameter which defines the length of an epoch in slots.
Each epoch shares the same `randomness` used as the basis for the block `challenge`, and is derived from some past Epoch.
The length is derived from the expected number of blocks in the epoch, such that simulation attacks become computationally expensive and afford negligible gain.
Initially set to 32 blocks.

##### Era Duration
A security parameter which defines the length of an era in slots.
Each era shares the same `solution_range`. At the conclusion of each era, a new `solution_range` is calculated, based on the average `solution_range` over the last era.
Roughly equivalent to the work-difficulty reset period in PoW blockchains.

##### Solution Range
A security parameter which defines the expected number of slots required for the network to obtain a valid PoR and generate a new block, for a given `SolutonRange`.
Higher probabilities increase the likelihood of honest forking and reduce the cost of private attacks.

##### Encoding Rounds
A security parameter which defines the number of depth-first iterations for the PRP, proportional to the sequential time required to encode any single piece, and the parallel time required for plotting.
A higher round count increases security but at the cost of farmer experience and energy-efficiency.

##### Salt Update Interval
A security parameter which defines the number of slots for which a given salt is valid.
This is required to discourage compression attacks.
A more frequent update interval linearly increases the computation required to preform the compression attack but also degrades the efficiency of the protocol, as the entire plot must be read and re-committed to at each update.

#### Initial Plotting Phase

![Imgur](https://i.imgur.com/t9HRGdy.png)

1. Given the above Public Parameters
2. Generate a keypair `public_key, private_key` under the digital signature scheme.
3. Derive a `public_key_hash` as `Hash(public_key)`
4. Given a disk of size `PLOT_SIZE` bytes.
5. For a given `ENCODING_COUNT` as `PLOT_SIZE / PIECE_SIZE`
6. For each `nonce` in the range `0..ENCODING_COUNT`
7. Create each `encoding` as `Encode(GENESIS_PIECE, public_key_hash, nonce, ENCODE_ROUNDS)`
8. Create a `tag` for each `encoding` as `Hmac(encoding, salt)`
9. Write each `encoding` to persistent storage at offset `nonce`.
10. Insert each `tag, nonce` pair into a Binary Search Tree (BST).

#### Continuous Challenge-Response Phase

![Imgur](https://i.imgur.com/AFdt7Sb.png)

##### Challenge Generation

1. For each block in the epoch compute the incremental `randomness` as `Hash(Sign(private_key, tag))`.
2. Compute the `epoch_randomness` as the hash of the concatenation of all incremental `randomness`.
3. For each `slot` (number), compute the global `challenge` as `Hash(randomness||slot)`.
2. Each farmer then computes their `local_challenge` as `Hash(challenge||public_key_hash)`.

##### Challenge Evaluation & Response

1. For each local `challenge`
2. Query the BST for the nearest `tag`.
3. If `tag as u64` is within +/- `solution_range` of `challenge as u64`.
4. Retrieve the offset (`nonce`) for the `tag` from the BST.
5. Retrieve the `encoding` at offset `nonce` from persistent storage.
6. Generate a `signature` as `Sign(private_key, tag)`
7. Forge a new block
8. Attach a `solution` consisting of

```Rust
Solution {
    challenge: [u8; 32];
    encoding: [u8; 4096];
    public_key: [u8; 32];
    nonce: u64;
    tag: [u8; 8];
    signature: [u8; 32];
}
```
##### Verification

1. Compute the `public_key_hash` and `local_challenge` using the `challenge` and `public_key`.
2. Verify `tag` is within +/- `solution_range` of `local_challenge`.
3. Verify the `tag` is valid for `encoding` and `public_key_hash`.
4. Verify the `encoding` decodes back to `GenesisPiece` using `public_key_hash` and `nonce`.

### Architectural Design

#### High Level Overview

##### `node-template-spartan`

Based on a fork of `parity-tech/substrate`.
Includes a new template in `../bin` based on `node-template` (with `BABE`).
`Grandpa` finality gadget has been removed.
`BABE` consensus is replaced with Spartan.
All notions of authorities and sessions have been removed.
This is simply a bare-bones account-based blockchain node that supports balance transfers.
The node cannot farm by itself, it can only validate received blocks and generate blocks from `Solutions` submitted by locally connected `Farmers`.

##### `spartan-farmer`

Based on a previous work from `subspace/substrate-core-rust`, but implemented as a standalone `Farmer` which connects to `node-template-spartan` over an RPC, conceptually similar to the distinction between `GETH` and `EthMiner`.
Able to create a `Plot` using local disk space and continuously `Farm` when connected to a full node.

##### `spartan-codec`

A Rust implementation and adaptation of [SLOTH](https://eprint.iacr.org/2015/366) (slow-timed hash function) into a time-asymmetric permutation using a standard CBC block cipher.
This code is largely based on the C implementation used in [PySloth](https://github.com/randomchain/pysloth/blob/master/sloth.c) which is the same as used in the paper.
This serves as the permutation for the Proof-of-Replication (PoR) that underlies `Spartan`.
When a farmer plots, it encodes the genesis piece using encode half.
When the client validates, it decodes the encoding using decode half, and verifies that it matches the genesis piece.
Decode time is roughly 100x faster than encode time.

#### Substrate Modules

![Imgur](https://i.imgur.com/22YBNZP.png)

##### `sp_consensus_poc`

Defines primitives for some abstract PoC consensus using some abstract PoR. This assumes the PoC consensus is round-based and permissionless.

##### `sc_consensus_poc`

Defines client functionality for some abstract PoC consensus using some PoR. This assumes the PoC consensus employed is both round-based and permissionless.

##### `sp_consensus_spartan`

Defines the shared primitives for a PoR based on the Spartan protocol (i.e. a sloth based permutation).

##### `pallet_spartan`

Defines the runtime logic for Spartan, a permissionless, round-based consensus algorithm, implemented for abstract PoC consensus using a Sloth-based Por.





