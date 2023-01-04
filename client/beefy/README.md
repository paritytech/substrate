# BEEFY
**BEEFY** (**B**ridge **E**fficiency **E**nabling **F**inality **Y**ielder) is a secondary
protocol running along GRANDPA Finality to support efficient bridging with non-Substrate
blockchains, currently mainly ETH mainnet.

It can be thought of as an (optional) Bridge-specific Gadget to the GRANDPA Finality protocol.
The Protocol piggybacks on many assumptions provided by GRANDPA, and is required to be built
on top of it to work correctly.

BEEFY is a consensus protocol designed with efficient trustless bridging in mind. It means
that building a light client of BEEFY protocol should be optimized for restricted environments
like Ethereum Smart Contracts or On-Chain State Transition Function (e.g. Substrate Runtime).
Note that BEEFY is not a standalone protocol, it is meant to be running alongside GRANDPA, a
finality gadget created for Substrate/Polkadot ecosystem. More details about GRANDPA can be found
in the [whitepaper](https://github.com/w3f/consensus/blob/master/pdf/grandpa.pdf).

# Context

## Bridges

We want to be able to "bridge" different blockchains. We do so by safely sharing and verifying
information about each chain’s state, i.e. blockchain `A` should be able to verify that blockchain
`B` is at block #X.

## Finality

Finality in blockchains is a concept that means that after a given block #X has been finalized,
it will never be reverted (e.g. due to a re-org). As such, we can be assured that any transaction
that exists in this block will never be reverted.

## GRANDPA

GRANDPA is our finality gadget. It allows a set of nodes to come to BFT agreement on what is the
canonical chain. It requires that 2/3 of the validator set agrees on a prefix of the canonical
chain, which then becomes finalized.

![img](https://miro.medium.com/max/955/1*NTg26i4xbO3JncF_Usu9MA.png)

### Difficulties of GRANDPA finality proofs

```rust
struct Justification<Block: BlockT> {
    round: u64,
    commit: Commit<Block>,
    votes_ancestries: Vec<Block::Header>,
}

struct Commit<Hash, Number, Signature, Id> {
    target_hash: Hash,
    target_number: Number,
    precommits: Vec<SignedPrecommit<Hash, Number, Signature, Id>>,
}

struct SignedPrecommit<Hash, Number, Signature, Id> {
    precommit: Precommit<Hash, Number>,
    signature: Signature,
    id: Id,
}

struct Precommit<Hash, Number> {
    target_hash: Hash,
    target_number: Number,
}
```

The main difficulty of verifying GRANDPA finality proofs comes from the fact that voters are
voting on different things. In GRANDPA each voter will vote for the block they think is the
latest one, and the protocol will come to agreement on what is the common ancestor which has >
2/3 support.

This creates two sets of inefficiencies:

- We may need to have each validator's vote data because they're all potentially different (i.e.
  just the signature isn't enough).
- We may need to attach a couple of headers to the finality proof in order to be able to verify
  all of the votes' ancestries.

Additionally, since our interim goal is to bridge to Ethereum there is also a difficulty related
to "incompatible" crypto schemes. We use \`ed25519\` signatures in GRANDPA which we can't
efficiently verify in the EVM.

Hence,

### Goals of BEEFY

1. Allow customisation of crypto to adapt for different targets. Support thresholds signatures as
   well eventually.
1. Minimize the size of the "signed payload" and the finality proof.
1. Unify data types and use backward-compatible versioning so that the protocol can be extended
   (additional payload, different crypto) without breaking existing light clients.

And since BEEFY is required to be running on top of GRANDPA. This allows us to take couple of
shortcuts:
1. BEEFY validator set is **the same** as GRANDPA's (i.e. the same bonded actors), they might be
   identified by different session keys though.
1. BEEFY runs on **finalized** canonical chain, i.e. no forks (note Misbehavior
   section though).
1. From a single validator perspective, BEEFY has at most one active voting round. Since GRANDPA
   validators are reaching finality, we assume they are on-line and well-connected and have
   similar view of the state of the blockchain.

# The BEEFY Protocol

## Mental Model

BEEFY should be considered as an extra voting round done by GRANDPA validators for the current
best finalized block. Similarily to how GRANDPA is lagging behind best produced (non-finalized)
block, BEEFY is going to lag behind best GRANDPA (finalized) block.

```
                       ┌──────┐ ┌──────┐ ┌──────┐ ┌──────┐ ┌──────┐
                       │      │ │      │ │      │ │      │ │      │
                       │  B1  │ │  B2  │ │  B3  │ │  B4  │ │  B5  │
                       │      │ │      │ │      │ │      │ │      │
                       └──────┘ └───▲──┘ └──────┘ └───▲──┘ └───▲──┘
                                    │                 │        │
     Best BEEFY block───────────────┘                 │        │
                                                      │        │
     Best GRANDPA block───────────────────────────────┘        │
                                                               │
     Best produced block───────────────────────────────────────┘

```

A pseudo-algorithm of behaviour for a fully-synced BEEFY validator is:

```
loop {
  let (best_beefy, best_grandpa) = wait_for_best_blocks();

  let block_to_vote_on = choose_next_beefy_block(
    best_beefy,
    best_grandpa
  );

  let payload_to_vote_on = retrieve_payload(block_to_vote_on);

  let commitment = (block_to_vote_on, payload_to_vote_on);

  let signature = sign_with_current_session_key(commitment);

  broadcast_vote(commitment, signature);
}
```

## Details

Before we jump into describing how BEEFY works in details, let's agree on the terms we are going
to use and actors in the system. All nodes in the network need to participate in the BEEFY
networking protocol, but we can identify two distinct actors though: **regular nodes** and
**BEEFY validators**.
Validators are expected to actively participate in the protocol, by producing and broadcasting
**votes**. Votes are simply their signatures over a **Commitment**. A Commitment consists of a
**payload** (an opaque blob of bytes extracted from a block or state at that block, expected to
be some form of crypto accumulator (like Merkle Tree Hash or Merkle Mountain Range Root Hash))
and **block number** from which this payload originates. Additionally, Commitment contains BEEFY
**validator set id** at that particular block. Note the block is finalized, so there is no
ambiguity despite using block number instead of a hash. A collection of **votes**, or rather
a Commitment and a collection of signatures is going to be called **Signed Commitment**. A valid
(see later for the rules) Signed Commitment is also called a **BEEFY Justification** or
**BEEFY Finality Proof**. For more details on the actual data structures please see
[BEEFY primitives definitions](https://github.com/paritytech/substrate/tree/master/primitives/beefy/src).

A **round** is an attempt by BEEFY validators to produce a BEEFY Justification. **Round number**
is simply defined as a block number the validators are voting for, or to be more precise, the
Commitment for that block number. Round ends when the next round is started, which may happen
when one of the events occur:
1. Either the node collects `2/3rd + 1` valid votes for that round.
2. Or the node receives a BEEFY Justification for a block greater than the current best BEEFY block.

In both cases the node proceeds to determining the new round number using "Round Selection"
procedure.

Regular nodes are expected to:
1. Receive & validate votes for the current round and broadcast them to their peers.
1. Receive & validate BEEFY Justifications and broadcast them to their peers.
1. Return BEEFY Justifications for **Mandatory Blocks** on demand.
1. Optionally return BEEFY Justifications for non-mandatory blocks on demand.

Validators are expected to additionally:
1. Produce & broadcast vote for the current round.

Both kinds of actors are expected to fully participate in the protocol ONLY IF they believe they
are up-to-date with the rest of the network, i.e. they are fully synced. Before this happens,
the node should continue processing imported BEEFY Justifications and votes without actively
voting themselves.

### Round Selection

Every node (both regular nodes and validators) need to determine locally what they believe
current round number is. The choice is based on their knowledge of:

1. Best GRANDPA finalized block number (`best_grandpa`).
1. Best BEEFY finalized block number (`best_beefy`).
1. Starting block of current session (`session_start`).

**Session** means a period of time (or rather number of blocks) where validator set (keys) do not change.
See `pallet_session` for implementation details in `FRAME` context. Since we piggy-back on
GRANDPA, session boundaries for BEEFY are exactly the same as the ones for GRANDPA.

We define two kinds of blocks from the perspective of BEEFY protocol:
1. **Mandatory Blocks**
2. **Non-mandatory Blocks**

Mandatory blocks are the ones that MUST have BEEFY justification. That means that the validators
will always start and conclude a round at mandatory blocks. For non-mandatory blocks, there may
or may not be a justification and validators may never choose these blocks to start a round.

Every **first block in** each **session** is considered a **mandatory block**. All other blocks
in the session are non-mandatory, however validators are encouraged to finalize as many blocks as
possible to enable lower latency for light clients and hence end users. Since GRANDPA is
considering session boundary blocks as mandatory as well, `session_start` block will always have
both GRANDPA and BEEFY Justification.

Therefore, to determine current round number nodes use a formula:

```
round_number =
      (1 - M) * session_start
   +        M * (best_beefy + NEXT_POWER_OF_TWO((best_grandpa - best_beefy + 1) / 2))
```

where:

- `M` is `1` if mandatory block in current session is already finalized and `0` otherwise.
- `NEXT_POWER_OF_TWO(x)` returns the smallest number greater or equal to `x` that is a power of two.

In other words, the next round number should be the oldest mandatory block without a justification,
or the highest GRANDPA-finalized block, whose block number difference with `best_beefy` block is
a power of two. The mental model for round selection is to first finalize the mandatory block and
then to attempt to pick a block taking into account how fast BEEFY catches up with GRANDPA.
In case GRANDPA makes progress, but BEEFY seems to be lagging behind, validators are changing
rounds less often to increase the chance of concluding them.

As mentioned earlier, every time the node picks a new `round_number` (and validator casts a vote)
it ends the previous one, no matter if finality was reached (i.e. the round concluded) or not.
Votes for an inactive round should not be propagated.

Note that since BEEFY only votes for GRANDPA-finalized blocks, `session_start` here actually means:
"the latest session for which the start of is GRANDPA-finalized", i.e. block production might
have already progressed, but BEEFY needs to first finalize the mandatory block of the older
session.

In good networking conditions BEEFY may end up finalizing each and every block (if GRANDPA does
the same). Practically, with short block times, it's going to be rare and might be excessive, so
it's suggested for implementations to introduce a `min_delta` parameter which will limit the
frequency with which new rounds are started. The affected component of the formula would be:
`best_beefy + MAX(min_delta, NEXT_POWER_OF_TWO(...))`, so we start a new round only if the
power-of-two component is greater than the min delta. Note that if `round_number > best_grandpa`
the validators are not expected to start any round.

### Catch up

Every session is guaranteed to have at least one BEEFY-finalized block. However it also means
that the round at mandatory block must be concluded even though, a new session has already started
(i.e. the on-chain component has selected a new validator set and GRANDPA might have already
finalized the transition). In such case BEEFY must "catch up" the previous sessions and make sure to
conclude rounds for mandatory blocks. Note that older sessions must obviously be finalized by the
validator set at that point in time, not the latest/current one.

### Initial Sync

It's all rainbows and unicorns when the node is fully synced with the network. However during cold
startup it will have hard time determining the current round number. Because of that nodes that
are not fully synced should not participate in BEEFY protocol at all.

During the sync we should make sure to also fetch BEEFY justifications for all mandatory blocks.
This can happen asynchronously, but validators, before starting to vote, need to be certain
about the last session that contains a concluded round on mandatory block in order to initiate the
catch up procedure.

### Gossip

Nodes participating in BEEFY protocol are expected to gossip messages around.
The protocol defines following messages:

1. Votes for the current round,
2. BEEFY Justifications for recently concluded rounds,
3. BEEFY Justification for the latest mandatory block,

Each message is additionally associated with a **topic**, which can be either:
1. the round number (i.e. topic associated with a particular round),
2. or the global topic (independent from the rounds).

Round-specific topic should only be used to gossip the votes, other messages are gossiped
periodically on the global topic. Let's now dive into description of the messages.

- **Votes**
  - Votes are sent on the round-specific topic.
  - Vote is considered valid when:
    - The commitment matches local commitment.
    - The validator is part of the current validator set.
    - The signature is correct.

- **BEEFY Justification**
  - Justifications are sent on the global topic.
  - Justification is considered worthwhile to gossip when:
    - It is for a recent (implementation specific) round or the latest mandatory round.
    - All signatures are valid and there is at least `2/3rd + 1` of them.
    - Signatorees are part of the current validator set.
  - Mandatory justifications should be announced periodically.

## Misbehavior

Similarily to other PoS protocols, BEEFY considers casting two different votes in the same round a
misbehavior. I.e. for a particular `round_number`, the validator produces signatures for 2 different
`Commitment`s and broadcasts them. This is called **equivocation**.

On top of this, voting on an incorrect **payload** is considered a misbehavior as well, and since
we piggy-back on GRANDPA there is no ambiguity in terms of the fork validators should be voting for.

Misbehavior should be penalized. If more validators misbehave in the exact same `round` the
penalty should be more severe, up to the entire bonded stake in case we reach `1/3rd + 1`
validators misbehaving.

## Ethereum

Initial version of BEEFY was made to enable efficient bridging with Ethereum, where the light
client is a Solidity Smart Contract compiled to EVM bytecode. Hence the choice of the initial
cryptography for BEEFY: `secp256k1` and usage of `keccak256` hashing function.

### Future: Supporting multiple crypto

While BEEFY currently works with `secp256k1` signatures, we intend in the future to support
multiple signature schemes.
This means that multiple kinds of `SignedCommitment`s might exist and only together they form a
full `BEEFY Justification`.

## BEEFY Key

The current cryptographic scheme used by BEEFY is `ecdsa`. This is **different** from other
schemes like `sr25519` and `ed25519` which are commonly used in Substrate configurations for
other pallets (BABE, GRANDPA, AuRa, etc). The most noticeable difference is that an `ecdsa`
public key is `33` bytes long, instead of `32` bytes for a `sr25519` based public key. So, a
BEEFY key [sticks out](https://github.com/paritytech/polkadot/blob/25951e45b1907853f120c752aaa01631a0b3e783/node/service/src/chain_spec.rs#L738)
among the other public keys a bit.

For other crypto (using the default Substrate configuration) the `AccountId` (32-bytes) matches
the `PublicKey`, but note that it's not the case for BEEFY. As a consequence of this, you can
**not** convert the `AccountId` raw bytes into a BEEFY `PublicKey`.

The easiest way to generate or view hex-encoded or SS58-encoded BEEFY Public Key is by using the
[Subkey](https://substrate.dev/docs/en/knowledgebase/integrate/subkey) tool. Generate a BEEFY key
using the following command

```sh
subkey generate --scheme ecdsa
```

The output will look something like

```sh
Secret phrase `sunset anxiety liberty mention dwarf actress advice stove peasant olive kite rebuild` is account:
  Secret seed:       0x9f844e21444683c8fcf558c4c11231a14ed9dea6f09a8cc505604368ef204a61
  Public key (hex):  0x02d69740c3bbfbdbb365886c8270c4aafd17cbffb2e04ecef581e6dced5aded2cd
  Public key (SS58): KW7n1vMENCBLQpbT5FWtmYWHNvEyGjSrNL4JE32mDds3xnXTf
  Account ID:        0x295509ae9a9b04ade5f1756b5f58f4161cf57037b4543eac37b3b555644f6aed
  SS58 Address:      5Czu5hudL79ETnQt6GAkVJHGhDQ6Qv3VWq54zN1CPKzKzYGu

```

In case your BEEFY keys are using the wrong cryptographic scheme, you will see an invalid public
key format message at node startup. Basically something like

```sh
...
2021-05-28 12:37:51  [Relaychain] Invalid BEEFY PublicKey format!
...
```

# BEEFY Light Client

TODO
