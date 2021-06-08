Substrate transaction pool implementation.

License: GPL-3.0-or-later WITH Classpath-exception-2.0

# Problem Statement

The transaction pool is responsible for maintaining a set of transactions that
possible to include by block authors in upcoming blocks. Transactions are received
either from networking (gossiped by other peers) or RPC (submitted locally).

The main task of the pool is to prepare an ordered list of transactions for block
authorship module. The same list is useful for gossiping to other peers, but note
that it's not a hard requirement for the gossiped transactions to be exactly the
same (see implementation notes below).

It's within block author incentives to have the transactions stored and ordered in
such a way to:

1. Maximize block author's profits (value of the produced block)
2. Minimize block author's amount of work (time to produce block)

In FRAME case the first property is simply making sure that the fee per weight
unit is the highest (high `tip` values), the second is about avoiding feeding
transactions that cannot be part of the next block (they are invalid, obsolete, etc).

From the transaction pool PoV, transactions are simply opaque blob of bytes,
it's required to query the runtime (via `TaggedTransactionQueue` Runtime API) to
verify transaction's mere correctnes and extract any information about how the
transaction relates to other transactions in the pool and current on-chain state.
Only valid transactions should be stored in the pool.

Each imported block can affect validity of transactions already in the pool. Block
authors expect from the pool to get most up to date information about transactions
that can be included in the block that they are going to build on top of the just
imported one.  The process of ensuring this property is called *pruning*. During
pruning the pool should remove transactions which are considered invalid by the
runtime (queried at current best imported block).

Since the blockchain is not always linear, forks need to be correctly handled by
the transaction pool as well. In case of a fork, some blocks are *retracted*
from the canonical chain, and some other blocks get *enacted* on top of some
common ancestor. The transactions from retrated blocks could simply be discarded,
but it's desirable to make sure they are still considered for inclusion in case they
are deemed valid by the runtime state at best, recently enacted block (fork the
chain re-organized to).

Transaction pool should also offer a way of tracking transaction lifecycle in the
pool, it's broadcasting status, block inclusion, finality, etc.

## Transaction Validity details

Information retrieved from the the runtime are encapsulated in `TransactionValidity`
type.

```rust
pub type TransactionValidity = Result<ValidTransaction, TransactionValidityError>;

pub struct ValidTransaction {
  pub requires: Vec<TransactionTag>,
  pub provides: Vec<TransactionTag>,
  pub priority: TransactionPriority,
  pub longevity: TransactionLongevity,
  pub propagate: bool,
}

pub enum TransactionValidityError {
  Invalid(/* details */),
  Unknown(/* details */),
}
```

We will go through each of the parameter now to understand the requirements they
create for transaction ordering.

The runtime is expected to return these values in a deterministic fashion. Calling
the API multiple times given exactly the same state must return same results.
Field-specific rules are described below.

### `requires` / `provides`

These two fields contain a set of `TransactionTag`s (opaque blobs) associated with
given transaction. Looking at these fields we can find dependencies between
transactions and their readiness for block inclusion.

The `provides` set contains properties that will be *satisfied* in case the transaction
is succesfuly added to a block. `requires` contains properties that must be satisfied
**before** the transaction can be included to a block.

Note that a transaction with empty `requires` set can be added to a block immediately,
there are no other transactions that it expects to be included before.

For some given series of transactions the `provides` and `requires` fields will create
a (simple) directed acyclic graph. The *sources* in such graph, if they don't have
any extra `requires` tags (i.e. they have their all dependencies *satisfied*), should
be considered for block inclusion first. Multiple transactions that are ready for
block inclusion should be ordered by `priority` (see below).

Note the process of including transactions to a block is basically building the graph,
then selecting "the best" source vertex (transaction) with all tags satisfied and
removing it from that graph.

#### Examples

- A transaction in Bitcoin-like chain will `provide` generated UTXOs and will `require`
  UTXOs it is still awaiting for (note that it's not necessarily all require inputs,
  since some of them might already be spendable (i.e. the UTXO is in state))

- A transaction in account-based chain will `provide` a `(sender, transaction_index/nonce)`
  (as one tag), and will `require` `(sender, nonce - 1)` in case
  `on_chain_nonce < nonce - 1`.

#### Rules & caveats

- `provides` must not be empty
- transactions with overlap in `provides` tags are mutually exclusive
- checking validity of transaction that `requires` tag `A` after including
  transaction that provides that tag must not return `A` in `requires` again
- runtime developers should avoid re-using `provides` tag (i.e. it should be unique)
- there should be no cycles in transaction dependencies
- caveat: on-chain state conditions may render transaction invalid despite no
  `requires` tags
- caveat: on-chain state conditions may render transaction valid despite some
  `requires` tags
- caveat: including transactions to a chain might make them valid again right away
  (for instance UTXO transaction get's in, but since we don't store spent outputs
  it will be valid again, awaiting the same inputs/tags to be satisfied)

### `priority`

Transaction priority describes importance of the transaction relative to other transactions
in the pool. Block authors can expect benefiting from including such transactions
before others.

Note that we can't simply order transactions in the pool by `priority`, cause first
we need to make sure that all of the transaction requirements are satisfied (see
`requires/provides` section). However if we consider a set of transactions
which all have their requirements (tags) satisfied, the block author should be
choosing the ones with highest priority to include to the next block first.

`priority` can be any number between `0` (lowest inclusion priority) to `u64::MAX`
(highest inclusion priority).

#### Rules & caveats

- `priority` of transaction may change over time
- on-chain conditions may affect `priority`
- Given two transactions with overlapping `provides` tags, the one with higher
  `priority` should be preferred. However we can also look at the total priority
  of a subtree rooted at that transaction and compare that instead (i.e. even though
  the transaction itself has lower `priority` it "unlocks" other high priority transactions).

### `longevity`

Longevity describes how long (in blocks) the transaction is expected to be
valid. This parameter only gives a hint to the transaction pool how long
current transaction may still be valid. Note that it does not guarantee
the transaction is valid all that time though.

#### Rules & caveats

- `longevity` of transaction may change over time
- on-chain conditions may affect `longevity`
- After `longevity` lapses the transaction may still be valid

### `propagate`

This parameter instructs the pool propagate/gossip a transaction to node peers.
By default this should be `true`, however in some cases it might be undesirable
to propagate transactions further (heavy transactions, privacy leaking, etc).

### 'TransactionSource`

To make it possible for the runtime to distinguish if the transaction that is
being validated was received over the network or submitted using local RPC or
maybe it's simply part of a block that is being imported, the transaction pool
should pass additional `TransactionSource` parameter to the validity function
runtime call.

This can be used by runtime developers to quickly reject transactions that for
instance are not expected to be gossiped in the network.

# Implementation caveats

TODO:

# Current implementation

TODO:
- ready / future
- revalidation

# Future work

TODO:

## Gossiping

It was discussed in the past to use set reconciliation strategies instead of
simply broadcasting all/some transactions to all/selected peers. An Ethereum's
[EIP-2464](https://github.com/ethereum/EIPs/blob/5b9685bb9c7ba0f5f921e4d3f23504f7ef08d5b1/EIPS/eip-2464.md)
might be a good first approach to reduce transaction gossip.


