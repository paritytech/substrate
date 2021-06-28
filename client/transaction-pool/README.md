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

In the case of FRAME the first property is simply making sure that the fee per weight
unit is the highest (high `tip` values), the second is about avoiding feeding
transactions that cannot be part of the next block (they are invalid, obsolete, etc).

From the transaction pool PoV, transactions are simply opaque blob of bytes,
it's required to query the runtime (via `TaggedTransactionQueue` Runtime API) to
verify transaction's mere correctness and extract any information about how the
transaction relates to other transactions in the pool and current on-chain state.
Only valid transactions should be stored in the pool.

Each imported block can affect validity of transactions already in the pool. Block
authors expect from the pool to get most up to date information about transactions
that can be included in the block that they are going to build on top of the just
imported one. The process of ensuring this property is called *pruning*. During
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
is successfully added to a block. `requires` contains properties that must be satisfied
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
- transactions with an overlap in `provides` tags are mutually exclusive
- checking validity of transaction that `requires` tag `A` after including
  transaction that provides that tag must not return `A` in `requires` again
- runtime developers should avoid re-using `provides` tag (i.e. it should be unique)
- there should be no cycles in transaction dependencies
- caveat: on-chain state conditions may render transaction invalid despite no
  `requires` tags
- caveat: on-chain state conditions may render transaction valid despite some
  `requires` tags
- caveat: including transactions to a chain might make them valid again right away
  (for instance UTXO transaction gets in, but since we don't store spent outputs
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
to propagate transactions further. Examples might include heavy transactions
produced by block authors in offchain workers (DoS) or risking being front
runned by someone else after finding some non trivial solution or equivocation,
etc.

### 'TransactionSource`

To make it possible for the runtime to distinguish if the transaction that is
being validated was received over the network or submitted using local RPC or
maybe it's simply part of a block that is being imported, the transaction pool
should pass additional `TransactionSource` parameter to the validity function
runtime call.

This can be used by runtime developers to quickly reject transactions that for
instance are not expected to be gossiped in the network.


### `Invalid` transaction

In case the runtime returns an `Invalid` error it means the transaction cannot
be added to a block at all. Extracting the actual reason of invalidity gives
more details about the source. For instance `Stale` transaction just indicates
the transaction was already included in a block, while `BadProof` signifies
invalid signature.
Invalidity might also be temporary. In case of `ExhaustsResources` the
transaction does not fit to the current block, but it might be okay for the next
one.

### `Unknown` transaction

In case of `Unknown` validity, the runtime cannot determine if the transaction
is valid or not in current block. However this situation might be temporary, so
it is expected for the transaction to be retried in the future.

# Implementation

An ideal transaction pool should be storing only transactions that are considered
valid by the runtime at current best imported block.
After every block is imported, the pool should:

1. Revalidate all transactions in the pool and remove the invalid ones.
1. Construct the transaction inclusion graph based on `provides/requires` tags.
   Some transactions might not be reachable (have unsatisfied dependencies),
   they should be just left out in the pool.
1. On block author request, the graph should be copied and transactions should
   be removed one-by-one from the graph starting from the one with highest
   priority and all conditions satisfied.

With current gossip protocol, networking should propagate transactions in the
same order as block author would include them. Most likely it's fine if we
propagate transactions with cumulative weight not exceeding upcoming `N`
blocks (choosing `N` is subject to networking conditions and block times).

Note that it's not a strict requirement though to propagate exactly the same
transactions that are prepared for block inclusion. Propagation is best
effort, especially for block authors and is not directly incentivised.
However the networking protocol might penalise peers that send invalid or
useless transactions so we should be nice to others. Also see below a proposal
to instead of gossiping everyting have other peers request transactions they
are interested in.

Since the pool is expected to store more transactions than what can fit
to a single block. Validating the entire pool on every block might not be
feasible, so the actual implementation might need to take some shortcuts.

## Suggestions & caveats

1. The validity of transaction should not change significantly from block to
   block. I.e. changes in validity should happen predicatably, e.g. `longevity`
   decrements by 1, `priority` stays the same, `requires` changes if transaction
   that provided a tag was included in block. `provides` does not change, etc.

1. That means we don't have to revalidate every transaction after every block
   import, but we need to take care of removing potentially stale transactions.

1. Transactions with exactly the same bytes are most likely going to give the
   same validity results. We can essentially treat them as identical.

1. Watch out for re-organisations and re-importing transactions from retracted
   blocks.

1. In the past there were many issues found when running small networks with a
   lot of re-orgs. Make sure that transactions are never lost.

1. UTXO model is quite challenging. The transaction becomes valid right after
   it's included in block, however it is waiting for exactly the same inputs to
   be spent, so it will never really be included again.

1. Note that in a non-ideal implementation the state of the pool will most
   likely always be a bit off, i.e. some transactions might be still in the pool,
   but they are invalid. The hard decision is about trade-offs you take.

1. Note that import notification is not reliable - you might not receive a
   notification about every imported block.

## Potential implementation ideas

1. Block authors remove transactions from the pool when they author a block. We
   still store them around to re-import in case the block does not end up
   canonical. This only works if the block is actively authoring blocks (also
   see below).

1. We don't prune, but rather remove a fixed amount of transactions from the front
   of the pool (number based on average/max transactions per block from the
   past) and re-validate them, reimporting the ones that are still valid.

1. We periodically validate all transactions in the pool in batches.

1. To minimize runtime calls, we introduce batch-verify call. Note it should reset
   the state (overlay) after every verification.

1. Consider leveraging finality. Maybe we could verify against latest finalised
   block instead. With this the pool in different nodes can be more similar
   which might help with gossiping (see set reconciliation). Note that finality
   is not a strict requirement for a Substrate chain to have though.

1. Perhaps we could avoid maintaining ready/future queues as currently, but
   rather if transaction doesn't have all requirements satisfied by existing
   transactions we attempt to re-import it in the future.

1. Instead of maintaining a full pool with total ordering we attempt to maintain
   a set of next (couple of) blocks. We could introduce batch-validate runtime
   api  method that pretty much attempts to simulate actual block inclusion of
   a set of such transactions (without necessarily fully running/dispatching
   them). Importing a transaction would consist of figuring out which next block
   this transaction have a chance to be included in and then attempting to
   either push it back or replace some of existing transactions.

1. Perhaps we could use some immutable graph structure to easily add/remove
   transactions. We need some traversal method that takes priority and
   reachability into account.

1. It was discussed in the past to use set reconciliation strategies instead of
simply broadcasting all/some transactions to all/selected peers. An Ethereum's
[EIP-2464](https://github.com/ethereum/EIPs/blob/5b9685bb9c7ba0f5f921e4d3f23504f7ef08d5b1/EIPS/eip-2464.md)
might be a good first approach to reduce transaction gossip.

# Current implementation

Current implementation of the pool is a result of experiences from Ethereum's
pool implementation, but also has some warts coming from the learning process of
Substrate's generic nature and light client support.

The pool consists of basically two independent parts:

1. The transaction pool itself.
2. Maintenance background task.

The pool is split into `ready` pool and `future` pool. The latter contains
transactions that don't have their requirements satisfied, and the former holds
transactions that can be used to build a graph of dependencies. Note that the
graph is build ad-hoc during the traversal process (getting the `ready`
iterator). This makes the importing process cheaper (we don't need to find the
exact position in the queue or graph), but traversal process slower
(logarithmic). However most of the time we will only need the beginning of the
total ordering of transactions for block inclusion or network propagation, hence
the decision.

The maintenance task is responsible for:

1. Periodically revalidating pool's transactions (revalidation queue).
1. Handling block import notifications and doing pruning + re-importing of
   transactions from retracted blocks.
1. Handling finality notifications and relaying that to transaction-specific
   listeners.

Additionally we maintain a list of recently included/rejected transactions
(`PoolRotator`) to quickly reject transactions that are unlikely to be valid
to limit number of runtime verification calls.

Each time a transaction is imported, we first verify it's validity and later
find if the tags it `requires` can be satisfied by transactions already in
`ready` pool. In case the transaction is imported to the `ready` pool we
additionally *promote* transactions from `future` pool if the transaction
happened to fulfill their requirements.
Note we need to cater for cases where transaction might replace a already
existing transaction in the pool. In such case we check the entire sub-tree of
transactions that we are about to replace, compare their cumulative priority to
determine which subtree to keep.

After a block is imported we kick-off pruning procedure. We first attempt to
figure out what tags were satisfied by transaction in that block. For each block
transaction we either call into runtime to get it's `ValidTransaction` object,
or we check the pool if that transaction is already known to spare the runtime
call. From this we gather full set of `provides` tags and perform pruning of
`ready` pool based on that. Also we promote all transactions from `future` that
have their tags satisfied.

In case we remove transactions that we are unsure if they were already included
in current block or some block in the past, it is being added to revalidation
queue and attempted to be re-imported by the background task in the future.

Runtime calls to verify transactions are performed from a separate (limited)
thread pool to avoid interferring too much with other subsystems of the node. We
definitely don't want to have all cores validating network transactions, cause
all of these transactions need to be considered untrusted (potentially DoS).
