Integration of the GRANDPA finality gadget into substrate.

This crate is unstable and the API and usage may change.

This crate provides a long-running future that produces finality notifications.

# Usage

First, create a block-import wrapper with the `block_import` function. The
GRANDPA worker needs to be linked together with this block import object, so
a `LinkHalf` is returned as well. All blocks imported (from network or
consensus or otherwise) must pass through this wrapper, otherwise consensus
is likely to break in unexpected ways.

Next, use the `LinkHalf` and a local configuration to `run_grandpa_voter`.
This requires a `Network` implementation. The returned future should be
driven to completion and will finalize blocks in the background.

# Changing authority sets

The rough idea behind changing authority sets in GRANDPA is that at some point,
we obtain agreement for some maximum block height that the current set can
finalize, and once a block with that height is finalized the next set will
pick up finalization from there.

Technically speaking, this would be implemented as a voting rule which says,
"if there is a signal for a change in N blocks in block B, only vote on
chains with length NUM(B) + N if they contain B". This conditional-inclusion
logic is complex to compute because it requires looking arbitrarily far
back in the chain.

Instead, we keep track of a list of all signals we've seen so far (across
all forks), sorted ascending by the block number they would be applied at.
We never vote on chains with number higher than the earliest handoff block
number (this is num(signal) + N). When finalizing a block, we either apply
or prune any signaled changes based on whether the signaling block is
included in the newly-finalized chain.

License: GPL-3.0-or-later WITH Classpath-exception-2.0