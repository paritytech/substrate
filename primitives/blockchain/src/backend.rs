// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Substrate blockchain trait

use log::warn;
use parking_lot::RwLock;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT, NumberFor, Saturating},
	Justifications,
};
use std::collections::btree_set::BTreeSet;

use crate::header_metadata::HeaderMetadata;

use crate::error::{Error, Result};

/// Blockchain database header backend. Does not perform any validation.
pub trait HeaderBackend<Block: BlockT>: Send + Sync {
	/// Get block header. Returns `None` if block is not found.
	fn header(&self, hash: Block::Hash) -> Result<Option<Block::Header>>;
	/// Get blockchain info.
	fn info(&self) -> Info<Block>;
	/// Get block status.
	fn status(&self, hash: Block::Hash) -> Result<BlockStatus>;
	/// Get block number by hash. Returns `None` if the header is not in the chain.
	fn number(
		&self,
		hash: Block::Hash,
	) -> Result<Option<<<Block as BlockT>::Header as HeaderT>::Number>>;
	/// Get block hash by number. Returns `None` if the header is not in the chain.
	fn hash(&self, number: NumberFor<Block>) -> Result<Option<Block::Hash>>;

	/// Convert an arbitrary block ID into a block hash.
	fn block_hash_from_id(&self, id: &BlockId<Block>) -> Result<Option<Block::Hash>> {
		match *id {
			BlockId::Hash(h) => Ok(Some(h)),
			BlockId::Number(n) => self.hash(n),
		}
	}

	/// Convert an arbitrary block ID into a block hash.
	fn block_number_from_id(&self, id: &BlockId<Block>) -> Result<Option<NumberFor<Block>>> {
		match *id {
			BlockId::Hash(h) => self.number(h),
			BlockId::Number(n) => Ok(Some(n)),
		}
	}

	/// Get block header. Returns `UnknownBlock` error if block is not found.
	fn expect_header(&self, hash: Block::Hash) -> Result<Block::Header> {
		self.header(hash)?
			.ok_or_else(|| Error::UnknownBlock(format!("Expect header: {}", hash)))
	}

	/// Convert an arbitrary block ID into a block number. Returns `UnknownBlock` error if block is
	/// not found.
	fn expect_block_number_from_id(&self, id: &BlockId<Block>) -> Result<NumberFor<Block>> {
		self.block_number_from_id(id).and_then(|n| {
			n.ok_or_else(|| Error::UnknownBlock(format!("Expect block number from id: {}", id)))
		})
	}

	/// Convert an arbitrary block ID into a block hash. Returns `UnknownBlock` error if block is
	/// not found.
	fn expect_block_hash_from_id(&self, id: &BlockId<Block>) -> Result<Block::Hash> {
		self.block_hash_from_id(id).and_then(|h| {
			h.ok_or_else(|| Error::UnknownBlock(format!("Expect block hash from id: {}", id)))
		})
	}
}

/// Handles stale forks.
pub trait ForkBackend<Block: BlockT>:
	HeaderMetadata<Block> + HeaderBackend<Block> + Send + Sync
{
	/// Best effort to get all the header hashes that are part of the provided forks
	/// starting only from the fork heads.
	///
	/// The function tries to reconstruct the route from the fork head to the canonical chain.
	/// If any of the hashes on the route can't be found in the db, the function won't be able
	/// to reconstruct the route anymore. In this case it will give up expanding the current fork,
	/// move on to the next ones and at the end it will return an error that also contains
	/// the partially expanded forks.
	fn expand_forks(
		&self,
		fork_heads: &[Block::Hash],
	) -> std::result::Result<BTreeSet<Block::Hash>, (BTreeSet<Block::Hash>, Error)> {
		let mut missing_blocks = vec![];
		let mut expanded_forks = BTreeSet::new();
		for fork_head in fork_heads {
			let mut route_head = *fork_head;
			// Insert stale blocks hashes until canonical chain is reached.
			// If we reach a block that is already part of the `expanded_forks` we can stop
			// processing the fork.
			while expanded_forks.insert(route_head) {
				match self.header_metadata(route_head) {
					Ok(meta) => {
						// If the parent is part of the canonical chain or there doesn't exist a
						// block hash for the parent number (bug?!), we can abort adding blocks.
						let parent_number = meta.number.saturating_sub(1u32.into());
						match self.hash(parent_number) {
							Ok(Some(parent_hash)) =>
								if parent_hash == meta.parent {
									break
								},
							Ok(None) | Err(_) => {
								missing_blocks.push(BlockId::<Block>::Number(parent_number));
								break
							},
						}

						route_head = meta.parent;
					},
					Err(_e) => {
						missing_blocks.push(BlockId::<Block>::Hash(route_head));
						break
					},
				}
			}
		}

		if !missing_blocks.is_empty() {
			return Err((
				expanded_forks,
				Error::UnknownBlocks(format!(
					"Missing stale headers {:?} while expanding forks {:?}.",
					fork_heads, missing_blocks
				)),
			))
		}

		Ok(expanded_forks)
	}
}

impl<Block, T> ForkBackend<Block> for T
where
	Block: BlockT,
	T: HeaderMetadata<Block> + HeaderBackend<Block> + Send + Sync,
{
}

/// Blockchain database backend. Does not perform any validation.
pub trait Backend<Block: BlockT>:
	HeaderBackend<Block> + HeaderMetadata<Block, Error = Error>
{
	/// Get block body. Returns `None` if block is not found.
	fn body(&self, hash: Block::Hash) -> Result<Option<Vec<<Block as BlockT>::Extrinsic>>>;
	/// Get block justifications. Returns `None` if no justification exists.
	fn justifications(&self, hash: Block::Hash) -> Result<Option<Justifications>>;
	/// Get last finalized block hash.
	fn last_finalized(&self) -> Result<Block::Hash>;

	/// Returns hashes of all blocks that are leaves of the block tree.
	/// in other words, that have no children, are chain heads.
	/// Results must be ordered best (longest, highest) chain first.
	fn leaves(&self) -> Result<Vec<Block::Hash>>;

	/// Returns displaced leaves after the given block would be finalized.
	///
	/// The returned leaves do not contain the leaves from the same height as `block_number`.
	fn displaced_leaves_after_finalizing(
		&self,
		block_number: NumberFor<Block>,
	) -> Result<Vec<Block::Hash>>;

	/// Return hashes of all blocks that are children of the block with `parent_hash`.
	fn children(&self, parent_hash: Block::Hash) -> Result<Vec<Block::Hash>>;

	/// Get the most recent block hash of the longest chain that contains
	/// a block with the given `base_hash`.
	///
	/// The search space is always limited to blocks which are in the finalized
	/// chain or descendents of it.
	///
	/// Returns `Ok(None)` if `base_hash` is not found in search space.
	// TODO: document time complexity of this, see [#1444](https://github.com/paritytech/substrate/issues/1444)
	fn longest_containing(
		&self,
		base_hash: Block::Hash,
		import_lock: &RwLock<()>,
	) -> Result<Option<Block::Hash>> {
		let Some(base_header) = self.header(base_hash)? else {
			return Ok(None)
		};

		let leaves = {
			// ensure no blocks are imported during this code block.
			// an import could trigger a reorg which could change the canonical chain.
			// we depend on the canonical chain staying the same during this code block.
			let _import_guard = import_lock.read();
			let info = self.info();
			if info.finalized_number > *base_header.number() {
				// `base_header` is on a dead fork.
				return Ok(None)
			}
			self.leaves()?
		};

		// for each chain. longest chain first. shortest last
		for leaf_hash in leaves {
			let mut current_hash = leaf_hash;
			// go backwards through the chain (via parent links)
			loop {
				if current_hash == base_hash {
					return Ok(Some(leaf_hash))
				}

				let current_header = self
					.header(current_hash)?
					.ok_or_else(|| Error::MissingHeader(current_hash.to_string()))?;

				// stop search in this chain once we go below the target's block number
				if current_header.number() < base_header.number() {
					break
				}

				current_hash = *current_header.parent_hash();
			}
		}

		// header may be on a dead fork -- the only leaves that are considered are
		// those which can still be finalized.
		//
		// FIXME #1558 only issue this warning when not on a dead fork
		warn!(
			"Block {:?} exists in chain but not found when following all leaves backwards",
			base_hash,
		);

		Ok(None)
	}

	/// Get single indexed transaction by content hash. Note that this will only fetch transactions
	/// that are indexed by the runtime with `storage_index_transaction`.
	fn indexed_transaction(&self, hash: Block::Hash) -> Result<Option<Vec<u8>>>;

	/// Check if indexed transaction exists.
	fn has_indexed_transaction(&self, hash: Block::Hash) -> Result<bool> {
		Ok(self.indexed_transaction(hash)?.is_some())
	}

	fn block_indexed_body(&self, hash: Block::Hash) -> Result<Option<Vec<Vec<u8>>>>;
}

/// Blockchain info
#[derive(Debug, Eq, PartialEq)]
pub struct Info<Block: BlockT> {
	/// Best block hash.
	pub best_hash: Block::Hash,
	/// Best block number.
	pub best_number: <<Block as BlockT>::Header as HeaderT>::Number,
	/// Genesis block hash.
	pub genesis_hash: Block::Hash,
	/// The head of the finalized chain.
	pub finalized_hash: Block::Hash,
	/// Last finalized block number.
	pub finalized_number: <<Block as BlockT>::Header as HeaderT>::Number,
	/// Last finalized state.
	pub finalized_state: Option<(Block::Hash, <<Block as BlockT>::Header as HeaderT>::Number)>,
	/// Number of concurrent leave forks.
	pub number_leaves: usize,
	/// Missing blocks after warp sync. (start, end).
	pub block_gap: Option<(NumberFor<Block>, NumberFor<Block>)>,
}

/// Block status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockStatus {
	/// Already in the blockchain.
	InChain,
	/// Not in the queue or the blockchain.
	Unknown,
}

/// A list of all well known keys in the blockchain cache.
pub mod well_known_cache_keys {
	/// The type representing cache keys.
	pub type Id = sp_consensus::CacheKeyId;

	/// A list of authorities.
	pub const AUTHORITIES: Id = *b"auth";

	/// Current Epoch data.
	pub const EPOCH: Id = *b"epch";

	/// Changes trie configuration.
	pub const CHANGES_TRIE_CONFIG: Id = *b"chtr";
}
