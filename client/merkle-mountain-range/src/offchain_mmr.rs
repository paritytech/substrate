// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Logic for canonicalizing MMR offchain entries for finalized forks,
//! and for pruning MMR offchain entries for stale forks.

#![warn(missing_docs)]

use std::{marker::PhantomData, sync::Arc};

use log::{debug, error, warn};

use sc_client_api::FinalityNotification;
use sc_offchain::OffchainDb;
use sp_blockchain::{CachedHeaderMetadata, ForkBackend, HeaderBackend, HeaderMetadata};
use sp_core::offchain::{DbExternalities, OffchainStorage, StorageKind};
use sp_mmr_primitives::{utils, utils::NodesUtils, NodeIndex};
use sp_runtime::traits::{Block, Header};

use crate::LOG_TARGET;

/// `OffchainMMR` exposes MMR offchain canonicalization and pruning logic.
pub struct OffchainMMR<C, B: Block, S> {
	pub client: Arc<C>,
	pub offchain_db: OffchainDb<S>,
	pub indexing_prefix: Vec<u8>,
	pub first_mmr_block: <B::Header as Header>::Number,

	pub _phantom: PhantomData<B>,
}

impl<C, S, B> OffchainMMR<C, B, S>
where
	C: HeaderBackend<B> + HeaderMetadata<B>,
	S: OffchainStorage,
	B: Block,
{
	fn node_temp_offchain_key(&self, pos: NodeIndex, parent_hash: B::Hash) -> Vec<u8> {
		NodesUtils::node_temp_offchain_key::<B::Header>(&self.indexing_prefix, pos, parent_hash)
	}

	fn node_canon_offchain_key(&self, pos: NodeIndex) -> Vec<u8> {
		NodesUtils::node_canon_offchain_key(&self.indexing_prefix, pos)
	}

	fn header_metadata_or_log(
		&self,
		hash: B::Hash,
		action: &str,
	) -> Option<CachedHeaderMetadata<B>> {
		match self.client.header_metadata(hash) {
			Ok(header) => Some(header),
			_ => {
				debug!(
					target: LOG_TARGET,
					"Block {} not found. Couldn't {} associated branch.", hash, action
				);
				None
			},
		}
	}

	fn right_branch_ending_in_block_or_log(
		&self,
		block_num: <B::Header as Header>::Number,
		action: &str,
	) -> Option<Vec<NodeIndex>> {
		match utils::block_num_to_leaf_index::<B::Header>(block_num, self.first_mmr_block) {
			Ok(leaf_idx) => {
				let branch = NodesUtils::right_branch_ending_in_leaf(leaf_idx);
				debug!(
					target: LOG_TARGET,
					"Nodes to {} for block {}: {:?}", action, block_num, branch
				);
				Some(branch)
			},
			Err(e) => {
				error!(
					target: LOG_TARGET,
					"Error converting block number {} to leaf index: {:?}. \
					Couldn't {} associated branch.",
					block_num,
					e,
					action
				);
				None
			},
		}
	}

	fn prune_branch(&mut self, block_hash: &B::Hash) {
		let action = "prune";
		let header = match self.header_metadata_or_log(*block_hash, action) {
			Some(header) => header,
			_ => return,
		};

		// We prune the leaf associated with the provided block and all the nodes added by that
		// leaf.
		let stale_nodes = match self.right_branch_ending_in_block_or_log(header.number, action) {
			Some(nodes) => nodes,
			None => {
				// If we can't convert the block number to a leaf index, the chain state is probably
				// corrupted. We only log the error, hoping that the chain state will be fixed.
				return
			},
		};

		for pos in stale_nodes {
			let temp_key = self.node_temp_offchain_key(pos, header.parent);
			self.offchain_db.local_storage_clear(StorageKind::PERSISTENT, &temp_key);
			debug!(target: LOG_TARGET, "Pruned elem at pos {} with temp key {:?}", pos, temp_key);
		}
	}

	fn canonicalize_branch(&mut self, block_hash: &B::Hash) {
		let action = "canonicalize";
		let header = match self.header_metadata_or_log(*block_hash, action) {
			Some(header) => header,
			_ => return,
		};

		// Don't canonicalize branches corresponding to blocks for which the MMR pallet
		// wasn't yet initialized.
		if header.number < self.first_mmr_block {
			return
		}

		// We "canonicalize" the leaf associated with the provided block
		// and all the nodes added by that leaf.
		let to_canon_nodes = match self.right_branch_ending_in_block_or_log(header.number, action) {
			Some(nodes) => nodes,
			None => {
				// If we can't convert the block number to a leaf index, the chain state is probably
				// corrupted. We only log the error, hoping that the chain state will be fixed.
				return
			},
		};

		for pos in to_canon_nodes {
			let temp_key = self.node_temp_offchain_key(pos, header.parent);
			if let Some(elem) =
				self.offchain_db.local_storage_get(StorageKind::PERSISTENT, &temp_key)
			{
				let canon_key = self.node_canon_offchain_key(pos);
				self.offchain_db.local_storage_set(StorageKind::PERSISTENT, &canon_key, &elem);
				self.offchain_db.local_storage_clear(StorageKind::PERSISTENT, &temp_key);
				debug!(
					target: LOG_TARGET,
					"Moved elem at pos {} from temp key {:?} to canon key {:?}",
					pos,
					temp_key,
					canon_key
				);
			} else {
				debug!(
					target: LOG_TARGET,
					"Couldn't canonicalize elem at pos {} using temp key {:?}", pos, temp_key
				);
			}
		}
	}

	/// Move leafs and nodes added by finalized blocks in offchain db from _fork-aware key_ to
	/// _canonical key_.
	/// Prune leafs and nodes added by stale blocks in offchain db from _fork-aware key_.
	pub fn canonicalize_and_prune(&mut self, notification: &FinalityNotification<B>) {
		// Move offchain MMR nodes for finalized blocks to canonical keys.
		for block_hash in notification.tree_route.iter().chain(std::iter::once(&notification.hash))
		{
			self.canonicalize_branch(block_hash);
		}

		// Remove offchain MMR nodes for stale forks.
		let stale_forks = self.client.expand_forks(&notification.stale_heads).unwrap_or_else(
			|(stale_forks, e)| {
				warn!(target: LOG_TARGET, "{:?}", e);
				stale_forks
			},
		);
		for hash in stale_forks.iter() {
			self.prune_branch(hash);
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::test_utils::run_test_with_mmr_gadget;
	use sp_runtime::generic::BlockId;
	use std::time::Duration;

	#[test]
	fn canonicalize_and_prune_works_correctly() {
		run_test_with_mmr_gadget(|client| async move {
			//                     -> D4 -> D5
			// G -> A1 -> A2 -> A3 -> A4
			//   -> B1 -> B2 -> B3
			//   -> C1

			let a1 = client.import_block(&BlockId::Number(0), b"a1", Some(0)).await;
			let a2 = client.import_block(&BlockId::Hash(a1.hash()), b"a2", Some(1)).await;
			let a3 = client.import_block(&BlockId::Hash(a2.hash()), b"a3", Some(2)).await;
			let a4 = client.import_block(&BlockId::Hash(a3.hash()), b"a4", Some(3)).await;

			let b1 = client.import_block(&BlockId::Number(0), b"b1", Some(0)).await;
			let b2 = client.import_block(&BlockId::Hash(b1.hash()), b"b2", Some(1)).await;
			let b3 = client.import_block(&BlockId::Hash(b2.hash()), b"b3", Some(2)).await;

			let c1 = client.import_block(&BlockId::Number(0), b"c1", Some(0)).await;

			let d4 = client.import_block(&BlockId::Hash(a3.hash()), b"d4", Some(3)).await;
			let d5 = client.import_block(&BlockId::Hash(d4.hash()), b"d5", Some(4)).await;

			client.finalize_block(a3.hash(), Some(3));
			async_std::task::sleep(Duration::from_millis(200)).await;
			// expected finalized heads: a1, a2, a3
			client.assert_canonicalized(&[&a1, &a2, &a3]);
			// expected stale heads: c1
			// expected pruned heads because of temp key collision: b1
			client.assert_pruned(&[&c1, &b1]);

			client.finalize_block(d5.hash(), None);
			async_std::task::sleep(Duration::from_millis(200)).await;
			// expected finalized heads: d4, d5,
			client.assert_canonicalized(&[&d4, &d5]);
			// expected stale heads: b1, b2, b3, a4
			client.assert_pruned(&[&b1, &b2, &b3, &a4]);
		})
	}
}
