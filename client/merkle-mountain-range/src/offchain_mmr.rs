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

use crate::{aux_schema, LOG_TARGET};
use log::{debug, error, info, warn};
use sc_client_api::{AuxStore, Backend, FinalityNotification};
use sc_offchain::OffchainDb;
use sp_blockchain::{CachedHeaderMetadata, ForkBackend, HeaderBackend, HeaderMetadata};
use sp_core::offchain::{DbExternalities, StorageKind};
use sp_mmr_primitives::{utils, utils::NodesUtils, NodeIndex};
use sp_runtime::{
	traits::{Block, NumberFor, One},
	Saturating,
};
use std::{collections::VecDeque, sync::Arc};

pub(crate) fn load_or_init_best_canonicalized<B, BE>(
	backend: &BE,
	first_mmr_block: NumberFor<B>,
) -> sp_blockchain::Result<NumberFor<B>>
where
	BE: AuxStore,
	B: Block,
{
	// Initialize gadget best_canon from AUX DB or from pallet genesis.
	if let Some(best) = aux_schema::load_persistent::<B, BE>(backend)? {
		info!(target: LOG_TARGET, "Loading MMR best canonicalized state from db: {:?}.", best);
		Ok(best)
	} else {
		let best = first_mmr_block.saturating_sub(One::one());
		info!(
			target: LOG_TARGET,
			"Loading MMR from pallet genesis on what appears to be the first startup: {:?}.", best
		);
		aux_schema::write_current_version(backend)?;
		aux_schema::write_gadget_state::<B, BE>(backend, &best)?;
		Ok(best)
	}
}

/// `OffchainMMR` exposes MMR offchain canonicalization and pruning logic.
pub struct OffchainMmr<B: Block, BE: Backend<B>, C> {
	pub backend: Arc<BE>,
	pub client: Arc<C>,
	pub offchain_db: OffchainDb<BE::OffchainStorage>,
	pub indexing_prefix: Vec<u8>,
	pub first_mmr_block: NumberFor<B>,
	pub best_canonicalized: NumberFor<B>,
}

impl<B, BE, C> OffchainMmr<B, BE, C>
where
	C: HeaderBackend<B> + HeaderMetadata<B>,
	BE: Backend<B>,
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
		block_num: NumberFor<B>,
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

	fn canonicalize_branch(&mut self, block_hash: B::Hash) {
		let action = "canonicalize";
		let header = match self.header_metadata_or_log(block_hash, action) {
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
				self.best_canonicalized = header.number;
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
		if self.best_canonicalized != header.number.saturating_sub(One::one()) {
			warn!(
				target: LOG_TARGET,
				"Detected canonicalization skip: best {:?} current {:?}.",
				self.best_canonicalized,
				header.number,
			);
		}
		self.best_canonicalized = header.number;
	}

	/// In case of missed finality notifications (node restarts for example),
	/// make sure to also canon everything leading up to `notification.tree_route`.
	pub fn canonicalize_catch_up(&mut self, notification: &FinalityNotification<B>) {
		let first = notification.tree_route.first().unwrap_or(&notification.hash);
		if let Some(mut header) = self.header_metadata_or_log(*first, "canonicalize") {
			let mut to_canon = VecDeque::<<B as Block>::Hash>::new();
			// Walk up the chain adding all blocks newer than `self.best_canonicalized`.
			loop {
				header = match self.header_metadata_or_log(header.parent, "canonicalize") {
					Some(header) => header,
					_ => break,
				};
				if header.number <= self.best_canonicalized {
					break
				}
				to_canon.push_front(header.hash);
			}
			// Canonicalize all blocks leading up to current finality notification.
			for hash in to_canon.drain(..) {
				self.canonicalize_branch(hash);
			}
			if let Err(e) =
				aux_schema::write_gadget_state::<B, BE>(&*self.backend, &self.best_canonicalized)
			{
				debug!(target: LOG_TARGET, "error saving state: {:?}", e);
			}
		}
	}

	/// Move leafs and nodes added by finalized blocks in offchain db from _fork-aware key_ to
	/// _canonical key_.
	/// Prune leafs and nodes added by stale blocks in offchain db from _fork-aware key_.
	pub fn canonicalize_and_prune(&mut self, notification: FinalityNotification<B>) {
		// Move offchain MMR nodes for finalized blocks to canonical keys.
		for hash in notification.tree_route.iter().chain(std::iter::once(&notification.hash)) {
			self.canonicalize_branch(*hash);
		}
		if let Err(e) =
			aux_schema::write_gadget_state::<B, BE>(&*self.backend, &self.best_canonicalized)
		{
			debug!(target: LOG_TARGET, "error saving state: {:?}", e);
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
	use crate::test_utils::{run_test_with_mmr_gadget, run_test_with_mmr_gadget_pre_post};
	use parking_lot::Mutex;
	use sp_runtime::generic::BlockId;
	use std::{sync::Arc, time::Duration};

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
			tokio::time::sleep(Duration::from_millis(200)).await;
			// expected finalized heads: a1, a2, a3
			client.assert_canonicalized(&[&a1, &a2, &a3]);
			// expected stale heads: c1
			// expected pruned heads because of temp key collision: b1
			client.assert_pruned(&[&c1, &b1]);

			client.finalize_block(d5.hash(), None);
			tokio::time::sleep(Duration::from_millis(200)).await;
			// expected finalized heads: d4, d5,
			client.assert_canonicalized(&[&d4, &d5]);
			// expected stale heads: b1, b2, b3, a4
			client.assert_pruned(&[&b1, &b2, &b3, &a4]);
		})
	}

	#[test]
	fn canonicalize_catchup_works_correctly() {
		let mmr_blocks = Arc::new(Mutex::new(vec![]));
		let mmr_blocks_ref = mmr_blocks.clone();
		run_test_with_mmr_gadget_pre_post(
			|client| async move {
				// G -> A1 -> A2
				//      |     |
				//      |     | -> finalized without gadget (missed notification)
				//      |
				//      | -> first mmr block

				let a1 = client.import_block(&BlockId::Number(0), b"a1", Some(0)).await;
				let a2 = client.import_block(&BlockId::Hash(a1.hash()), b"a2", Some(1)).await;

				client.finalize_block(a2.hash(), Some(2));

				{
					let mut mmr_blocks = mmr_blocks_ref.lock();
					mmr_blocks.push(a1);
					mmr_blocks.push(a2);
				}
			},
			|client| async move {
				// G -> A1 -> A2 -> A3 -> A4
				//      |     |     |     |
				//      |     |     |     | -> finalized after starting gadget
				//      |     |     |
				//      |     |     | -> gadget start
				//      |     |
				//      |     | -> finalized before starting gadget (missed notification)
				//      |
				//      | -> first mmr block
				let blocks = mmr_blocks.lock();
				let a1 = blocks[0].clone();
				let a2 = blocks[1].clone();
				let a3 = client.import_block(&BlockId::Hash(a2.hash()), b"a3", Some(2)).await;
				let a4 = client.import_block(&BlockId::Hash(a3.hash()), b"a4", Some(3)).await;

				client.finalize_block(a4.hash(), Some(4));
				tokio::time::sleep(Duration::from_millis(200)).await;
				// expected finalized heads: a1, a2 _and_ a3, a4.
				client.assert_canonicalized(&[&a1, &a2, &a3, &a4]);
			},
		)
	}
}
