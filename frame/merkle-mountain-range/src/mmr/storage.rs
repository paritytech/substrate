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

//! An MMR storage implementation.

use codec::Encode;
use frame_support::log::{debug, trace};
use sp_core::offchain::StorageKind;
use sp_io::offchain_index;
use sp_mmr_primitives::{mmr_lib, mmr_lib::helper, utils::NodesUtils};
use sp_std::iter::Peekable;
#[cfg(not(feature = "std"))]
use sp_std::prelude::*;

use crate::{
	mmr::{Node, NodeOf},
	primitives::{self, NodeIndex},
	Config, Nodes, NumberOfLeaves, Pallet,
};

/// A marker type for runtime-specific storage implementation.
///
/// Allows appending new items to the MMR and proof verification.
/// MMR nodes are appended to two different storages:
/// 1. We add nodes (leaves) hashes to the on-chain storage (see [crate::Nodes]).
/// 2. We add full leaves (and all inner nodes as well) into the `IndexingAPI` during block
///    processing, so the values end up in the Offchain DB if indexing is enabled.
pub struct RuntimeStorage;

/// A marker type for offchain-specific storage implementation.
///
/// Allows proof generation and verification, but does not support appending new items.
/// MMR nodes are assumed to be stored in the Off-Chain DB. Note this storage type
/// DOES NOT support adding new items to the MMR.
pub struct OffchainStorage;

/// A storage layer for MMR.
///
/// There are two different implementations depending on the use case.
/// See docs for [RuntimeStorage] and [OffchainStorage].
pub struct Storage<StorageType, T, I, L>(sp_std::marker::PhantomData<(StorageType, T, I, L)>);

impl<StorageType, T, I, L> Default for Storage<StorageType, T, I, L> {
	fn default() -> Self {
		Self(Default::default())
	}
}

impl<T, I, L> mmr_lib::MMRStore<NodeOf<T, I, L>> for Storage<OffchainStorage, T, I, L>
where
	T: Config<I>,
	I: 'static,
	L: primitives::FullLeaf + codec::Decode,
{
	fn get_elem(&self, pos: NodeIndex) -> mmr_lib::Result<Option<NodeOf<T, I, L>>> {
		let leaves = NumberOfLeaves::<T, I>::get();
		// Find out which leaf added node `pos` in the MMR.
		let ancestor_leaf_idx = NodesUtils::leaf_index_that_added_node(pos);

		// We should only get here when trying to generate proofs. The client requests
		// for proofs for finalized blocks, which should usually be already canonicalized,
		// unless the MMR client gadget has a delay.
		let key = Pallet::<T, I>::node_canon_offchain_key(pos);
		debug!(
			target: "runtime::mmr::offchain", "offchain db get {}: leaf idx {:?}, canon key {:?}",
			pos, ancestor_leaf_idx, key
		);
		// Try to retrieve the element from Off-chain DB.
		if let Some(elem) = sp_io::offchain::local_storage_get(StorageKind::PERSISTENT, &key) {
			return Ok(codec::Decode::decode(&mut &*elem).ok())
		}

		// Fall through to searching node using fork-specific key.
		let ancestor_parent_block_num =
			Pallet::<T, I>::leaf_index_to_parent_block_num(ancestor_leaf_idx, leaves);
		let ancestor_parent_hash = <frame_system::Pallet<T>>::block_hash(ancestor_parent_block_num);
		let temp_key = Pallet::<T, I>::node_temp_offchain_key(pos, ancestor_parent_hash);
		debug!(
			target: "runtime::mmr::offchain",
			"offchain db get {}: leaf idx {:?}, hash {:?}, temp key {:?}",
			pos, ancestor_leaf_idx, ancestor_parent_hash, temp_key
		);
		// Retrieve the element from Off-chain DB.
		Ok(sp_io::offchain::local_storage_get(StorageKind::PERSISTENT, &temp_key)
			.and_then(|v| codec::Decode::decode(&mut &*v).ok()))
	}

	fn append(&mut self, _: NodeIndex, _: Vec<NodeOf<T, I, L>>) -> mmr_lib::Result<()> {
		panic!("MMR must not be altered in the off-chain context.")
	}
}

impl<T, I, L> mmr_lib::MMRStore<NodeOf<T, I, L>> for Storage<RuntimeStorage, T, I, L>
where
	T: Config<I>,
	I: 'static,
	L: primitives::FullLeaf,
{
	fn get_elem(&self, pos: NodeIndex) -> mmr_lib::Result<Option<NodeOf<T, I, L>>> {
		Ok(<Nodes<T, I>>::get(pos).map(Node::Hash))
	}

	fn append(&mut self, pos: NodeIndex, elems: Vec<NodeOf<T, I, L>>) -> mmr_lib::Result<()> {
		if elems.is_empty() {
			return Ok(())
		}

		trace!(
			target: "runtime::mmr", "elems: {:?}",
			elems.iter().map(|elem| elem.hash()).collect::<Vec<_>>()
		);

		let leaves = NumberOfLeaves::<T, I>::get();
		let size = NodesUtils::new(leaves).size();

		if pos != size {
			return Err(mmr_lib::Error::InconsistentStore)
		}

		let new_size = size + elems.len() as NodeIndex;

		// A sorted (ascending) iterator over peak indices to prune and persist.
		let (peaks_to_prune, mut peaks_to_store) = peaks_to_prune_and_store(size, new_size);

		// Now we are going to iterate over elements to insert
		// and keep track of the current `node_index` and `leaf_index`.
		let mut leaf_index = leaves;
		let mut node_index = size;

		// Use parent hash of block adding new nodes (this block) as extra identifier
		// in offchain DB to avoid DB collisions and overwrites in case of forks.
		let parent_hash = <frame_system::Pallet<T>>::parent_hash();
		for elem in elems {
			// On-chain we are going to only store new peaks.
			if peaks_to_store.next_if_eq(&node_index).is_some() {
				<Nodes<T, I>>::insert(node_index, elem.hash());
			}
			// We are storing full node off-chain (using indexing API).
			Self::store_to_offchain(node_index, parent_hash, &elem);

			// Increase the indices.
			if let Node::Data(..) = elem {
				leaf_index += 1;
			}
			node_index += 1;
		}

		// Update current number of leaves.
		NumberOfLeaves::<T, I>::put(leaf_index);

		// And remove all remaining items from `peaks_before` collection.
		for pos in peaks_to_prune {
			<Nodes<T, I>>::remove(pos);
		}

		Ok(())
	}
}

impl<T, I, L> Storage<RuntimeStorage, T, I, L>
where
	T: Config<I>,
	I: 'static,
	L: primitives::FullLeaf,
{
	fn store_to_offchain(
		pos: NodeIndex,
		parent_hash: <T as frame_system::Config>::Hash,
		node: &NodeOf<T, I, L>,
	) {
		let encoded_node = node.encode();
		// We store this leaf offchain keyed by `(parent_hash, node_index)` to make it
		// fork-resistant. The MMR client gadget task will "canonicalize" it on the first
		// finality notification that follows, when we are not worried about forks anymore.
		let temp_key = Pallet::<T, I>::node_temp_offchain_key(pos, parent_hash);
		debug!(
			target: "runtime::mmr::offchain", "offchain db set: pos {} parent_hash {:?} key {:?}",
			pos, parent_hash, temp_key
		);
		// Indexing API is used to store the full node content.
		offchain_index::set(&temp_key, &encoded_node);
	}
}

fn peaks_to_prune_and_store(
	old_size: NodeIndex,
	new_size: NodeIndex,
) -> (impl Iterator<Item = NodeIndex>, Peekable<impl Iterator<Item = NodeIndex>>) {
	// A sorted (ascending) collection of peak indices before and after insertion.
	// both collections may share a common prefix.
	let peaks_before = if old_size == 0 { vec![] } else { helper::get_peaks(old_size) };
	let peaks_after = helper::get_peaks(new_size);
	trace!(target: "runtime::mmr", "peaks_before: {:?}", peaks_before);
	trace!(target: "runtime::mmr", "peaks_after: {:?}", peaks_after);
	let mut peaks_before = peaks_before.into_iter().peekable();
	let mut peaks_after = peaks_after.into_iter().peekable();

	// Consume a common prefix between `peaks_before` and `peaks_after`,
	// since that's something we will not be touching anyway.
	while peaks_before.peek() == peaks_after.peek() {
		peaks_before.next();
		peaks_after.next();
	}

	// what's left in both collections is:
	// 1. Old peaks to remove from storage
	// 2. New peaks to persist in storage
	(peaks_before, peaks_after)
}
