// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! A MMR storage implementations.

use codec::Encode;
use frame_support::traits::Get;
use mmr_lib::helper;
use sp_core::offchain::StorageKind;
use sp_io::{offchain, offchain_index};
use sp_runtime::traits::UniqueSaturatedInto;
use sp_std::iter::Peekable;
#[cfg(not(feature = "std"))]
use sp_std::prelude::*;

use crate::{
	mmr::{utils::NodesUtils, Node, NodeOf},
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

/// Suffix of key for the 'pruning_map'.
///
/// Nodes and leaves are initially saved under fork-specific keys in offchain db,
/// eventually they are "canonicalized" and this map is used to prune non-canon entries.
const OFFCHAIN_PRUNING_MAP_KEY_SUFFIX: &str = "pruning_map";

/// Used to store offchain mappings of `BlockNumber -> Vec[Hash]` to track all forks.
/// Size of this offchain map is at most `frame_system::BlockHashCount`, its entries are pruned
/// as part of the mechanism that prunes the forks this map tracks.
pub(crate) struct PruningMap<T, I>(sp_std::marker::PhantomData<(T, I)>);
impl<T, I> PruningMap<T, I>
where
	T: Config<I>,
	I: 'static,
{
	pub(crate) fn pruning_map_offchain_key(block: T::BlockNumber) -> sp_std::prelude::Vec<u8> {
		(T::INDEXING_PREFIX, block, OFFCHAIN_PRUNING_MAP_KEY_SUFFIX).encode()
	}

	/// Append `hash` to the list of parent hashes for `block` in offchain db.
	pub fn append(block: T::BlockNumber, hash: <T as frame_system::Config>::Hash) {
		let map_key = Self::pruning_map_offchain_key(block);
		offchain::local_storage_get(StorageKind::PERSISTENT, &map_key)
			.and_then(|v| codec::Decode::decode(&mut &*v).ok())
			.or_else(|| Some(Vec::<<T as frame_system::Config>::Hash>::new()))
			.map(|mut parents| {
				parents.push(hash);
				offchain::local_storage_set(
					StorageKind::PERSISTENT,
					&map_key,
					&Encode::encode(&parents),
				);
			});
	}

	/// Remove list of parent hashes for `block` from offchain db and return it.
	pub fn remove(block: T::BlockNumber) -> Option<Vec<<T as frame_system::Config>::Hash>> {
		let map_key = Self::pruning_map_offchain_key(block);
		offchain::local_storage_get(StorageKind::PERSISTENT, &map_key).and_then(|v| {
			offchain::local_storage_clear(StorageKind::PERSISTENT, &map_key);
			codec::Decode::decode(&mut &*v).ok()
		})
	}
}

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

impl<T, I, L> Storage<OffchainStorage, T, I, L>
where
	T: Config<I>,
	I: 'static,
	L: primitives::FullLeaf,
{
	/// Move nodes and leaves added by block `N` in offchain db from _fork-aware key_ to
	/// _canonical key_,
	/// where `N` is `frame_system::BlockHashCount` blocks behind current block number.
	///
	/// This "canonicalization" process is required because the _fork-aware key_ value depends
	/// on `frame_system::block_hash(block_num)` map which only holds the last
	/// `frame_system::BlockHashCount` blocks.
	///
	/// For the canonicalized block, prune all nodes pertaining to other forks from offchain db.
	///
	/// Should only be called from offchain context, because it requires both read and write
	/// access to offchain db.
	pub(crate) fn canonicalize_and_prune(block: T::BlockNumber) {
		// Add "block_num -> hash" mapping to offchain db,
		// with all forks pushing hashes to same entry (same block number).
		let parent_hash = <frame_system::Pallet<T>>::parent_hash();
		PruningMap::<T, I>::append(block, parent_hash);

		// Effectively move a rolling window of fork-unique leaves. Once out of the window, leaves
		// are "canonicalized" in offchain by moving them under `Pallet::node_canon_offchain_key`.
		let leaves = NumberOfLeaves::<T, I>::get();
		let window_size =
			<T as frame_system::Config>::BlockHashCount::get().unique_saturated_into();
		if leaves >= window_size {
			// Move the rolling window towards the end of `block_num->hash` mappings available
			// in the runtime: we "canonicalize" the leaf at the end,
			let to_canon_leaf = leaves.saturating_sub(window_size);
			// and all the nodes added by that leaf.
			let to_canon_nodes = NodesUtils::right_branch_ending_in_leaf(to_canon_leaf);
			frame_support::log::debug!(
				target: "runtime::mmr::offchain", "Nodes to canon for leaf {}: {:?}",
				to_canon_leaf, to_canon_nodes
			);
			// For this block number there may be node entries saved from multiple forks.
			let to_canon_block_num =
				Pallet::<T, I>::leaf_index_to_parent_block_num(to_canon_leaf, leaves);
			// Only entries under this hash (retrieved from state on current canon fork) are to be
			// persisted. All other entries added by same block number will be cleared.
			let to_canon_hash = <frame_system::Pallet<T>>::block_hash(to_canon_block_num);

			Self::canonicalize_nodes_for_hash(&to_canon_nodes, to_canon_hash);
			// Get all the forks to prune, also remove them from the offchain pruning_map.
			PruningMap::<T, I>::remove(to_canon_block_num)
				.map(|forks| {
					Self::prune_nodes_for_forks(&to_canon_nodes, forks);
				})
				.unwrap_or_else(|| {
					frame_support::log::error!(
						target: "runtime::mmr::offchain",
						"Offchain: could not prune: no entry in pruning map for block {:?}",
						to_canon_block_num
					);
				})
		}
	}

	fn prune_nodes_for_forks(nodes: &[NodeIndex], forks: Vec<<T as frame_system::Config>::Hash>) {
		for hash in forks {
			for pos in nodes {
				let key = Pallet::<T, I>::node_offchain_key(hash, *pos);
				frame_support::log::debug!(
					target: "runtime::mmr::offchain",
					"Clear elem at pos {} with key {:?}",
					pos, key
				);
				offchain::local_storage_clear(StorageKind::PERSISTENT, &key);
			}
		}
	}

	fn canonicalize_nodes_for_hash(
		to_canon_nodes: &[NodeIndex],
		to_canon_hash: <T as frame_system::Config>::Hash,
	) {
		for pos in to_canon_nodes {
			let key = Pallet::<T, I>::node_offchain_key(to_canon_hash, *pos);
			// Retrieve the element from Off-chain DB under fork-aware key.
			if let Some(elem) = offchain::local_storage_get(StorageKind::PERSISTENT, &key) {
				let canon_key = Pallet::<T, I>::node_canon_offchain_key(*pos);
				// Add under new canon key.
				offchain::local_storage_set(StorageKind::PERSISTENT, &canon_key, &elem);
				frame_support::log::debug!(
					target: "runtime::mmr::offchain",
					"Moved elem at pos {} from key {:?} to canon key {:?}",
					pos, key, canon_key
				);
			} else {
				frame_support::log::error!(
					target: "runtime::mmr::offchain",
					"Could not canonicalize elem at pos {} using key {:?}",
					pos, key
				);
			}
		}
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

		let window_size =
			<T as frame_system::Config>::BlockHashCount::get().unique_saturated_into();
		// Leaves older than this window should have been canonicalized.
		if leaves.saturating_sub(ancestor_leaf_idx) > window_size {
			let key = Pallet::<T, I>::node_canon_offchain_key(pos);
			frame_support::log::debug!(
				target: "runtime::mmr::offchain", "offchain db get {}: leaf idx {:?}, key {:?}",
				pos, ancestor_leaf_idx, key
			);
			// Just for safety, to easily handle runtime upgrades where any of the window params
			// change and maybe we mess up storage migration,
			// return _if and only if_ node is found (in normal conditions it's always found),
			if let Some(elem) =
				sp_io::offchain::local_storage_get(sp_core::offchain::StorageKind::PERSISTENT, &key)
			{
				return Ok(codec::Decode::decode(&mut &*elem).ok())
			}
			// BUT if we DID MESS UP, fall through to searching node using fork-specific key.
		}

		// Leaves still within the window will be found in offchain db under fork-aware keys.
		let ancestor_parent_block_num =
			Pallet::<T, I>::leaf_index_to_parent_block_num(ancestor_leaf_idx, leaves);
		let ancestor_parent_hash = <frame_system::Pallet<T>>::block_hash(ancestor_parent_block_num);
		let key = Pallet::<T, I>::node_offchain_key(ancestor_parent_hash, pos);
		frame_support::log::debug!(
			target: "runtime::mmr::offchain", "offchain db get {}: leaf idx {:?}, hash {:?}, key {:?}",
			pos, ancestor_leaf_idx, ancestor_parent_hash, key
		);
		// Retrieve the element from Off-chain DB.
		Ok(sp_io::offchain::local_storage_get(sp_core::offchain::StorageKind::PERSISTENT, &key)
			.or_else(|| {
				// Again, this is just us being extra paranoid.
				// We get here only if we mess up a storage migration for a runtime upgrades where
				// say the window is increased, and for a little while following the upgrade there's
				// leaves inside new 'window' that had been already canonicalized before upgrade.
				let key = Pallet::<T, I>::node_canon_offchain_key(pos);
				sp_io::offchain::local_storage_get(sp_core::offchain::StorageKind::PERSISTENT, &key)
			})
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

		frame_support::log::trace!(
			target: "runtime::mmr",
			"elems: {:?}",
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
			// For now we store this leaf offchain keyed by `(parent_hash, node_index)`
			// to make it fork-resistant.
			// Offchain worker task will "canonicalize" it `frame_system::BlockHashCount` blocks
			// later when we are not worried about forks anymore (highly unlikely to have a fork
			// in the chain that deep).
			// "Canonicalization" in this case means moving this leaf under a new key based
			// only on the leaf's `node_index`.
			let key = Pallet::<T, I>::node_offchain_key(parent_hash, node_index);
			frame_support::log::debug!(
				target: "runtime::mmr::offchain", "offchain db set: pos {} parent_hash {:?} key {:?}",
				node_index, parent_hash, key
			);
			// Indexing API is used to store the full node content (both leaf and inner).
			elem.using_encoded(|elem| offchain_index::set(&key, elem));

			// On-chain we are going to only store new peaks.
			if peaks_to_store.next_if_eq(&node_index).is_some() {
				<Nodes<T, I>>::insert(node_index, elem.hash());
			}

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

fn peaks_to_prune_and_store(
	old_size: NodeIndex,
	new_size: NodeIndex,
) -> (impl Iterator<Item = NodeIndex>, Peekable<impl Iterator<Item = NodeIndex>>) {
	// A sorted (ascending) collection of peak indices before and after insertion.
	// both collections may share a common prefix.
	let peaks_before = if old_size == 0 { vec![] } else { helper::get_peaks(old_size) };
	let peaks_after = helper::get_peaks(new_size);
	frame_support::log::trace!(target: "runtime::mmr", "peaks_before: {:?}", peaks_before);
	frame_support::log::trace!(target: "runtime::mmr", "peaks_after: {:?}", peaks_after);
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
