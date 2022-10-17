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

//! # Merkle Mountain Range
//!
//! ## Overview
//!
//! Details on Merkle Mountain Ranges (MMRs) can be found here:
//! <https://github.com/mimblewimble/grin/blob/master/doc/mmr.md>
//!
//! The MMR pallet constructs a MMR from leaf data obtained on every block from
//! `LeafDataProvider`. MMR nodes are stored both in:
//! - on-chain storage - hashes only; not full leaf content)
//! - off-chain storage - via Indexing API we push full leaf content (and all internal nodes as
//! well) to the Off-chain DB, so that the data is available for Off-chain workers.
//! Hashing used for MMR is configurable independently from the rest of the runtime (i.e. not using
//! `frame_system::Hashing`) so something compatible with external chains can be used (like
//! Keccak256 for Ethereum compatibility).
//!
//! Depending on the usage context (off-chain vs on-chain) the pallet is able to:
//! - verify MMR leaf proofs (on-chain)
//! - generate leaf proofs (off-chain)
//!
//! See [primitives::Compact] documentation for how you can optimize proof size for leafs that are
//! composed from multiple elements.
//!
//! ## What for?
//!
//! Primary use case for this pallet is to generate MMR root hashes, that can latter on be used by
//! BEEFY protocol (see <https://github.com/paritytech/grandpa-bridge-gadget>).
//! MMR root hashes along with BEEFY will make it possible to build Super Light Clients (SLC) of
//! Substrate-based chains. The SLC will be able to follow finality and can be shown proofs of more
//! details that happened on the source chain.
//! In that case the chain which contains the pallet generates the Root Hashes and Proofs, which
//! are then presented to another chain acting as a light client which can verify them.
//!
//! Secondary use case is to archive historical data, but still be able to retrieve them on-demand
//! if needed. For instance if parent block hashes are stored in the MMR it's possible at any point
//! in time to provide a MMR proof about some past block hash, while this data can be safely pruned
//! from on-chain storage.
//!
//! NOTE This pallet is experimental and not proven to work in production.
#![cfg_attr(not(feature = "std"), no_std)]

use codec::Encode;
use frame_support::{log, traits::Get, weights::Weight};
use sp_runtime::{
	traits::{self, CheckedSub, One, Saturating, UniqueSaturatedInto},
	SaturatedConversion,
};

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
mod default_weights;
mod mmr;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

pub use pallet::*;
pub use sp_mmr_primitives::{self as primitives, Error, LeafDataProvider, LeafIndex, NodeIndex};
use sp_std::prelude::*;

/// The most common use case for MMRs is to store historical block hashes,
/// so that any point in time in the future we can receive a proof about some past
/// blocks without using excessive on-chain storage.
///
/// Hence we implement the [LeafDataProvider] for [ParentNumberAndHash] which is a
/// crate-local wrapper over [frame_system::Pallet]. Since the current block hash
/// is not available (since the block is not finished yet),
/// we use the `parent_hash` here along with parent block number.
pub struct ParentNumberAndHash<T: frame_system::Config> {
	_phanthom: sp_std::marker::PhantomData<T>,
}

impl<T: frame_system::Config> LeafDataProvider for ParentNumberAndHash<T> {
	type LeafData = (<T as frame_system::Config>::BlockNumber, <T as frame_system::Config>::Hash);

	fn leaf_data() -> Self::LeafData {
		(
			frame_system::Pallet::<T>::block_number().saturating_sub(One::one()),
			frame_system::Pallet::<T>::parent_hash(),
		)
	}
}

pub trait WeightInfo {
	fn on_initialize(peaks: NodeIndex) -> Weight;
}

/// A MMR specific to the pallet.
type ModuleMmr<StorageType, T, I> = mmr::Mmr<StorageType, T, I, LeafOf<T, I>>;

/// Leaf data.
type LeafOf<T, I> = <<T as Config<I>>::LeafData as primitives::LeafDataProvider>::LeafData;

/// Hashing used for the pallet.
pub(crate) type HashingOf<T, I> = <T as Config<I>>::Hashing;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	/// This pallet's configuration trait
	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// Prefix for elements stored in the Off-chain DB via Indexing API.
		///
		/// Each node of the MMR is inserted both on-chain and off-chain via Indexing API.
		/// The former does not store full leaf content, just its compact version (hash),
		/// and some of the inner mmr nodes might be pruned from on-chain storage.
		/// The latter will contain all the entries in their full form.
		///
		/// Each node is stored in the Off-chain DB under key derived from the
		/// [`Self::INDEXING_PREFIX`] and its in-tree index (MMR position).
		const INDEXING_PREFIX: &'static [u8];

		/// A hasher type for MMR.
		///
		/// To construct trie nodes that result in merging (bagging) two peaks, depending on the
		/// node kind we take either:
		/// - The node (hash) itself if it's an inner node.
		/// - The hash of SCALE-encoding of the leaf data if it's a leaf node.
		///
		/// Then we create a tuple of these two hashes, SCALE-encode it (concatenate) and
		/// hash, to obtain a new MMR inner node - the new peak.
		type Hashing: traits::Hash<Output = <Self as Config<I>>::Hash>;

		/// The hashing output type.
		///
		/// This type is actually going to be stored in the MMR.
		/// Required to be provided again, to satisfy trait bounds for storage items.
		type Hash: traits::Member
			+ traits::MaybeSerializeDeserialize
			+ sp_std::fmt::Debug
			+ sp_std::hash::Hash
			+ AsRef<[u8]>
			+ AsMut<[u8]>
			+ Copy
			+ Default
			+ codec::Codec
			+ codec::EncodeLike
			+ scale_info::TypeInfo
			+ MaxEncodedLen;

		/// Data stored in the leaf nodes.
		///
		/// The [LeafData](primitives::LeafDataProvider) is responsible for returning the entire
		/// leaf data that will be inserted to the MMR.
		/// [LeafDataProvider](primitives::LeafDataProvider)s can be composed into tuples to put
		/// multiple elements into the tree. In such a case it might be worth using
		/// [primitives::Compact] to make MMR proof for one element of the tuple leaner.
		///
		/// Note that the leaf at each block MUST be unique. You may want to include a block hash or
		/// block number as an easiest way to ensure that.
		/// Also note that the leaf added by each block is expected to only reference data coming
		/// from ancestor blocks (leaves are saved offchain using `(pos, parent_hash)` key to be
		/// fork-resistant, as such conflicts could only happen on 1-block deep forks, which means
		/// two forks with identical line of ancestors compete to write the same offchain key, but
		/// that's fine as long as leaves only contain data coming from ancestors - conflicting
		/// writes are identical).
		type LeafData: primitives::LeafDataProvider;

		/// A hook to act on the new MMR root.
		///
		/// For some applications it might be beneficial to make the MMR root available externally
		/// apart from having it in the storage. For instance you might output it in the header
		/// digest (see [`frame_system::Pallet::deposit_log`]) to make it available for Light
		/// Clients. Hook complexity should be `O(1)`.
		type OnNewRoot: primitives::OnNewRoot<<Self as Config<I>>::Hash>;

		/// Weights for this pallet.
		type WeightInfo: WeightInfo;
	}

	/// Latest MMR Root hash.
	#[pallet::storage]
	#[pallet::getter(fn mmr_root_hash)]
	pub type RootHash<T: Config<I>, I: 'static = ()> =
		StorageValue<_, <T as Config<I>>::Hash, ValueQuery>;

	/// Current size of the MMR (number of leaves).
	#[pallet::storage]
	#[pallet::getter(fn mmr_leaves)]
	pub type NumberOfLeaves<T, I = ()> = StorageValue<_, LeafIndex, ValueQuery>;

	/// Hashes of the nodes in the MMR.
	///
	/// Note this collection only contains MMR peaks, the inner nodes (and leaves)
	/// are pruned and only stored in the Offchain DB.
	#[pallet::storage]
	#[pallet::getter(fn mmr_peak)]
	pub type Nodes<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Identity, NodeIndex, <T as Config<I>>::Hash, OptionQuery>;

	#[pallet::hooks]
	impl<T: Config<I>, I: 'static> Hooks<BlockNumberFor<T>> for Pallet<T, I> {
		fn on_initialize(_n: T::BlockNumber) -> Weight {
			use primitives::LeafDataProvider;
			let leaves = Self::mmr_leaves();
			let peaks_before = mmr::utils::NodesUtils::new(leaves).number_of_peaks();
			let data = T::LeafData::leaf_data();

			// append new leaf to MMR
			let mut mmr: ModuleMmr<mmr::storage::RuntimeStorage, T, I> = mmr::Mmr::new(leaves);
			// MMR push never fails, but better safe than sorry.
			if mmr.push(data).is_none() {
				log::error!(target: "runtime::mmr", "MMR push failed");
				return T::WeightInfo::on_initialize(peaks_before)
			}
			// Update the size, `mmr.finalize()` should also never fail.
			let (leaves, root) = match mmr.finalize() {
				Ok((leaves, root)) => (leaves, root),
				Err(e) => {
					log::error!(target: "runtime::mmr", "MMR finalize failed: {:?}", e);
					return T::WeightInfo::on_initialize(peaks_before)
				},
			};
			<T::OnNewRoot as primitives::OnNewRoot<_>>::on_new_root(&root);

			<NumberOfLeaves<T, I>>::put(leaves);
			<RootHash<T, I>>::put(root);

			let peaks_after = mmr::utils::NodesUtils::new(leaves).number_of_peaks();

			T::WeightInfo::on_initialize(peaks_before.max(peaks_after))
		}

		fn offchain_worker(n: T::BlockNumber) {
			use mmr::storage::{OffchainStorage, Storage};
			// The MMR nodes can be found in offchain db under either:
			//   - fork-unique keys `(prefix, pos, parent_hash)`, or,
			//   - "canonical" keys `(prefix, pos)`,
			//   depending on how many blocks in the past the node at position `pos` was
			//   added to the MMR.
			//
			// For the fork-unique keys, the MMR pallet depends on
			// `frame_system::block_hash(parent_num)` mappings to find the relevant parent block
			// hashes, so it is limited by `frame_system::BlockHashCount` in terms of how many
			// historical forks it can track. Nodes added to MMR by block `N` can be found in
			// offchain db at:
			//   - fork-unique keys `(prefix, pos, parent_hash)` when (`N` >= `latest_block` -
			//     `frame_system::BlockHashCount`);
			//   - "canonical" keys `(prefix, pos)` when (`N` < `latest_block` -
			//     `frame_system::BlockHashCount`);
			//
			// The offchain worker is responsible for maintaining the nodes' positions in
			// offchain db as the chain progresses by moving a rolling window of the same size as
			// `frame_system::block_hash` map, where nodes/leaves added by blocks that are just
			// about to exit the window are "canonicalized" so that their offchain key no longer
			// depends on `parent_hash`.
			//
			// This approach works to eliminate fork-induced leaf collisions in offchain db,
			// under the assumption that no fork will be deeper than `frame_system::BlockHashCount`
			// blocks:
			//   entries pertaining to block `N` where `N < current-BlockHashCount` are moved to a
			//   key based solely on block number. The only way to have collisions is if two
			//   competing forks are deeper than `frame_system::BlockHashCount` blocks and they
			//   both "canonicalize" their view of block `N`
			// Once a block is canonicalized, all MMR entries pertaining to sibling blocks from
			// other forks are pruned from offchain db.
			Storage::<OffchainStorage, T, I, LeafOf<T, I>>::canonicalize_and_prune(n);
		}
	}
}

/// Stateless MMR proof verification for batch of leaves.
///
/// This function can be used to verify received MMR [primitives::BatchProof] (`proof`)
/// for given leaves set (`leaves`) against a known MMR root hash (`root`).
/// Note, the leaves should be sorted such that corresponding leaves and leaf indices have the
/// same position in both the `leaves` vector and the `leaf_indices` vector contained in the
/// [primitives::BatchProof].
pub fn verify_leaves_proof<H, L>(
	root: H::Output,
	leaves: Vec<mmr::Node<H, L>>,
	proof: primitives::BatchProof<H::Output>,
) -> Result<(), primitives::Error>
where
	H: traits::Hash,
	L: primitives::FullLeaf,
{
	let is_valid = mmr::verify_leaves_proof::<H, L>(root, leaves, proof)?;
	if is_valid {
		Ok(())
	} else {
		Err(primitives::Error::Verify.log_debug(("The proof is incorrect.", root)))
	}
}

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Build offchain key from `parent_hash` of block that originally added node `pos` to MMR.
	///
	/// This combination makes the offchain (key,value) entry resilient to chain forks.
	fn node_offchain_key(
		pos: NodeIndex,
		parent_hash: <T as frame_system::Config>::Hash,
	) -> sp_std::prelude::Vec<u8> {
		(T::INDEXING_PREFIX, pos, parent_hash).encode()
	}

	/// Build canonical offchain key for node `pos` in MMR.
	///
	/// Used for nodes added by now finalized blocks.
	/// Never read keys using `node_canon_offchain_key` unless you sure that
	/// there's no `node_offchain_key` key in the storage.
	fn node_canon_offchain_key(pos: NodeIndex) -> sp_std::prelude::Vec<u8> {
		(T::INDEXING_PREFIX, pos).encode()
	}

	/// Return size of rolling window of leaves saved in offchain under fork-unique keys.
	///
	/// Leaves outside this window are canonicalized.
	/// Window size is `frame_system::BlockHashCount - 1` to make sure fork-unique keys
	/// can be built using `frame_system::block_hash` map.
	fn offchain_canonicalization_window() -> LeafIndex {
		let window_size: LeafIndex =
			<T as frame_system::Config>::BlockHashCount::get().unique_saturated_into();
		window_size.saturating_sub(1)
	}

	/// Provide the parent number for the block that added `leaf_index` to the MMR.
	fn leaf_index_to_parent_block_num(
		leaf_index: LeafIndex,
		leaves_count: LeafIndex,
	) -> <T as frame_system::Config>::BlockNumber {
		// leaves are zero-indexed and were added one per block since pallet activation,
		// while block numbers are one-indexed, so block number that added `leaf_idx` is:
		// `block_num = block_num_when_pallet_activated + leaf_idx + 1`
		// `block_num = (current_block_num - leaves_count) + leaf_idx + 1`
		// `parent_block_num = current_block_num - leaves_count + leaf_idx`.
		<frame_system::Pallet<T>>::block_number()
			.saturating_sub(leaves_count.saturated_into())
			.saturating_add(leaf_index.saturated_into())
	}

	/// Convert a `block_num` into a leaf index.
	fn block_num_to_leaf_index(block_num: T::BlockNumber) -> Result<LeafIndex, primitives::Error>
	where
		T: frame_system::Config,
	{
		// leaf_idx = (leaves_count - 1) - (current_block_num - block_num);
		let best_block_num = <frame_system::Pallet<T>>::block_number();
		let blocks_diff = best_block_num.checked_sub(&block_num).ok_or_else(|| {
			primitives::Error::BlockNumToLeafIndex
				.log_debug("The provided block_number is greater than the best block number.")
		})?;
		let blocks_diff_as_leaf_idx = blocks_diff.try_into().map_err(|_| {
			primitives::Error::BlockNumToLeafIndex
				.log_debug("The `blocks_diff` couldn't be converted to `LeafIndex`.")
		})?;

		let leaf_idx = Self::mmr_leaves()
			.checked_sub(1)
			.and_then(|last_leaf_idx| last_leaf_idx.checked_sub(blocks_diff_as_leaf_idx))
			.ok_or_else(|| {
				primitives::Error::BlockNumToLeafIndex
					.log_debug("There aren't enough leaves in the chain.")
			})?;
		Ok(leaf_idx)
	}

	/// Generate a MMR proof for the given `block_numbers`.
	///
	/// Note this method can only be used from an off-chain context
	/// (Offchain Worker or Runtime API call), since it requires
	/// all the leaves to be present.
	/// It may return an error or panic if used incorrectly.
	pub fn generate_batch_proof(
		block_numbers: Vec<T::BlockNumber>,
	) -> Result<
		(Vec<LeafOf<T, I>>, primitives::BatchProof<<T as Config<I>>::Hash>),
		primitives::Error,
	> {
		Self::generate_historical_batch_proof(
			block_numbers,
			<frame_system::Pallet<T>>::block_number(),
		)
	}

	/// Generate a MMR proof for the given `block_numbers` given the `best_known_block_number`.
	///
	/// Note this method can only be used from an off-chain context
	/// (Offchain Worker or Runtime API call), since it requires
	/// all the leaves to be present.
	/// It may return an error or panic if used incorrectly.
	pub fn generate_historical_batch_proof(
		block_numbers: Vec<T::BlockNumber>,
		best_known_block_number: T::BlockNumber,
	) -> Result<
		(Vec<LeafOf<T, I>>, primitives::BatchProof<<T as Config<I>>::Hash>),
		primitives::Error,
	> {
		let leaves_count =
			Self::block_num_to_leaf_index(best_known_block_number)?.saturating_add(1);

		// we need to translate the block_numbers into leaf indices.
		let leaf_indices = block_numbers
			.iter()
			.map(|block_num| -> Result<LeafIndex, primitives::Error> {
				Self::block_num_to_leaf_index(*block_num)
			})
			.collect::<Result<Vec<LeafIndex>, _>>()?;

		let mmr: ModuleMmr<mmr::storage::OffchainStorage, T, I> = mmr::Mmr::new(leaves_count);
		mmr.generate_batch_proof(leaf_indices)
	}

	/// Return the on-chain MMR root hash.
	pub fn mmr_root() -> <T as Config<I>>::Hash {
		Self::mmr_root_hash()
	}

	/// Verify MMR proof for given `leaves`.
	///
	/// This method is safe to use within the runtime code.
	/// It will return `Ok(())` if the proof is valid
	/// and an `Err(..)` if MMR is inconsistent (some leaves are missing)
	/// or the proof is invalid.
	pub fn verify_leaves(
		leaves: Vec<LeafOf<T, I>>,
		proof: primitives::BatchProof<<T as Config<I>>::Hash>,
	) -> Result<(), primitives::Error> {
		if proof.leaf_count > Self::mmr_leaves() ||
			proof.leaf_count == 0 ||
			(proof.items.len().saturating_add(leaves.len())) as u64 > proof.leaf_count
		{
			return Err(primitives::Error::Verify
				.log_debug("The proof has incorrect number of leaves or proof items."))
		}

		let mmr: ModuleMmr<mmr::storage::OffchainStorage, T, I> = mmr::Mmr::new(proof.leaf_count);
		let is_valid = mmr.verify_leaves_proof(leaves, proof)?;
		if is_valid {
			Ok(())
		} else {
			Err(primitives::Error::Verify.log_debug("The proof is incorrect."))
		}
	}
}
