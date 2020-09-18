// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
//! NOTE This pallet is experimental and not proven to work in production.
//!
#![cfg_attr(not(feature = "std"), no_std)]

use codec::Encode;
use frame_support::{
	debug, decl_module, decl_storage,
	weights::Weight,
	traits::Get,
};
use sp_runtime::traits;

mod mmr;
mod primitives;
#[cfg(test)]
mod tests;

/// This pallet's configuration trait
pub trait Trait: frame_system::Trait {
	/// A hasher type for MMR.
	///
	/// To construct trie nodes that result in merging (bagging) two peaks, depending on the node
	/// kind we take either:
	/// - The node (hash) itself if it's an inner node.
	/// - The hash of SCALE-encoding of the leaf data if it's a leaf node.
	///
	/// Then we create a tuple of these two hashes, SCALE-encode it (concatenate) and
	/// hash, to obtain a new MMR inner node - the new peak.
	type Hashing: traits::Hash<Output = <Self as Trait>::Hash>;

	/// The hashing output type.
	///
	/// This type is actually going to be stored in the MMR.
	/// Required to be provided again, to satisfy trait bounds for storage items.
	type Hash: traits::Member + traits::MaybeSerializeDeserialize + sp_std::fmt::Debug
		+ sp_std::hash::Hash + AsRef<[u8]> + AsMut<[u8]> + Copy + Default + codec::Codec
		+ codec::EncodeLike;

	/// Data stored in the leaf nodes.
	///
	/// By default every leaf node will always include a (parent) block hash and
	/// any additional [LeafData](primitives::LeafDataProvider) defined by this type.
	type LeafData: primitives::LeafDataProvider;
}

decl_storage! {
	trait Store for Module<T: Trait> as MerkleMountainRange {
		/// Latest MMR Root hash.
		pub RootHash get(fn mmr_root_hash): <T as Trait>::Hash;

		/// Current size of the MMR (number of leaves).
		pub NumberOfLeaves get(fn mmr_leaves): u64;

		/// Hashes of the nodes in the MMR.
		///
		/// Note this collection only contains MMR peaks, the inner nodes (and leaves)
		/// are pruned and only stored in the Offchain DB.
		pub Nodes get(fn mmr_peak): map hasher(identity) u64 => Option<<T as Trait>::Hash>;

		// TODO [ToDr] Populate initial MMR?
	}
}

decl_module! {
	/// A public part of the pallet.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn on_initialize(n: T::BlockNumber) -> Weight {
			use primitives::LeafDataProvider;

			let hash = <frame_system::Module<T>>::parent_hash();
			let (data, leaf_weight) = T::LeafData::leaf_data();
			// append new leaf to MMR
			let mut mmr: ModuleMMR<mmr::storage::RuntimeStorage, T> = mmr::MMR::new(Self::mmr_leaves());
			mmr.push(primitives::Leaf { hash, data }).expect("MMR push never fails.");

			// update the size
			let (leaves, root) = mmr.finalize().expect("MMR finalize never fails.");
			<NumberOfLeaves>::put(leaves);
			<RootHash<T>>::put(root);

			let pruned = Self::prune_non_peaks();
			let peaks = mmr::utils::NodesUtils::new(leaves).number_of_peaks();

			leaf_weight + <T as frame_system::Trait>::DbWeight::get().reads_writes(
				2 + peaks,
				2 + peaks + pruned
			)
		}
	}
}

/// A MMR specific to the pallet.
type ModuleMMR<StorageType, T> = mmr::MMR<StorageType, T, LeafOf<T>>;

/// Leaf data.
type LeafOf<T> = primitives::Leaf<
	<T as frame_system::Trait>::Hash,
	<<T as Trait>::LeafData as primitives::LeafDataProvider>::LeafData
>;

impl<T: Trait> Module<T> {
	/// Prune leaf & inner nodes that are no longer necessary to keep.
	///
	/// Returns the number of nodes pruned.
	fn prune_non_peaks() -> u64 {
		debug::native::info!("Pruning MMR of size: {:?}", Self::mmr_leaves());
		// TODO [ToDr] Implement me
		0
	}

	fn offchain_key(pos: u64) -> Vec<u8> {
		// TODO [ToDr] Configurable?
		(b"mmr-", pos).encode()
	}

	/// Generate a MMR proof for given `leaf_index`.
	///
	/// Note this method can only be used from an off-chain context
	/// (Offchain Worker or Runtime API call), since it requires
	/// all the leaves to be present.
	/// It may return an error or panic if used incorrectly.
	pub fn generate_proof(leaf_index: u64) -> Result<
		(LeafOf<T>, primitives::Proof<<T as Trait>::Hash>),
		mmr::Error,
	> {
		let mmr: ModuleMMR<mmr::storage::OffchainStorage, T> = mmr::MMR::new(Self::mmr_leaves());
		mmr.generate_proof(leaf_index)
	}

	/// Verify MMR proof for given `leaf`.
	///
	/// This method is safe to use within the runtime code.
	/// It will return `Ok(())` if the proof is valid
	/// and an `Err(..)` if MMR is inconsistent (some leaves are missing)
	/// or the proof is invalid.
	pub fn verify_leaf(leaf: LeafOf<T>, proof: primitives::Proof<<T as Trait>::Hash>) -> Result<(), mmr::Error> {
		if proof.leaf_count > Self::mmr_leaves()
			|| proof.leaf_count == 0
			|| proof.items.len() as u64 > proof.leaf_count
		{
			return Err(mmr::Error::Verify.debug("Invalid leaf count."));
		}

		let mmr: ModuleMMR<mmr::storage::RuntimeStorage, T> = mmr::MMR::new(proof.leaf_count);
		let is_valid = mmr.verify_leaf_proof(leaf, proof)?;
		if is_valid {
			Ok(())
		} else {
			Err(mmr::Error::Verify.debug("Incorrect proof."))
		}
	}
}
