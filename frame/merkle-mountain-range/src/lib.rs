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
//! Details on Merkle Mountain Ranges (MMRs) can be found here:
//! https://github.com/mimblewimble/grin/blob/master/doc/mmr.md
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
//! - verify MMR leafs proofs (on-chain)
//! - generate leaf proofs (off-chain)
//!
//! See [primitives::Compact] documentation for how you can optimize proof size for leafs that are
//! composed from multiple elements.
//!
//! ## What for?
//!
//!	Primary use case for this pallet is to generate MMR root hashes, that can later on be used by
//!	BEEFY protocol (see https://github.com/paritytech/grandpa-bridge-gadget).
//!	MMR root hashes along with BEEFY will make it possible to build Super Light Clients of
//!	Substrate-based chains. The SLC will be able to follow finality and can be shown proves of more
//!	details that happened on the source chain.
//!	In that case the chain which contains the pallet generates the Root Hashes and Proofs, which
//!	are then presented to another chain acting as a light client which can verify them.
//!
//!	Secondary use case is to archive historical data, but still be able to retrieve them on-demand
//!	if needed. For instance if parent block hashes are stored in the MMR it's possible at any point
//!	in time to provide a MMR proof about some past block hash, while this data can be safely pruned
//!	from on-chain storage.
//!
//! NOTE This pallet is experimental and not proven to work in production.
//!
#![cfg_attr(not(feature = "std"), no_std)]

use codec::Encode;
use frame_support::{
	decl_module, decl_storage,
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
	/// Prefix for elements stored in the Off-chain DB via Indexing API.
	///
	/// Each node of the MMR is inserted both on-chain and off-chain via Indexing API.
	/// The former does not store full leaf content, just it's compact version (hash),
	/// and some of the inner mmr nodes might be pruned from on-chain storage.
	/// The later will contain all the entries in their full form.
	///
	/// Each node is stored in the Off-chain DB under key derived from the [INDEXING_PREFIX] and
	/// it's in-tree index (MMR position).
	const INDEXING_PREFIX: &'static [u8];

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

	/// The cost of hashing a concatentation of two [Self::Hash] elements.
	type HashWeight: Get<Weight>;

	/// Data stored in the leaf nodes.
	///
	/// The [LeafData](primitives::LeafDataProvider) is responsible for returning the entire leaf
	/// data that will be inserted to the MMR.
	/// [LeafDataProvider](primitives::LeafDataProvider)s can be composed into tuples to put
	/// multiple elements into the tree. In such case it might be worth using [primitives::Compact]
	/// to make MMR proof for one element of the tuple leaner.
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
	}
}

decl_module! {
	/// A public part of the pallet.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn on_initialize(n: T::BlockNumber) -> Weight {
			use primitives::LeafDataProvider;
			let leaves = Self::mmr_leaves();
			let peaks_before = mmr::utils::NodesUtils::new(leaves).number_of_peaks();
			let (data, leaf_weight) = T::LeafData::leaf_data();
			// append new leaf to MMR
			let mut mmr: ModuleMMR<mmr::storage::RuntimeStorage, T> = mmr::MMR::new(leaves);
			mmr.push(data).expect("MMR push never fails.");

			// update the size
			let (leaves, root) = mmr.finalize().expect("MMR finalize never fails.");
			<NumberOfLeaves>::put(leaves);
			<RootHash<T>>::put(root);

			let peaks_after = mmr::utils::NodesUtils::new(leaves).number_of_peaks();
			let hash_weight = peaks_after.saturating_mul(T::HashWeight::get());

			leaf_weight
				.saturating_add(hash_weight)
				.saturating_add(<T as frame_system::Trait>::DbWeight::get().reads_writes(
					2 + peaks_before,
					2 + peaks_after,
				))
		}
	}
}

/// A MMR specific to the pallet.
type ModuleMMR<StorageType, T> = mmr::MMR<StorageType, T, LeafOf<T>>;

/// Leaf data.
type LeafOf<T> = <<T as Trait>::LeafData as primitives::LeafDataProvider>::LeafData;

/// Hashing used for the pallet.
pub(crate) type HashingOf<T> = <T as crate::Trait>::Hashing;

impl<T: Trait> Module<T> {
	fn offchain_key(pos: u64) -> Vec<u8> {
		(T::INDEXING_PREFIX, pos).encode()
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
			|| proof.items.len() as u32 > mmr::utils::NodesUtils::new(proof.leaf_count).depth()
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
