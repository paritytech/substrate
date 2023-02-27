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

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! A BEEFY+MMR pallet combo.
//!
//! While both BEEFY and Merkle Mountain Range (MMR) can be used separately,
//! these tools were designed to work together in unison.
//!
//! The pallet provides a standardized MMR Leaf format that can be used
//! to bridge BEEFY+MMR-based networks (both standalone and Polkadot-like).
//!
//! The MMR leaf contains:
//! 1. Block number and parent block hash.
//! 2. Merkle Tree Root Hash of next BEEFY validator set.
//! 3. Arbitrary extra leaf data to be used by downstream pallets to include custom data.
//!
//! and thanks to versioning can be easily updated in the future.

use sp_runtime::traits::{Convert, Member};
use sp_std::prelude::*;

use beefy_primitives::{
	mmr::{BeefyAuthoritySet, BeefyDataProvider, BeefyNextAuthoritySet, MmrLeaf, MmrLeafVersion},
	ValidatorSet as BeefyValidatorSet,
};
use pallet_mmr::{LeafDataProvider, ParentNumberAndHash};

use frame_support::{crypto::ecdsa::ECDSAExt, traits::Get};

pub use pallet::*;

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

/// A BEEFY consensus digest item with MMR root hash.
pub struct DepositBeefyDigest<T>(sp_std::marker::PhantomData<T>);

impl<T> pallet_mmr::primitives::OnNewRoot<beefy_primitives::MmrRootHash> for DepositBeefyDigest<T>
where
	T: pallet_mmr::Config<Hash = beefy_primitives::MmrRootHash>,
	T: pallet_beefy::Config,
{
	fn on_new_root(root: &<T as pallet_mmr::Config>::Hash) {
		let digest = sp_runtime::generic::DigestItem::Consensus(
			beefy_primitives::BEEFY_ENGINE_ID,
			codec::Encode::encode(&beefy_primitives::ConsensusLog::<
				<T as pallet_beefy::Config>::BeefyId,
			>::MmrRoot(*root)),
		);
		<frame_system::Pallet<T>>::deposit_log(digest);
	}
}

/// Convert BEEFY secp256k1 public keys into Ethereum addresses
pub struct BeefyEcdsaToEthereum;
impl Convert<beefy_primitives::crypto::AuthorityId, Vec<u8>> for BeefyEcdsaToEthereum {
	fn convert(beefy_id: beefy_primitives::crypto::AuthorityId) -> Vec<u8> {
		sp_core::ecdsa::Public::from(beefy_id)
			.to_eth_address()
			.map(|v| v.to_vec())
			.map_err(|_| {
				log::error!(target: "runtime::beefy", "Failed to convert BEEFY PublicKey to ETH address!");
			})
			.unwrap_or_default()
	}
}

type MerkleRootOf<T> = <T as pallet_mmr::Config>::Hash;

#[frame_support::pallet]
pub mod pallet {
	#![allow(missing_docs)]

	use super::*;
	use frame_support::pallet_prelude::*;

	/// BEEFY-MMR pallet.
	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	/// The module's configuration trait.
	#[pallet::config]
	#[pallet::disable_frame_system_supertrait_check]
	pub trait Config: pallet_mmr::Config + pallet_beefy::Config {
		/// Current leaf version.
		///
		/// Specifies the version number added to every leaf that get's appended to the MMR.
		/// Read more in [`MmrLeafVersion`] docs about versioning leaves.
		type LeafVersion: Get<MmrLeafVersion>;

		/// Convert BEEFY AuthorityId to a form that would end up in the Merkle Tree.
		///
		/// For instance for ECDSA (secp256k1) we want to store uncompressed public keys (65 bytes)
		/// and later to Ethereum Addresses (160 bits) to simplify using them on Ethereum chain,
		/// but the rest of the Substrate codebase is storing them compressed (33 bytes) for
		/// efficiency reasons.
		type BeefyAuthorityToMerkleLeaf: Convert<<Self as pallet_beefy::Config>::BeefyId, Vec<u8>>;

		/// The type expected for the leaf extra data
		type LeafExtra: Member + codec::FullCodec;

		/// Retrieve arbitrary data that should be added to the mmr leaf
		type BeefyDataProvider: BeefyDataProvider<Self::LeafExtra>;
	}

	/// Details of current BEEFY authority set.
	#[pallet::storage]
	#[pallet::getter(fn beefy_authorities)]
	pub type BeefyAuthorities<T: Config> =
		StorageValue<_, BeefyAuthoritySet<MerkleRootOf<T>>, ValueQuery>;

	/// Details of next BEEFY authority set.
	///
	/// This storage entry is used as cache for calls to `update_beefy_next_authority_set`.
	#[pallet::storage]
	#[pallet::getter(fn beefy_next_authorities)]
	pub type BeefyNextAuthorities<T: Config> =
		StorageValue<_, BeefyNextAuthoritySet<MerkleRootOf<T>>, ValueQuery>;
}

impl<T: Config> LeafDataProvider for Pallet<T> {
	type LeafData = MmrLeaf<
		<T as frame_system::Config>::BlockNumber,
		<T as frame_system::Config>::Hash,
		MerkleRootOf<T>,
		T::LeafExtra,
	>;

	fn leaf_data() -> Self::LeafData {
		MmrLeaf {
			version: T::LeafVersion::get(),
			parent_number_and_hash: ParentNumberAndHash::<T>::leaf_data(),
			leaf_extra: T::BeefyDataProvider::extra_data(),
			beefy_next_authority_set: Pallet::<T>::beefy_next_authorities(),
		}
	}
}

impl<T> beefy_primitives::OnNewValidatorSet<<T as pallet_beefy::Config>::BeefyId> for Pallet<T>
where
	T: pallet::Config,
{
	/// Compute and cache BEEFY authority sets based on updated BEEFY validator sets.
	fn on_new_validator_set(
		current_set: &BeefyValidatorSet<<T as pallet_beefy::Config>::BeefyId>,
		next_set: &BeefyValidatorSet<<T as pallet_beefy::Config>::BeefyId>,
	) {
		let current = Pallet::<T>::compute_authority_set(current_set);
		let next = Pallet::<T>::compute_authority_set(next_set);
		// cache the result
		BeefyAuthorities::<T>::put(&current);
		BeefyNextAuthorities::<T>::put(&next);
	}
}

impl<T: Config> Pallet<T> {
	/// Return the currently active BEEFY authority set proof.
	pub fn authority_set_proof() -> BeefyAuthoritySet<MerkleRootOf<T>> {
		Pallet::<T>::beefy_authorities()
	}

	/// Return the next/queued BEEFY authority set proof.
	pub fn next_authority_set_proof() -> BeefyNextAuthoritySet<MerkleRootOf<T>> {
		Pallet::<T>::beefy_next_authorities()
	}

	/// Returns details of a BEEFY authority set.
	///
	/// Details contain authority set id, authority set length and a merkle root,
	/// constructed from uncompressed secp256k1 public keys converted to Ethereum addresses
	/// of the next BEEFY authority set.
	fn compute_authority_set(
		validator_set: &BeefyValidatorSet<<T as pallet_beefy::Config>::BeefyId>,
	) -> BeefyAuthoritySet<MerkleRootOf<T>> {
		let id = validator_set.id();
		let beefy_addresses = validator_set
			.validators()
			.into_iter()
			.cloned()
			.map(T::BeefyAuthorityToMerkleLeaf::convert)
			.collect::<Vec<_>>();
		let len = beefy_addresses.len() as u32;
		let root = binary_merkle_tree::merkle_root::<<T as pallet_mmr::Config>::Hashing, _>(
			beefy_addresses,
		)
		.into();
		BeefyAuthoritySet { id, len, root }
	}
}

sp_api::decl_runtime_apis! {
	/// API useful for BEEFY light clients.
	pub trait BeefyMmrApi<H>
	where
		BeefyAuthoritySet<H>: sp_api::Decode,
	{
		/// Return the currently active BEEFY authority set proof.
		fn authority_set_proof() -> BeefyAuthoritySet<H>;

		/// Return the next/queued BEEFY authority set proof.
		fn next_authority_set_proof() -> BeefyNextAuthoritySet<H>;
	}
}
