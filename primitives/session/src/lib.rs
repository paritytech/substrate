// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Substrate core types around sessions.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Encode, Decode};

#[cfg(feature = "std")]
use sp_runtime::{generic::BlockId, traits::Block as BlockT};
#[cfg(feature = "std")]
use sp_api::ProvideRuntimeApi;

use sp_core::RuntimeDebug;
use sp_core::crypto::KeyTypeId;
use sp_staking::SessionIndex;
use sp_std::vec::Vec;

sp_api::decl_runtime_apis! {
	/// Session keys runtime api.
	pub trait SessionKeys {
		/// Generate a set of session keys with optionally using the given seed.
		/// The keys should be stored within the keystore exposed via runtime
		/// externalities.
		///
		/// The seed needs to be a valid `utf8` string.
		///
		/// Returns the concatenated SCALE encoded public keys.
		fn generate_session_keys(seed: Option<Vec<u8>>) -> Vec<u8>;

		/// Decode the given public session keys.
		///
		/// Returns the list of public raw public keys + key type.
		fn decode_session_keys(encoded: Vec<u8>) -> Option<Vec<(Vec<u8>, KeyTypeId)>>;
	}
}

/// Number of validators in a given session.
pub type ValidatorCount = u32;

/// Proof of membership of a specific key in a given session.
#[derive(Encode, Decode, Clone, Eq, PartialEq, Default, RuntimeDebug)]
pub struct MembershipProof {
	/// The session index on which the specific key is a member.
	pub session: SessionIndex,
	/// Trie nodes of a merkle proof of session membership.
	pub trie_nodes: Vec<Vec<u8>>,
	/// The validator count of the session on which the specific key is a member.
	pub validator_count: ValidatorCount,
}

/// Generate the initial session keys with the given seeds, at the given block and store them in
/// the client's keystore.
#[cfg(feature = "std")]
pub fn generate_initial_session_keys<Block, T>(
	client: std::sync::Arc<T>,
	at: &BlockId<Block>,
	seeds: Vec<String>,
) -> Result<(), sp_api::ApiErrorFor<T, Block>>
where
	Block: BlockT,
	T: ProvideRuntimeApi<Block>,
	T::Api: SessionKeys<Block>,
{
	let runtime_api = client.runtime_api();

	for seed in seeds {
		runtime_api.generate_session_keys(at, Some(seed.as_bytes().to_vec()))?;
	}

	Ok(())
}
