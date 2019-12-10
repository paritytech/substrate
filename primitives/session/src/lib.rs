// Copyright 2019 Parity Technologies (UK) Ltd.
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
use sp_runtime::KeyTypeId;
use sp_staking::SessionIndex;
use sp_std::vec::Vec;

#[cfg(feature = "std")]
use sp_runtime::{generic::BlockId, traits::{ProvideRuntimeApi, Block as BlockT}};

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
	}

	/// Historical session membership runtime api.
	pub trait SessionMembership {
		/// Generates a proof that the given session key is a part of the
		/// current session. The generated proof can later on be validated with
		/// the historical session module. Proofs of membership are useful e.g.
		/// for validating misbehavior reports.
		fn generate_session_membership_proof(
			session_key: (KeyTypeId, Vec<u8>),
		) -> Option<MembershipProof>;
	}
}

/// Proof of membership of a specific key in a given session.
#[derive(Encode, Decode, Clone, PartialEq, Eq, Default, Debug)]
pub struct MembershipProof {
	/// The session index on which the specific key is a member.
	pub session: SessionIndex,
	/// Trie nodes of a merkle proof of session membership.
	pub trie_nodes: Vec<Vec<u8>>,
}

/// Generate the initial session keys with the given seeds, at the given block and store them in
/// the client's keystore.
#[cfg(feature = "std")]
pub fn generate_initial_session_keys<Block, T>(
	client: std::sync::Arc<T>,
	at: &BlockId<Block>,
	seeds: Vec<String>,
) -> Result<(), <<T as ProvideRuntimeApi>::Api as sp_api::ApiExt<Block>>::Error>
where
	Block: BlockT,
	T: ProvideRuntimeApi,
	<T as ProvideRuntimeApi>::Api: SessionKeys<Block>,
{
	let runtime_api = client.runtime_api();

	for seed in seeds {
		runtime_api.generate_session_keys(at, Some(seed.as_bytes().to_vec()))?;
	}

	Ok(())
}
