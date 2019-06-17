// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Primitives for Aura.

#![cfg_attr(not(feature = "std"), no_std)]

use parity_codec::{Encode, Decode, Codec};
use substrate_client::decl_runtime_apis;
use rstd::vec::Vec;
use runtime_primitives::ConsensusEngineId;

mod digest;
pub use digest::{CompatibleDigestItem, find_pre_digest};

/// The `ConsensusEngineId` of AuRa.
pub const AURA_ENGINE_ID: ConsensusEngineId = [b'a', b'u', b'r', b'a'];

/// An consensus log item for Aura.
#[derive(Decode, Encode)]
pub enum ConsensusLog<AuthorityId: Codec> {
	/// The authorities have changed.
	AuthoritiesChange(Vec<AuthorityId>),
}

decl_runtime_apis! {
	/// API necessary for block authorship with aura.
	pub trait AuraApi<AuthorityId: Codec> {
		/// Return the slot duration in seconds for Aura.
		/// Currently, only the value provided by this type at genesis
		/// will be used.
		///
		/// Dynamic slot duration may be supported in the future.
		fn slot_duration() -> u64;

		// Return the current set of authorities.
		fn authorities() -> Vec<AuthorityId>;
	}
}


/// Get slot author for given block along with authorities.
pub fn slot_author<AuthorityId>(slot_num: u64, authorities: &[AuthorityId]) -> Option<&AuthorityId>
{
	if authorities.is_empty() { return None }

	let idx = slot_num % (authorities.len() as u64);
	assert!(idx <= usize::max_value() as u64,
		"It is impossible to have a vector with length beyond the address space; qed");

	let current_author = authorities.get(idx as usize)
		.expect("authorities not empty; index constrained to list length;\
				this is a valid index; qed");

	Some(current_author)
}
