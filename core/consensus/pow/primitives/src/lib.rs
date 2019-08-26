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

//! Primitives for Substrate PoW consensus.

#![cfg_attr(not(feature = "std"), no_std)]

use substrate_client::decl_runtime_apis;
use rstd::vec::Vec;
use sr_primitives::ConsensusEngineId;
use primitives::H256;

/// The `ConsensusEngineId` of PoW.
pub const POW_ENGINE_ID: ConsensusEngineId = [b'p', b'o', b'w', b'_'];

/// Type of difficulty.
pub type Difficulty = u128;

/// Type of seal.
pub type Seal = Vec<u8>;

decl_runtime_apis! {
	/// API necessary for block authorship with Proof of Work.
	pub trait PowApi {
		/// Verify a given proof of work against the current difficulty.
		/// Note that `pre_hash` is always a hash of a direct child.
		///
		/// Returns the current difficulty if the seal is valid. Otherwise
		/// returns `None`.
		fn verify(pre_hash: &H256, seal: &Seal) -> Option<Difficulty>;

		/// Mine a seal that satisfy the current difficulty.
		fn mine(pre_hash: &H256, seed: &H256, round: u32) -> Option<(Difficulty, Seal)>;
	}
}
