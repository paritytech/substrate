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
///
/// For runtime designed for Substrate, it's always possible to fit its total
/// difficulty range under `u128::max_value()` because it can be freely scaled
/// up or scaled down. Practially, nearly no PoW chains uses difficulty values
/// larger than `u128::max_value()`.
pub type Difficulty = u128;

/// Type of seal.
pub type Seal = Vec<u8>;

decl_runtime_apis! {
	/// API necessary for block authorship with Proof of Work.
	///
	/// This API allows online upgrades of PoW algorithms as well as the difficulty
	/// adjustment algorithm. Note that we always validate difficulty and seals
	/// against the parent block. This means that in the case of code upgrade, the
	/// first block that upgraded the code will still use the old algorithm. The block
	/// after that will switch to the new algorithm.
	///
	/// All functions here should not modify block state. Instead, state modifications
	/// related to PoW should use `on_initialize` and `on_finalize` routine.
	pub trait PowApi {
		/// Return the difficulty that should be applied for the next block.
		fn difficulty() -> Difficulty;

		/// Verify a given proof of work against the given difficulty.
		/// Note that `pre_hash` is always a hash of a direct child.
		fn verify(
			pre_hash: &H256,
			seal: &Seal,
			difficulty: Difficulty
		) -> bool;

		/// Mine a seal that satisfy the given difficulty.
		fn mine(
			pre_hash: &H256,
			seed: &H256,
			difficulty: Difficulty,
			round: u32
		) -> Option<Seal>;
	}
}
