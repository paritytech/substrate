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

//! Primitives for Substrate Proof-of-Work (PoW) consensus.

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::vec::Vec;
use sr_primitives::ConsensusEngineId;

/// The `ConsensusEngineId` of PoW.
pub const POW_ENGINE_ID: ConsensusEngineId = [b'p', b'o', b'w', b'_'];

/// Type of difficulty.
///
/// For runtime designed for Substrate, it's always possible to fit its total
/// difficulty range under `u128::max_value()` because it can be freely scaled
/// up or scaled down. Very few PoW chains use difficulty values
/// larger than `u128::max_value()`.
pub type Difficulty = u128;

/// Type of seal.
pub type Seal = Vec<u8>;
