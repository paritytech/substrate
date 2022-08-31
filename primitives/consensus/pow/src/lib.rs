// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Primitives for Substrate Proof-of-Work (PoW) consensus.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::vec::Vec;
use sp_runtime::ConsensusEngineId;
use codec::Decode;

/// The `ConsensusEngineId` of PoW.
pub const POW_ENGINE_ID: ConsensusEngineId = [b'p', b'o', b'w', b'_'];

/// Type of seal.
pub type Seal = Vec<u8>;

/// Define methods that total difficulty should implement.
pub trait TotalDifficulty {
	fn increment(&mut self, other: Self);
}

impl TotalDifficulty for sp_core::U256 {
	fn increment(&mut self, other: Self) {
		let ret = self.saturating_add(other);
		*self = ret;
	}
}

impl TotalDifficulty for u128 {
	fn increment(&mut self, other: Self) {
		let ret = self.saturating_add(other);
		*self = ret;
	}
}

sp_api::decl_runtime_apis! {
	/// API necessary for timestamp-based difficulty adjustment algorithms.
	pub trait TimestampApi<Moment: Decode> {
		/// Return the timestamp in the current block.
		fn timestamp() -> Moment;
	}

	/// API for those chains that put their difficulty adjustment algorithm directly
	/// onto runtime. Note that while putting difficulty adjustment algorithm to
	/// runtime is safe, putting the PoW algorithm on runtime is not.
	pub trait DifficultyApi<Difficulty: Decode> {
		/// Return the target difficulty of the next block.
		fn difficulty() -> Difficulty;
	}
}
