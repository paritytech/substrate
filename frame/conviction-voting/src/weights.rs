// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

//! Autogenerated weights for pallet_conviction_voting
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-01-24, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `bm2`, CPU: `Intel(R) Core(TM) i7-7700K CPU @ 4.20GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_conviction_voting
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/conviction-voting/src/weights.rs
// --header=./HEADER-APACHE2
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_conviction_voting.
pub trait WeightInfo {
	fn vote_new() -> Weight;
	fn vote_existing() -> Weight;
	fn remove_vote() -> Weight;
	fn remove_other_vote() -> Weight;
	fn delegate(r: u32, ) -> Weight;
	fn undelegate(r: u32, ) -> Weight;
	fn unlock() -> Weight;
}

/// Weights for pallet_conviction_voting using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: Referenda ReferendumInfoFor (r:1 w:1)
	/// Proof: Referenda ReferendumInfoFor (max_values: None, max_size: Some(366), added: 2841, mode: MaxEncodedLen)
	/// Storage: ConvictionVoting VotingFor (r:1 w:1)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: ConvictionVoting ClassLocksFor (r:1 w:1)
	/// Proof: ConvictionVoting ClassLocksFor (max_values: None, max_size: Some(59), added: 2534, mode: MaxEncodedLen)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:2 w:2)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	fn vote_new() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `13168`
		//  Estimated: `257859`
		// Minimum execution time: 85_569 nanoseconds.
		Weight::from_parts(86_492_000, 257859)
			.saturating_add(T::DbWeight::get().reads(6_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
	}
	/// Storage: Referenda ReferendumInfoFor (r:1 w:1)
	/// Proof: Referenda ReferendumInfoFor (max_values: None, max_size: Some(366), added: 2841, mode: MaxEncodedLen)
	/// Storage: ConvictionVoting VotingFor (r:1 w:1)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: ConvictionVoting ClassLocksFor (r:1 w:1)
	/// Proof: ConvictionVoting ClassLocksFor (max_values: None, max_size: Some(59), added: 2534, mode: MaxEncodedLen)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:2 w:2)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	fn vote_existing() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `20342`
		//  Estimated: `257859`
		// Minimum execution time: 212_727 nanoseconds.
		Weight::from_parts(213_741_000, 257859)
			.saturating_add(T::DbWeight::get().reads(6_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
	}
	/// Storage: ConvictionVoting VotingFor (r:1 w:1)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: Referenda ReferendumInfoFor (r:1 w:1)
	/// Proof: Referenda ReferendumInfoFor (max_values: None, max_size: Some(366), added: 2841, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:2 w:2)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	fn remove_vote() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `20062`
		//  Estimated: `251551`
		// Minimum execution time: 200_513 nanoseconds.
		Weight::from_parts(201_589_000, 251551)
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().writes(4_u64))
	}
	/// Storage: ConvictionVoting VotingFor (r:1 w:1)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: Referenda ReferendumInfoFor (r:1 w:0)
	/// Proof: Referenda ReferendumInfoFor (max_values: None, max_size: Some(366), added: 2841, mode: MaxEncodedLen)
	fn remove_other_vote() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `12738`
		//  Estimated: `32557`
		// Minimum execution time: 43_083 nanoseconds.
		Weight::from_parts(43_763_000, 32557)
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: ConvictionVoting VotingFor (r:2 w:2)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: Referenda ReferendumInfoFor (r:1 w:1)
	/// Proof: Referenda ReferendumInfoFor (max_values: None, max_size: Some(366), added: 2841, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:2 w:2)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// Storage: ConvictionVoting ClassLocksFor (r:1 w:1)
	/// Proof: ConvictionVoting ClassLocksFor (max_values: None, max_size: Some(59), added: 2534, mode: MaxEncodedLen)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// The range of component `r` is `[0, 1]`.
	fn delegate(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `272 + r * (1689 ±0)`
		//  Estimated: `176657 + r * (110917 ±0)`
		// Minimum execution time: 33_246 nanoseconds.
		Weight::from_parts(34_560_391, 176657)
			// Standard Error: 63_925
			.saturating_add(Weight::from_ref_time(34_500_408).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().reads((3_u64).saturating_mul(r.into())))
			.saturating_add(T::DbWeight::get().writes(4_u64))
			.saturating_add(T::DbWeight::get().writes((3_u64).saturating_mul(r.into())))
			.saturating_add(Weight::from_proof_size(110917).saturating_mul(r.into()))
	}
	/// Storage: ConvictionVoting VotingFor (r:2 w:2)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: Referenda ReferendumInfoFor (r:1 w:1)
	/// Proof: Referenda ReferendumInfoFor (max_values: None, max_size: Some(366), added: 2841, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:2 w:2)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// The range of component `r` is `[0, 1]`.
	fn undelegate(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `470 + r * (1407 ±0)`
		//  Estimated: `170349 + r * (110917 ±0)`
		// Minimum execution time: 20_508 nanoseconds.
		Weight::from_parts(21_240_024, 170349)
			// Standard Error: 37_314
			.saturating_add(Weight::from_ref_time(30_890_875).saturating_mul(r.into()))
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().reads((3_u64).saturating_mul(r.into())))
			.saturating_add(T::DbWeight::get().writes(2_u64))
			.saturating_add(T::DbWeight::get().writes((3_u64).saturating_mul(r.into())))
			.saturating_add(Weight::from_proof_size(110917).saturating_mul(r.into()))
	}
	/// Storage: ConvictionVoting VotingFor (r:1 w:1)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: ConvictionVoting ClassLocksFor (r:1 w:1)
	/// Proof: ConvictionVoting ClassLocksFor (max_values: None, max_size: Some(59), added: 2534, mode: MaxEncodedLen)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	fn unlock() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `11797`
		//  Estimated: `36024`
		// Minimum execution time: 50_305 nanoseconds.
		Weight::from_parts(51_226_000, 36024)
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// Storage: Referenda ReferendumInfoFor (r:1 w:1)
	/// Proof: Referenda ReferendumInfoFor (max_values: None, max_size: Some(366), added: 2841, mode: MaxEncodedLen)
	/// Storage: ConvictionVoting VotingFor (r:1 w:1)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: ConvictionVoting ClassLocksFor (r:1 w:1)
	/// Proof: ConvictionVoting ClassLocksFor (max_values: None, max_size: Some(59), added: 2534, mode: MaxEncodedLen)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:2 w:2)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	fn vote_new() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `13168`
		//  Estimated: `257859`
		// Minimum execution time: 85_569 nanoseconds.
		Weight::from_parts(86_492_000, 257859)
			.saturating_add(RocksDbWeight::get().reads(6_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: Referenda ReferendumInfoFor (r:1 w:1)
	/// Proof: Referenda ReferendumInfoFor (max_values: None, max_size: Some(366), added: 2841, mode: MaxEncodedLen)
	/// Storage: ConvictionVoting VotingFor (r:1 w:1)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: ConvictionVoting ClassLocksFor (r:1 w:1)
	/// Proof: ConvictionVoting ClassLocksFor (max_values: None, max_size: Some(59), added: 2534, mode: MaxEncodedLen)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:2 w:2)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	fn vote_existing() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `20342`
		//  Estimated: `257859`
		// Minimum execution time: 212_727 nanoseconds.
		Weight::from_parts(213_741_000, 257859)
			.saturating_add(RocksDbWeight::get().reads(6_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: ConvictionVoting VotingFor (r:1 w:1)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: Referenda ReferendumInfoFor (r:1 w:1)
	/// Proof: Referenda ReferendumInfoFor (max_values: None, max_size: Some(366), added: 2841, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:2 w:2)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	fn remove_vote() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `20062`
		//  Estimated: `251551`
		// Minimum execution time: 200_513 nanoseconds.
		Weight::from_parts(201_589_000, 251551)
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().writes(4_u64))
	}
	/// Storage: ConvictionVoting VotingFor (r:1 w:1)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: Referenda ReferendumInfoFor (r:1 w:0)
	/// Proof: Referenda ReferendumInfoFor (max_values: None, max_size: Some(366), added: 2841, mode: MaxEncodedLen)
	fn remove_other_vote() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `12738`
		//  Estimated: `32557`
		// Minimum execution time: 43_083 nanoseconds.
		Weight::from_parts(43_763_000, 32557)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: ConvictionVoting VotingFor (r:2 w:2)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: Referenda ReferendumInfoFor (r:1 w:1)
	/// Proof: Referenda ReferendumInfoFor (max_values: None, max_size: Some(366), added: 2841, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:2 w:2)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// Storage: ConvictionVoting ClassLocksFor (r:1 w:1)
	/// Proof: ConvictionVoting ClassLocksFor (max_values: None, max_size: Some(59), added: 2534, mode: MaxEncodedLen)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// The range of component `r` is `[0, 1]`.
	fn delegate(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `272 + r * (1689 ±0)`
		//  Estimated: `176657 + r * (110917 ±0)`
		// Minimum execution time: 33_246 nanoseconds.
		Weight::from_parts(34_560_391, 176657)
			// Standard Error: 63_925
			.saturating_add(Weight::from_ref_time(34_500_408).saturating_mul(r.into()))
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().reads((3_u64).saturating_mul(r.into())))
			.saturating_add(RocksDbWeight::get().writes(4_u64))
			.saturating_add(RocksDbWeight::get().writes((3_u64).saturating_mul(r.into())))
			.saturating_add(Weight::from_proof_size(110917).saturating_mul(r.into()))
	}
	/// Storage: ConvictionVoting VotingFor (r:2 w:2)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: Referenda ReferendumInfoFor (r:1 w:1)
	/// Proof: Referenda ReferendumInfoFor (max_values: None, max_size: Some(366), added: 2841, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:2 w:2)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// The range of component `r` is `[0, 1]`.
	fn undelegate(r: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `470 + r * (1407 ±0)`
		//  Estimated: `170349 + r * (110917 ±0)`
		// Minimum execution time: 20_508 nanoseconds.
		Weight::from_parts(21_240_024, 170349)
			// Standard Error: 37_314
			.saturating_add(Weight::from_ref_time(30_890_875).saturating_mul(r.into()))
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().reads((3_u64).saturating_mul(r.into())))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
			.saturating_add(RocksDbWeight::get().writes((3_u64).saturating_mul(r.into())))
			.saturating_add(Weight::from_proof_size(110917).saturating_mul(r.into()))
	}
	/// Storage: ConvictionVoting VotingFor (r:1 w:1)
	/// Proof: ConvictionVoting VotingFor (max_values: None, max_size: Some(27241), added: 29716, mode: MaxEncodedLen)
	/// Storage: ConvictionVoting ClassLocksFor (r:1 w:1)
	/// Proof: ConvictionVoting ClassLocksFor (max_values: None, max_size: Some(59), added: 2534, mode: MaxEncodedLen)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	fn unlock() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `11797`
		//  Estimated: `36024`
		// Minimum execution time: 50_305 nanoseconds.
		Weight::from_parts(51_226_000, 36024)
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
}
