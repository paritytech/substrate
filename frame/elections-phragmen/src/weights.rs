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

//! Autogenerated weights for pallet_elections_phragmen
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-02-03, STEPS: `10`, REPEAT: `10`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `Kians-MacBook-Pro-2.local`, CPU: `<UNKNOWN>`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// target/debug/substrate
// benchmark
// pallet
// --steps=10
// --repeat=10
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --pallet=pallet_elections_phragmen
// --chain=dev
// --header=./HEADER-APACHE2
// --output=./frame/elections-phragmen/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_elections_phragmen.
pub trait WeightInfo {
	fn vote_equal(v: u32, ) -> Weight;
	fn vote_more(v: u32, ) -> Weight;
	fn vote_less(v: u32, ) -> Weight;
	fn remove_voter() -> Weight;
	fn submit_candidacy(c: u32, ) -> Weight;
	fn renounce_candidacy_candidate(c: u32, ) -> Weight;
	fn renounce_candidacy_members() -> Weight;
	fn renounce_candidacy_runners_up() -> Weight;
	fn remove_member_without_replacement() -> Weight;
	fn remove_member_with_replacement() -> Weight;
	fn clean_defunct_voters(v: u32, d: u32, ) -> Weight;
	fn election_phragmen(c: u32, v: u32, e: u32, ) -> Weight;
}

/// Weights for pallet_elections_phragmen using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: Elections Candidates (r:1 w:0)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Members (r:1 w:0)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:0)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Voting (r:1 w:1)
	/// Proof Skipped: Elections Voting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// The range of component `v` is `[1, 16]`.
	fn vote_equal(v: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `499 + v * (80 ±0)`
		//  Estimated: `9726 + v * (320 ±0)`
		// Minimum execution time: 415_000 nanoseconds.
		Weight::from_parts(421_838_802, 9726)
			// Standard Error: 133_238
			.saturating_add(Weight::from_ref_time(326_568).saturating_mul(v.into()))
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
			.saturating_add(Weight::from_proof_size(320).saturating_mul(v.into()))
	}
	/// Storage: Elections Candidates (r:1 w:0)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Members (r:1 w:0)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:0)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Voting (r:1 w:1)
	/// Proof Skipped: Elections Voting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// The range of component `v` is `[2, 16]`.
	fn vote_more(v: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `467 + v * (80 ±0)`
		//  Estimated: `9598 + v * (320 ±0)`
		// Minimum execution time: 558_000 nanoseconds.
		Weight::from_parts(556_163_102, 9598)
			// Standard Error: 738_644
			.saturating_add(Weight::from_ref_time(3_391_887).saturating_mul(v.into()))
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
			.saturating_add(Weight::from_proof_size(320).saturating_mul(v.into()))
	}
	/// Storage: Elections Candidates (r:1 w:0)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Members (r:1 w:0)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:0)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Voting (r:1 w:1)
	/// Proof Skipped: Elections Voting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// The range of component `v` is `[2, 16]`.
	fn vote_less(v: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `499 + v * (80 ±0)`
		//  Estimated: `9726 + v * (320 ±0)`
		// Minimum execution time: 568_000 nanoseconds.
		Weight::from_parts(621_939_239, 9726)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
			.saturating_add(Weight::from_proof_size(320).saturating_mul(v.into()))
	}
	/// Storage: Elections Voting (r:1 w:1)
	/// Proof Skipped: Elections Voting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	fn remove_voter() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `989`
		//  Estimated: `7238`
		// Minimum execution time: 504_000 nanoseconds.
		Weight::from_parts(512_000_000, 7238)
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: Elections Candidates (r:1 w:1)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Members (r:1 w:0)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:0)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `c` is `[1, 1000]`.
	fn submit_candidacy(c: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1690 + c * (48 ±0)`
		//  Estimated: `6540 + c * (144 ±0)`
		// Minimum execution time: 368_000 nanoseconds.
		Weight::from_parts(406_083_483, 6540)
			// Standard Error: 11_995
			.saturating_add(Weight::from_ref_time(161_971).saturating_mul(c.into()))
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
			.saturating_add(Weight::from_proof_size(144).saturating_mul(c.into()))
	}
	/// Storage: Elections Candidates (r:1 w:1)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `c` is `[1, 1000]`.
	fn renounce_candidacy_candidate(c: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `347 + c * (48 ±0)`
		//  Estimated: `825 + c * (48 ±0)`
		// Minimum execution time: 332_000 nanoseconds.
		Weight::from_parts(374_734_634, 825)
			// Standard Error: 10_531
			.saturating_add(Weight::from_ref_time(35_062).saturating_mul(c.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
			.saturating_add(Weight::from_proof_size(48).saturating_mul(c.into()))
	}
	/// Storage: Elections Members (r:1 w:1)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:1)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Prime (r:1 w:1)
	/// Proof Skipped: Council Prime (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Proposals (r:1 w:0)
	/// Proof Skipped: Council Proposals (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Members (r:0 w:1)
	/// Proof Skipped: Council Members (max_values: Some(1), max_size: None, mode: Measured)
	fn renounce_candidacy_members() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `2027`
		//  Estimated: `12115`
		// Minimum execution time: 521_000 nanoseconds.
		Weight::from_parts(531_000_000, 12115)
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().writes(4_u64))
	}
	/// Storage: Elections RunnersUp (r:1 w:1)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	fn renounce_candidacy_runners_up() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `975`
		//  Estimated: `1470`
		// Minimum execution time: 345_000 nanoseconds.
		Weight::from_parts(381_000_000, 1470)
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Benchmark Override (r:0 w:0)
	/// Proof Skipped: Benchmark Override (max_values: None, max_size: None, mode: Measured)
	fn remove_member_without_replacement() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_000_000_000 nanoseconds.
		Weight::from_ref_time(2_000_000_000_000)
	}
	/// Storage: Elections Members (r:1 w:1)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Elections RunnersUp (r:1 w:1)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Prime (r:1 w:1)
	/// Proof Skipped: Council Prime (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Proposals (r:1 w:0)
	/// Proof Skipped: Council Proposals (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Members (r:0 w:1)
	/// Proof Skipped: Council Members (max_values: Some(1), max_size: None, mode: Measured)
	fn remove_member_with_replacement() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `2027`
		//  Estimated: `14718`
		// Minimum execution time: 601_000 nanoseconds.
		Weight::from_parts(610_000_000, 14718)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(5_u64))
	}
	/// Storage: Elections Voting (r:10001 w:10000)
	/// Proof Skipped: Elections Voting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Elections Members (r:1 w:0)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:0)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Candidates (r:1 w:0)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Balances Locks (r:10000 w:10000)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// Storage: System Account (r:10000 w:10000)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `v` is `[5000, 10000]`.
	/// The range of component `d` is `[0, 5000]`.
	fn clean_defunct_voters(v: u32, _d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `36373 + v * (872 ±0)`
		//  Estimated: `32033948 + v * (9658 ±0)`
		// Minimum execution time: 5_401_340_000 nanoseconds.
		Weight::from_parts(5_410_097_000_000, 32033948)
			// Standard Error: 13_924_977
			.saturating_add(Weight::from_ref_time(686_578_019).saturating_mul(v.into()))
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().reads((3_u64).saturating_mul(v.into())))
			.saturating_add(T::DbWeight::get().writes((3_u64).saturating_mul(v.into())))
			.saturating_add(Weight::from_proof_size(9658).saturating_mul(v.into()))
	}
	/// Storage: Elections Candidates (r:1 w:1)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Members (r:1 w:1)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:1)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Voting (r:10001 w:0)
	/// Proof Skipped: Elections Voting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Council Proposals (r:1 w:0)
	/// Proof Skipped: Council Proposals (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: System Account (r:980 w:980)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Elections ElectionRounds (r:1 w:1)
	/// Proof Skipped: Elections ElectionRounds (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Members (r:0 w:1)
	/// Proof Skipped: Council Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Prime (r:0 w:1)
	/// Proof Skipped: Council Prime (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `c` is `[1, 1000]`.
	/// The range of component `v` is `[1, 10000]`.
	/// The range of component `e` is `[10000, 160000]`.
	fn election_phragmen(c: u32, v: u32, e: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0 + v * (638 ±0) + e * (28 ±0)`
		//  Estimated: `5586978 + v * (5383 ±21) + e * (99 ±1) + c * (2478 ±6)`
		// Minimum execution time: 337_238_000 nanoseconds.
		Weight::from_parts(338_755_000_000, 5586978)
			// Standard Error: 16_598_609
			.saturating_add(Weight::from_ref_time(8_686_952).saturating_mul(c.into()))
			// Standard Error: 1_659_179
			.saturating_add(Weight::from_ref_time(102_136_811).saturating_mul(v.into()))
			// Standard Error: 106_480
			.saturating_add(Weight::from_ref_time(331).saturating_mul(e.into()))
			.saturating_add(T::DbWeight::get().reads(448_u64))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(c.into())))
			.saturating_add(T::DbWeight::get().reads((1_u64).saturating_mul(v.into())))
			.saturating_add(T::DbWeight::get().writes(6_u64))
			.saturating_add(T::DbWeight::get().writes((1_u64).saturating_mul(c.into())))
			.saturating_add(Weight::from_proof_size(5383).saturating_mul(v.into()))
			.saturating_add(Weight::from_proof_size(99).saturating_mul(e.into()))
			.saturating_add(Weight::from_proof_size(2478).saturating_mul(c.into()))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// Storage: Elections Candidates (r:1 w:0)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Members (r:1 w:0)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:0)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Voting (r:1 w:1)
	/// Proof Skipped: Elections Voting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// The range of component `v` is `[1, 16]`.
	fn vote_equal(v: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `499 + v * (80 ±0)`
		//  Estimated: `9726 + v * (320 ±0)`
		// Minimum execution time: 415_000 nanoseconds.
		Weight::from_parts(421_838_802, 9726)
			// Standard Error: 133_238
			.saturating_add(Weight::from_ref_time(326_568).saturating_mul(v.into()))
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
			.saturating_add(Weight::from_proof_size(320).saturating_mul(v.into()))
	}
	/// Storage: Elections Candidates (r:1 w:0)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Members (r:1 w:0)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:0)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Voting (r:1 w:1)
	/// Proof Skipped: Elections Voting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// The range of component `v` is `[2, 16]`.
	fn vote_more(v: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `467 + v * (80 ±0)`
		//  Estimated: `9598 + v * (320 ±0)`
		// Minimum execution time: 558_000 nanoseconds.
		Weight::from_parts(556_163_102, 9598)
			// Standard Error: 738_644
			.saturating_add(Weight::from_ref_time(3_391_887).saturating_mul(v.into()))
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
			.saturating_add(Weight::from_proof_size(320).saturating_mul(v.into()))
	}
	/// Storage: Elections Candidates (r:1 w:0)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Members (r:1 w:0)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:0)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Voting (r:1 w:1)
	/// Proof Skipped: Elections Voting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// The range of component `v` is `[2, 16]`.
	fn vote_less(v: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `499 + v * (80 ±0)`
		//  Estimated: `9726 + v * (320 ±0)`
		// Minimum execution time: 568_000 nanoseconds.
		Weight::from_parts(621_939_239, 9726)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
			.saturating_add(Weight::from_proof_size(320).saturating_mul(v.into()))
	}
	/// Storage: Elections Voting (r:1 w:1)
	/// Proof Skipped: Elections Voting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Balances Locks (r:1 w:1)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	fn remove_voter() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `989`
		//  Estimated: `7238`
		// Minimum execution time: 504_000 nanoseconds.
		Weight::from_parts(512_000_000, 7238)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: Elections Candidates (r:1 w:1)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Members (r:1 w:0)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:0)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `c` is `[1, 1000]`.
	fn submit_candidacy(c: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `1690 + c * (48 ±0)`
		//  Estimated: `6540 + c * (144 ±0)`
		// Minimum execution time: 368_000 nanoseconds.
		Weight::from_parts(406_083_483, 6540)
			// Standard Error: 11_995
			.saturating_add(Weight::from_ref_time(161_971).saturating_mul(c.into()))
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
			.saturating_add(Weight::from_proof_size(144).saturating_mul(c.into()))
	}
	/// Storage: Elections Candidates (r:1 w:1)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `c` is `[1, 1000]`.
	fn renounce_candidacy_candidate(c: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `347 + c * (48 ±0)`
		//  Estimated: `825 + c * (48 ±0)`
		// Minimum execution time: 332_000 nanoseconds.
		Weight::from_parts(374_734_634, 825)
			// Standard Error: 10_531
			.saturating_add(Weight::from_ref_time(35_062).saturating_mul(c.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
			.saturating_add(Weight::from_proof_size(48).saturating_mul(c.into()))
	}
	/// Storage: Elections Members (r:1 w:1)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:1)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Prime (r:1 w:1)
	/// Proof Skipped: Council Prime (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Proposals (r:1 w:0)
	/// Proof Skipped: Council Proposals (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Members (r:0 w:1)
	/// Proof Skipped: Council Members (max_values: Some(1), max_size: None, mode: Measured)
	fn renounce_candidacy_members() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `2027`
		//  Estimated: `12115`
		// Minimum execution time: 521_000 nanoseconds.
		Weight::from_parts(531_000_000, 12115)
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().writes(4_u64))
	}
	/// Storage: Elections RunnersUp (r:1 w:1)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	fn renounce_candidacy_runners_up() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `975`
		//  Estimated: `1470`
		// Minimum execution time: 345_000 nanoseconds.
		Weight::from_parts(381_000_000, 1470)
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Benchmark Override (r:0 w:0)
	/// Proof Skipped: Benchmark Override (max_values: None, max_size: None, mode: Measured)
	fn remove_member_without_replacement() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_000_000_000 nanoseconds.
		Weight::from_ref_time(2_000_000_000_000)
	}
	/// Storage: Elections Members (r:1 w:1)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Elections RunnersUp (r:1 w:1)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Prime (r:1 w:1)
	/// Proof Skipped: Council Prime (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Proposals (r:1 w:0)
	/// Proof Skipped: Council Proposals (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Members (r:0 w:1)
	/// Proof Skipped: Council Members (max_values: Some(1), max_size: None, mode: Measured)
	fn remove_member_with_replacement() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `2027`
		//  Estimated: `14718`
		// Minimum execution time: 601_000 nanoseconds.
		Weight::from_parts(610_000_000, 14718)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(5_u64))
	}
	/// Storage: Elections Voting (r:10001 w:10000)
	/// Proof Skipped: Elections Voting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Elections Members (r:1 w:0)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:0)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Candidates (r:1 w:0)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Balances Locks (r:10000 w:10000)
	/// Proof: Balances Locks (max_values: None, max_size: Some(1299), added: 3774, mode: MaxEncodedLen)
	/// Storage: System Account (r:10000 w:10000)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `v` is `[5000, 10000]`.
	/// The range of component `d` is `[0, 5000]`.
	fn clean_defunct_voters(v: u32, _d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `36373 + v * (872 ±0)`
		//  Estimated: `32033948 + v * (9658 ±0)`
		// Minimum execution time: 5_401_340_000 nanoseconds.
		Weight::from_parts(5_410_097_000_000, 32033948)
			// Standard Error: 13_924_977
			.saturating_add(Weight::from_ref_time(686_578_019).saturating_mul(v.into()))
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().reads((3_u64).saturating_mul(v.into())))
			.saturating_add(RocksDbWeight::get().writes((3_u64).saturating_mul(v.into())))
			.saturating_add(Weight::from_proof_size(9658).saturating_mul(v.into()))
	}
	/// Storage: Elections Candidates (r:1 w:1)
	/// Proof Skipped: Elections Candidates (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Members (r:1 w:1)
	/// Proof Skipped: Elections Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections RunnersUp (r:1 w:1)
	/// Proof Skipped: Elections RunnersUp (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Elections Voting (r:10001 w:0)
	/// Proof Skipped: Elections Voting (max_values: None, max_size: None, mode: Measured)
	/// Storage: Council Proposals (r:1 w:0)
	/// Proof Skipped: Council Proposals (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: System Account (r:980 w:980)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Elections ElectionRounds (r:1 w:1)
	/// Proof Skipped: Elections ElectionRounds (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Members (r:0 w:1)
	/// Proof Skipped: Council Members (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: Council Prime (r:0 w:1)
	/// Proof Skipped: Council Prime (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `c` is `[1, 1000]`.
	/// The range of component `v` is `[1, 10000]`.
	/// The range of component `e` is `[10000, 160000]`.
	fn election_phragmen(c: u32, v: u32, e: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0 + v * (638 ±0) + e * (28 ±0)`
		//  Estimated: `5586978 + v * (5383 ±21) + e * (99 ±1) + c * (2478 ±6)`
		// Minimum execution time: 337_238_000 nanoseconds.
		Weight::from_parts(338_755_000_000, 5586978)
			// Standard Error: 16_598_609
			.saturating_add(Weight::from_ref_time(8_686_952).saturating_mul(c.into()))
			// Standard Error: 1_659_179
			.saturating_add(Weight::from_ref_time(102_136_811).saturating_mul(v.into()))
			// Standard Error: 106_480
			.saturating_add(Weight::from_ref_time(331).saturating_mul(e.into()))
			.saturating_add(RocksDbWeight::get().reads(448_u64))
			.saturating_add(RocksDbWeight::get().reads((1_u64).saturating_mul(c.into())))
			.saturating_add(RocksDbWeight::get().reads((1_u64).saturating_mul(v.into())))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
			.saturating_add(RocksDbWeight::get().writes((1_u64).saturating_mul(c.into())))
			.saturating_add(Weight::from_proof_size(5383).saturating_mul(v.into()))
			.saturating_add(Weight::from_proof_size(99).saturating_mul(e.into()))
			.saturating_add(Weight::from_proof_size(2478).saturating_mul(c.into()))
	}
}
