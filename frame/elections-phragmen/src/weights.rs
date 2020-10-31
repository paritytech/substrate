// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Weights for pallet_elections_phragmen
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-10-27, STEPS: [50, ], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_elections_phragmen
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/elections-phragmen/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_elections_phragmen.
pub trait WeightInfo {
	fn vote(_v: u32, ) -> Weight;
	fn vote_update(_v: u32, ) -> Weight;
	fn remove_voter() -> Weight;
	fn report_defunct_voter_correct(_c: u32, _v: u32, ) -> Weight;
	fn report_defunct_voter_incorrect(_c: u32, _v: u32, ) -> Weight;
	fn submit_candidacy(_c: u32, ) -> Weight;
	fn renounce_candidacy_candidate(_c: u32, ) -> Weight;
	fn renounce_candidacy_members() -> Weight;
	fn renounce_candidacy_runners_up() -> Weight;
	fn remove_member_with_replacement() -> Weight;
	fn remove_member_wrong_refund() -> Weight;
	
}

/// Weights for pallet_elections_phragmen using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Trait> WeightInfo for SubstrateWeight<T> {
	fn vote(v: u32, ) -> Weight {
		(89_627_000 as Weight)
			.saturating_add((197_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn vote_update(v: u32, ) -> Weight {
		(54_724_000 as Weight)
			.saturating_add((213_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn remove_voter() -> Weight {
		(73_774_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn report_defunct_voter_correct(c: u32, v: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1_746_000 as Weight).saturating_mul(c as Weight))
			.saturating_add((31_383_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(7 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
			
	}
	fn report_defunct_voter_incorrect(c: u32, v: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1_725_000 as Weight).saturating_mul(c as Weight))
			.saturating_add((31_293_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn submit_candidacy(c: u32, ) -> Weight {
		(73_403_000 as Weight)
			.saturating_add((314_000 as Weight).saturating_mul(c as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn renounce_candidacy_candidate(c: u32, ) -> Weight {
		(48_834_000 as Weight)
			.saturating_add((187_000 as Weight).saturating_mul(c as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn renounce_candidacy_members() -> Weight {
		(78_402_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
			
	}
	fn renounce_candidacy_runners_up() -> Weight {
		(49_054_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn remove_member_with_replacement() -> Weight {
		(75_421_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(5 as Weight))
			
	}
	fn remove_member_wrong_refund() -> Weight {
		(8_489_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			
	}
	
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn vote(v: u32, ) -> Weight {
		(89_627_000 as Weight)
			.saturating_add((197_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn vote_update(v: u32, ) -> Weight {
		(54_724_000 as Weight)
			.saturating_add((213_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn remove_voter() -> Weight {
		(73_774_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn report_defunct_voter_correct(c: u32, v: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1_746_000 as Weight).saturating_mul(c as Weight))
			.saturating_add((31_383_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(7 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			
	}
	fn report_defunct_voter_incorrect(c: u32, v: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1_725_000 as Weight).saturating_mul(c as Weight))
			.saturating_add((31_293_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn submit_candidacy(c: u32, ) -> Weight {
		(73_403_000 as Weight)
			.saturating_add((314_000 as Weight).saturating_mul(c as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn renounce_candidacy_candidate(c: u32, ) -> Weight {
		(48_834_000 as Weight)
			.saturating_add((187_000 as Weight).saturating_mul(c as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn renounce_candidacy_members() -> Weight {
		(78_402_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
			
	}
	fn renounce_candidacy_runners_up() -> Weight {
		(49_054_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn remove_member_with_replacement() -> Weight {
		(75_421_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
			
	}
	fn remove_member_wrong_refund() -> Weight {
		(8_489_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			
	}
	
}
