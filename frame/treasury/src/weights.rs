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

//! Weights for pallet_treasury
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-10-27, STEPS: [50, ], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_treasury
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/treasury/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_treasury.
pub trait WeightInfo {
	fn propose_spend() -> Weight;
	fn reject_proposal() -> Weight;
	fn approve_proposal() -> Weight;
	fn report_awesome(r: u32, ) -> Weight;
	fn retract_tip() -> Weight;
	fn tip_new(r: u32, t: u32, ) -> Weight;
	fn tip(t: u32, ) -> Weight;
	fn close_tip(t: u32, ) -> Weight;
	fn propose_bounty(d: u32, ) -> Weight;
	fn approve_bounty() -> Weight;
	fn propose_curator() -> Weight;
	fn unassign_curator() -> Weight;
	fn accept_curator() -> Weight;
	fn award_bounty() -> Weight;
	fn claim_bounty() -> Weight;
	fn close_bounty_proposed() -> Weight;
	fn close_bounty_active() -> Weight;
	fn extend_bounty_expiry() -> Weight;
	fn on_initialize_proposals(p: u32, ) -> Weight;
	fn on_initialize_bounties(b: u32, ) -> Weight;
	
}

/// Weights for pallet_treasury using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Trait> WeightInfo for SubstrateWeight<T> {
	fn propose_spend() -> Weight {
		(56_844_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn reject_proposal() -> Weight {
		(46_098_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn approve_proposal() -> Weight {
		(13_622_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn report_awesome(r: u32, ) -> Weight {
		(71_823_000 as Weight)
			.saturating_add((2_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn retract_tip() -> Weight {
		(60_150_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn tip_new(r: u32, t: u32, ) -> Weight {
		(46_522_000 as Weight)
			.saturating_add((2_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((145_000 as Weight).saturating_mul(t as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn tip(t: u32, ) -> Weight {
		(33_790_000 as Weight)
			.saturating_add((713_000 as Weight).saturating_mul(t as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn close_tip(t: u32, ) -> Weight {
		(113_040_000 as Weight)
			.saturating_add((375_000 as Weight).saturating_mul(t as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
			
	}
	fn propose_bounty(d: u32, ) -> Weight {
		(60_887_000 as Weight)
			.saturating_add((1_000 as Weight).saturating_mul(d as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
			
	}
	fn approve_bounty() -> Weight {
		(17_337_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn propose_curator() -> Weight {
		(14_068_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn unassign_curator() -> Weight {
		(49_717_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn accept_curator() -> Weight {
		(50_596_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn award_bounty() -> Weight {
		(36_030_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn claim_bounty() -> Weight {
		(167_088_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(5 as Weight))
			
	}
	fn close_bounty_proposed() -> Weight {
		(48_977_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
			
	}
	fn close_bounty_active() -> Weight {
		(110_959_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
			
	}
	fn extend_bounty_expiry() -> Weight {
		(34_987_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn on_initialize_proposals(p: u32, ) -> Weight {
		(76_596_000 as Weight)
			.saturating_add((73_988_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((3 as Weight).saturating_mul(p as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((3 as Weight).saturating_mul(p as Weight)))
	}
	fn on_initialize_bounties(b: u32, ) -> Weight {
		(75_165_000 as Weight)
			.saturating_add((73_634_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((3 as Weight).saturating_mul(b as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((3 as Weight).saturating_mul(b as Weight)))
	}
	
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn propose_spend() -> Weight {
		(56_844_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn reject_proposal() -> Weight {
		(46_098_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn approve_proposal() -> Weight {
		(13_622_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn report_awesome(r: u32, ) -> Weight {
		(71_823_000 as Weight)
			.saturating_add((2_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn retract_tip() -> Weight {
		(60_150_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn tip_new(r: u32, t: u32, ) -> Weight {
		(46_522_000 as Weight)
			.saturating_add((2_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((145_000 as Weight).saturating_mul(t as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn tip(t: u32, ) -> Weight {
		(33_790_000 as Weight)
			.saturating_add((713_000 as Weight).saturating_mul(t as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn close_tip(t: u32, ) -> Weight {
		(113_040_000 as Weight)
			.saturating_add((375_000 as Weight).saturating_mul(t as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			
	}
	fn propose_bounty(d: u32, ) -> Weight {
		(60_887_000 as Weight)
			.saturating_add((1_000 as Weight).saturating_mul(d as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
			
	}
	fn approve_bounty() -> Weight {
		(17_337_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn propose_curator() -> Weight {
		(14_068_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn unassign_curator() -> Weight {
		(49_717_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn accept_curator() -> Weight {
		(50_596_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn award_bounty() -> Weight {
		(36_030_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn claim_bounty() -> Weight {
		(167_088_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
			
	}
	fn close_bounty_proposed() -> Weight {
		(48_977_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			
	}
	fn close_bounty_active() -> Weight {
		(110_959_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
			
	}
	fn extend_bounty_expiry() -> Weight {
		(34_987_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn on_initialize_proposals(p: u32, ) -> Weight {
		(76_596_000 as Weight)
			.saturating_add((73_988_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((3 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((3 as Weight).saturating_mul(p as Weight)))
	}
	fn on_initialize_bounties(b: u32, ) -> Weight {
		(75_165_000 as Weight)
			.saturating_add((73_634_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((3 as Weight).saturating_mul(b as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((3 as Weight).saturating_mul(b as Weight)))
	}
	
}
