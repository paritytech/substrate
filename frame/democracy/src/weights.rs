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

//! Weights for pallet_democracy
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-10-27, STEPS: [50, ], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_democracy
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/democracy/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_democracy.
pub trait WeightInfo {
	fn propose() -> Weight;
	fn second(_s: u32, ) -> Weight;
	fn vote_new(_r: u32, ) -> Weight;
	fn vote_existing(_r: u32, ) -> Weight;
	fn emergency_cancel() -> Weight;
	fn blacklist(_p: u32, ) -> Weight;
	fn external_propose(_v: u32, ) -> Weight;
	fn external_propose_majority() -> Weight;
	fn external_propose_default() -> Weight;
	fn fast_track() -> Weight;
	fn veto_external(_v: u32, ) -> Weight;
	fn cancel_proposal(_p: u32, ) -> Weight;
	fn cancel_referendum() -> Weight;
	fn cancel_queued(_r: u32, ) -> Weight;
	fn on_initialize_base(_r: u32, ) -> Weight;
	fn delegate(_r: u32, ) -> Weight;
	fn undelegate(_r: u32, ) -> Weight;
	fn clear_public_proposals() -> Weight;
	fn note_preimage(_b: u32, ) -> Weight;
	fn note_imminent_preimage(_b: u32, ) -> Weight;
	fn reap_preimage(_b: u32, ) -> Weight;
	fn unlock_remove(_r: u32, ) -> Weight;
	fn unlock_set(_r: u32, ) -> Weight;
	fn remove_vote(_r: u32, ) -> Weight;
	fn remove_other_vote(_r: u32, ) -> Weight;

}

/// Weights for pallet_democracy using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Trait> WeightInfo for SubstrateWeight<T> {
	fn propose() -> Weight {
		(86_479_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn second(s: u32, ) -> Weight {
		(52_126_000 as Weight)
			.saturating_add((211_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn vote_new(r: u32, ) -> Weight {
		(62_010_000 as Weight)
			.saturating_add((288_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn vote_existing(r: u32, ) -> Weight {
		(61_870_000 as Weight)
			.saturating_add((294_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn emergency_cancel() -> Weight {
		(37_329_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}
	fn blacklist(p: u32, ) -> Weight {
		(105_595_000 as Weight)
			.saturating_add((812_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(6 as Weight))

	}
	fn external_propose(v: u32, ) -> Weight {
		(18_670_000 as Weight)
			.saturating_add((110_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn external_propose_majority() -> Weight {
		(4_413_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn external_propose_default() -> Weight {
		(4_365_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn fast_track() -> Weight {
		(37_914_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn veto_external(v: u32, ) -> Weight {
		(38_965_000 as Weight)
			.saturating_add((188_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}
	fn cancel_proposal(p: u32, ) -> Weight {
		(66_560_000 as Weight)
			.saturating_add((898_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn cancel_referendum() -> Weight {
		(22_971_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn cancel_queued(r: u32, ) -> Weight {
		(41_431_000 as Weight)
			.saturating_add((4_598_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}
	fn on_initialize_base(r: u32, ) -> Weight {
		(14_908_000 as Weight)
			.saturating_add((6_638_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))

	}
	fn delegate(r: u32, ) -> Weight {
		(82_620_000 as Weight)
			.saturating_add((9_780_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn undelegate(r: u32, ) -> Weight {
		(40_817_000 as Weight)
			.saturating_add((9_870_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn clear_public_proposals() -> Weight {
		(4_071_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn note_preimage(b: u32, ) -> Weight {
		(58_361_000 as Weight)
			.saturating_add((4_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn note_imminent_preimage(b: u32, ) -> Weight {
		(39_294_000 as Weight)
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn reap_preimage(b: u32, ) -> Weight {
		(52_829_000 as Weight)
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn unlock_remove(r: u32, ) -> Weight {
		(52_058_000 as Weight)
			.saturating_add((131_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn unlock_set(r: u32, ) -> Weight {
		(47_488_000 as Weight)
			.saturating_add((317_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn remove_vote(r: u32, ) -> Weight {
		(28_231_000 as Weight)
			.saturating_add((311_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}
	fn remove_other_vote(r: u32, ) -> Weight {
		(27_743_000 as Weight)
			.saturating_add((217_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}

}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn propose() -> Weight {
		(86_479_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn second(s: u32, ) -> Weight {
		(52_126_000 as Weight)
			.saturating_add((211_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn vote_new(r: u32, ) -> Weight {
		(62_010_000 as Weight)
			.saturating_add((288_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn vote_existing(r: u32, ) -> Weight {
		(61_870_000 as Weight)
			.saturating_add((294_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn emergency_cancel() -> Weight {
		(37_329_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}
	fn blacklist(p: u32, ) -> Weight {
		(105_595_000 as Weight)
			.saturating_add((812_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(6 as Weight))

	}
	fn external_propose(v: u32, ) -> Weight {
		(18_670_000 as Weight)
			.saturating_add((110_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn external_propose_majority() -> Weight {
		(4_413_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn external_propose_default() -> Weight {
		(4_365_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn fast_track() -> Weight {
		(37_914_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn veto_external(v: u32, ) -> Weight {
		(38_965_000 as Weight)
			.saturating_add((188_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}
	fn cancel_proposal(p: u32, ) -> Weight {
		(66_560_000 as Weight)
			.saturating_add((898_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn cancel_referendum() -> Weight {
		(22_971_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn cancel_queued(r: u32, ) -> Weight {
		(41_431_000 as Weight)
			.saturating_add((4_598_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}
	fn on_initialize_base(r: u32, ) -> Weight {
		(14_908_000 as Weight)
			.saturating_add((6_638_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))

	}
	fn delegate(r: u32, ) -> Weight {
		(82_620_000 as Weight)
			.saturating_add((9_780_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn undelegate(r: u32, ) -> Weight {
		(40_817_000 as Weight)
			.saturating_add((9_870_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn clear_public_proposals() -> Weight {
		(4_071_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn note_preimage(b: u32, ) -> Weight {
		(58_361_000 as Weight)
			.saturating_add((4_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn note_imminent_preimage(b: u32, ) -> Weight {
		(39_294_000 as Weight)
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn reap_preimage(b: u32, ) -> Weight {
		(52_829_000 as Weight)
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn unlock_remove(r: u32, ) -> Weight {
		(52_058_000 as Weight)
			.saturating_add((131_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn unlock_set(r: u32, ) -> Weight {
		(47_488_000 as Weight)
			.saturating_add((317_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn remove_vote(r: u32, ) -> Weight {
		(28_231_000 as Weight)
			.saturating_add((311_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}
	fn remove_other_vote(r: u32, ) -> Weight {
		(27_743_000 as Weight)
			.saturating_add((217_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}

}
