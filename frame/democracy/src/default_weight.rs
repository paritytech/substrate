// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Weights for pallet_democracy
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-09-24, STEPS: [50], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

impl crate::WeightInfo for () {
	fn propose() -> Weight {
		(96_316_000 as Weight)
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn second(s: u32, ) -> Weight {
		(58_386_000 as Weight)
			.saturating_add((259_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn vote_new(r: u32, ) -> Weight {
		(70_374_000 as Weight)
			.saturating_add((291_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn vote_existing(r: u32, ) -> Weight {
		(70_097_000 as Weight)
			.saturating_add((296_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn emergency_cancel() -> Weight {
		(41_731_000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn blacklist(p: u32, ) -> Weight {
		(117_847_000 as Weight)
			.saturating_add((871_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(6 as Weight))
	}
	fn external_propose(v: u32, ) -> Weight {
		(20_972_000 as Weight)
			.saturating_add((114_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn external_propose_majority() -> Weight {
		(5_030_000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn external_propose_default() -> Weight {
		(4_981_000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn fast_track() -> Weight {
		(42_801_000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn veto_external(v: u32, ) -> Weight {
		(44_115_000 as Weight)
			.saturating_add((194_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn cancel_proposal(p: u32, ) -> Weight {
		(73_937_000 as Weight)
			.saturating_add((962_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn cancel_referendum() -> Weight {
		(25_233_000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn cancel_queued(r: u32, ) -> Weight {
		(48_251_000 as Weight)
			.saturating_add((3_590_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn on_initialize_base(r: u32, ) -> Weight {
		(17_597_000 as Weight)
			.saturating_add((7_248_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
	}
	fn delegate(r: u32, ) -> Weight {
		(93_916_000 as Weight)
			.saturating_add((10_794_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(4 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn undelegate(r: u32, ) -> Weight {
		(47_855_000 as Weight)
			.saturating_add((10_805_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn clear_public_proposals() -> Weight {
		(4_864_000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn note_preimage(b: u32, ) -> Weight {
		(66_754_000 as Weight)
			.saturating_add((4_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn note_imminent_preimage(b: u32, ) -> Weight {
		(44_664_000 as Weight)
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn reap_preimage(b: u32, ) -> Weight {
		(59_968_000 as Weight)
			.saturating_add((3_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn unlock_remove(r: u32, ) -> Weight {
		(58_573_000 as Weight)
			.saturating_add((131_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn unlock_set(r: u32, ) -> Weight {
		(53_831_000 as Weight)
			.saturating_add((324_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn remove_vote(r: u32, ) -> Weight {
		(31_846_000 as Weight)
			.saturating_add((327_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn remove_other_vote(r: u32, ) -> Weight {
		(31_880_000 as Weight)
			.saturating_add((222_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
}
