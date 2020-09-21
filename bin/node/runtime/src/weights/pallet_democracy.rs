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

//! Weights for the Democracy Pallet
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc6

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

pub struct WeightInfo;
impl pallet_democracy::WeightInfo for WeightInfo {
	fn propose(p: u32, ) -> Weight {
		(173882000 as Weight)
			.saturating_add((58000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(4 as Weight))
	}
	fn second(s: u32, ) -> Weight {
		(111076000 as Weight)
			.saturating_add((551000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn vote_new(r: u32, ) -> Weight {
		(150748000 as Weight)
			.saturating_add((396000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(4 as Weight))
	}
	fn vote_existing(r: u32, ) -> Weight {
		(118820000 as Weight)
			.saturating_add((1193000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(4 as Weight))
	}
	fn emergency_cancel() -> Weight {
		(43278000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn blacklist(p: u32, ) -> Weight {
		(442525000 as Weight)
			.saturating_add((515000 as Weight).saturating_mul(p as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(6 as Weight))
	}
	fn external_propose(v: u32, ) -> Weight {
		(20349000 as Weight)
			.saturating_add((114000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn external_propose_majority() -> Weight {
		(4889000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn external_propose_default() -> Weight {
		(4875000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn fast_track() -> Weight {
		(41326000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn veto_external(v: u32, ) -> Weight {
		(42518000 as Weight)
			.saturating_add((191000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn cancel_proposal() -> Weight {
		(65871000 as Weight)
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn cancel_referendum() -> Weight {
		(26151000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn cancel_queued(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((8246000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn on_initialize_base(r: u32, ) -> Weight {
		(302489000 as Weight)
			.saturating_add((21766000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(6 as Weight))
			.saturating_add(DbWeight::get().reads((2 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(5 as Weight))
	}
	fn delegate(r: u32, ) -> Weight {
		(178766000 as Weight)
			.saturating_add((19805000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(5 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn undelegate(r: u32, ) -> Weight {
		(163433000 as Weight)
			.saturating_add((8980000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(r as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(r as Weight)))
	}
	fn clear_public_proposals() -> Weight {
		(4854000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn note_preimage(b: u32, ) -> Weight {
		(63227000 as Weight)
			.saturating_add((4000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn note_imminent_preimage(b: u32, ) -> Weight {
		(42569000 as Weight)
			.saturating_add((4000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn reap_preimage(b: u32, ) -> Weight {
		(57894000 as Weight)
			.saturating_add((3000 as Weight).saturating_mul(b as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn unlock_remove(r: u32, ) -> Weight {
		(57008000 as Weight)
			.saturating_add((275000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn unlock_set(r: u32, ) -> Weight {
		(53179000 as Weight)
			.saturating_add((460000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn remove_vote(r: u32, ) -> Weight {
		(31536000 as Weight)
			.saturating_add((445000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn remove_other_vote(r: u32, ) -> Weight {
		(31418000 as Weight)
			.saturating_add((446000 as Weight).saturating_mul(r as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
}
