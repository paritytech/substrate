// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Default weights of pallet-staking.
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0-rc6

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::weights::{Weight, constants::RocksDbWeight as DbWeight};

impl crate::WeightInfo for () {
		fn bond() -> Weight {
		(412198000 as Weight)
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(4 as Weight))
	}
	fn bond_extra() -> Weight {
		(317637000 as Weight)
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn unbond() -> Weight {
		(277418000 as Weight)
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn withdraw_unbonded_update(s: u32, ) -> Weight {
		(282986000 as Weight)
			.saturating_add((45000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn withdraw_unbonded_kill(s: u32, ) -> Weight {
		(471338000 as Weight)
			.saturating_add((20118000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(7 as Weight))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn validate() -> Weight {
		(99599000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn nominate(n: u32, ) -> Weight {
		(125965000 as Weight)
			.saturating_add((5544000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn chill() -> Weight {
		(97291000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn set_payee() -> Weight {
		(73810000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_controller() -> Weight {
		(153200000 as Weight)
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	// WARNING! Some components were not used: ["c"]
	fn set_validator_count() -> Weight {
		(10913000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_no_eras() -> Weight {
		(13148000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_new_era() -> Weight {
		(13215000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_new_era_always() -> Weight {
		(13150000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_invulnerables(v: u32, ) -> Weight {
		(14525000 as Weight)
			.saturating_add((224000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_unstake(s: u32, ) -> Weight {
		(345510000 as Weight)
			.saturating_add((20063000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn cancel_deferred_slash(s: u32, ) -> Weight {
		(260000722000 as Weight)
			.saturating_add((1678139000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn payout_stakers(n: u32, ) -> Weight {
		(65430000 as Weight)
			.saturating_add((275913000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(n as Weight)))
	}
	fn payout_stakers_alive_controller(n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((373671000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().reads((5 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn rebond(l: u32, ) -> Weight {
		(209660000 as Weight)
			.saturating_add((2307000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn set_history_depth(e: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((92748000 as Weight).saturating_mul(e as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(4 as Weight))
			.saturating_add(DbWeight::get().writes((7 as Weight).saturating_mul(e as Weight)))
	}
	fn reap_stash(s: u32, ) -> Weight {
		(396133000 as Weight)
			.saturating_add((19951000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn new_era(v: u32, n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((20017645000 as Weight).saturating_mul(v as Weight))
			.saturating_add((1812349000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(10 as Weight))
			.saturating_add(DbWeight::get().reads((4 as Weight).saturating_mul(v as Weight)))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(v as Weight)))
	}
	fn payout_all(v: u32, n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((24211976000 as Weight).saturating_mul(v as Weight))
			.saturating_add((2022572000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads((15 as Weight).saturating_mul(v as Weight)))
			.saturating_add(DbWeight::get().reads((5 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes((8 as Weight).saturating_mul(v as Weight)))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}

	fn submit_solution_better(v: u32, n: u32, a: u32, w: u32, ) -> Weight { 0 }
}
