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
		(148930000 as Weight)
			.saturating_add(DbWeight::get().reads(6 as Weight))
			.saturating_add(DbWeight::get().writes(5 as Weight))
	}
	fn bond_extra() -> Weight {
		(113370000 as Weight)
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn unbond() -> Weight {
		(102041000 as Weight)
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn withdraw_unbonded_update(s: u32, ) -> Weight {
		(102396000 as Weight)
			.saturating_add((69000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn withdraw_unbonded_kill(s: u32, ) -> Weight {
		(168850000 as Weight)
			.saturating_add((6968000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(7 as Weight))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn validate() -> Weight {
		(36647000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn nominate(n: u32, ) -> Weight {
		(47419000 as Weight)
			.saturating_add((914000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn chill() -> Weight {
		(36017000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn set_payee() -> Weight {
		(24557000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_controller() -> Weight {
		(53165000 as Weight)
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	// WARNING! Some components were not used: ["c"]
	fn set_validator_count() -> Weight {
		(5281000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_no_eras() -> Weight {
		(6003000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_new_era() -> Weight {
		(6043000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_new_era_always() -> Weight {
		(6096000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_invulnerables(v: u32, ) -> Weight {
		(6334000 as Weight)
			.saturating_add((9000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_unstake(s: u32, ) -> Weight {
		(120299000 as Weight)
			.saturating_add((6962000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn cancel_deferred_slash(s: u32, ) -> Weight {
		(5389294000 as Weight)
			.saturating_add((34593000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn payout_stakers(n: u32, ) -> Weight {
		(40610000 as Weight)
			.saturating_add((94430000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(n as Weight)))
	}
	fn payout_stakers_alive_controller(n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((119601000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().reads((5 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn rebond(l: u32, ) -> Weight {
		(71994000 as Weight)
			.saturating_add((167000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn set_history_depth(e: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((53251000 as Weight).saturating_mul(e as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(4 as Weight))
			.saturating_add(DbWeight::get().writes((7 as Weight).saturating_mul(e as Weight)))
	}
	fn reap_stash(s: u32, ) -> Weight {
		(149165000 as Weight)
			.saturating_add((6980000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn new_era(v: u32, n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1470601000 as Weight).saturating_mul(v as Weight))
			.saturating_add((187200000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(10 as Weight))
			.saturating_add(DbWeight::get().reads((4 as Weight).saturating_mul(v as Weight)))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(v as Weight)))
	}
	fn payout_all(v: u32, n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((6796630000 as Weight).saturating_mul(v as Weight))
			.saturating_add((582776000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads((15 as Weight).saturating_mul(v as Weight)))
			.saturating_add(DbWeight::get().reads((5 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes((8 as Weight).saturating_mul(v as Weight)))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn submit_solution_better(v: u32, n: u32, a: u32, w: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1488000 as Weight).saturating_mul(v as Weight))
			.saturating_add((719000 as Weight).saturating_mul(n as Weight))
			.saturating_add((211407000 as Weight).saturating_mul(a as Weight))
			.saturating_add((10786000 as Weight).saturating_mul(w as Weight))
			.saturating_add(DbWeight::get().reads(6 as Weight))
			.saturating_add(DbWeight::get().reads((4 as Weight).saturating_mul(a as Weight)))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(w as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
}
