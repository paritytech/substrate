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
		(144278000 as Weight)
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(4 as Weight))
	}
	fn bond_extra() -> Weight {
		(110715000 as Weight)
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn unbond() -> Weight {
		(99840000 as Weight)
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn withdraw_unbonded_update(s: u32, ) -> Weight {
		(100728000 as Weight)
			.saturating_add((63000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn withdraw_unbonded_kill(s: u32, ) -> Weight {
		(168879000 as Weight)
			.saturating_add((6666000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(7 as Weight))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn validate() -> Weight {
		(35539000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn nominate(n: u32, ) -> Weight {
		(48596000 as Weight)
			.saturating_add((308000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn chill() -> Weight {
		(35144000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn set_payee() -> Weight {
		(24255000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_controller() -> Weight {
		(52294000 as Weight)
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn set_validator_count() -> Weight {
		(5185000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_no_eras() -> Weight {
		(5907000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_new_era() -> Weight {
		(5917000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_new_era_always() -> Weight {
		(5952000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_invulnerables(v: u32, ) -> Weight {
		(6324000 as Weight)
			.saturating_add((9000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_unstake(s: u32, ) -> Weight {
		(119691000 as Weight)
			.saturating_add((6681000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn cancel_deferred_slash(s: u32, ) -> Weight {
		(5820201000 as Weight)
			.saturating_add((34672000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn payout_stakers_dead_controller(n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((92486000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(n as Weight)))
	}
	fn payout_stakers_alive_staked(n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((117324000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads((5 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn rebond(l: u32, ) -> Weight {
		(71316000 as Weight)
			.saturating_add((142000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn set_history_depth(e: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((51901000 as Weight).saturating_mul(e as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(4 as Weight))
			.saturating_add(DbWeight::get().writes((7 as Weight).saturating_mul(e as Weight)))
	}
	fn reap_stash(s: u32, ) -> Weight {
		(147166000 as Weight)
			.saturating_add((6661000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn new_era(v: u32, n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1440459000 as Weight).saturating_mul(v as Weight))
			.saturating_add((182580000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(10 as Weight))
			.saturating_add(DbWeight::get().reads((4 as Weight).saturating_mul(v as Weight)))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(v as Weight)))
	}
	fn submit_solution_better(v: u32, n: u32, a: u32, w: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((964000 as Weight).saturating_mul(v as Weight))
			.saturating_add((432000 as Weight).saturating_mul(n as Weight))
			.saturating_add((204294000 as Weight).saturating_mul(a as Weight))
			.saturating_add((9546000 as Weight).saturating_mul(w as Weight))
			.saturating_add(DbWeight::get().reads(6 as Weight))
			.saturating_add(DbWeight::get().reads((4 as Weight).saturating_mul(a as Weight)))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(w as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
}
