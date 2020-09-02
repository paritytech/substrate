
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

pub struct WeightInfo;
impl crate::WeightInfo for WeightInfo {
	// WARNING! Some components were not used: ["u"]
	fn bond() -> Weight {
		(65788000 as Weight)
			.saturating_add(DbWeight::get().reads(6 as Weight))
			.saturating_add(DbWeight::get().writes(5 as Weight))
	}
	// WARNING! Some components were not used: ["u"]
	fn bond_extra() -> Weight {
		(53598000 as Weight)
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	// WARNING! Some components were not used: ["u"]
	fn unbond() -> Weight {
		(48977000 as Weight)
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn withdraw_unbonded_update(s: u32, ) -> Weight {
		(49008000 as Weight)
			.saturating_add((30000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn withdraw_unbonded_kill(s: u32, ) -> Weight {
		(69924000 as Weight)
			.saturating_add((1554000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(7 as Weight))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	// WARNING! Some components were not used: ["u"]
	fn validate() -> Weight {
		(15848000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn nominate(n: u32, ) -> Weight {
		(20625000 as Weight)
			.saturating_add((357000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	// WARNING! Some components were not used: ["u"]
	fn chill() -> Weight {
		(17159000 as Weight)
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	// WARNING! Some components were not used: ["u"]
	fn set_payee() -> Weight {
		(10970000 as Weight)
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	// WARNING! Some components were not used: ["u"]
	fn set_controller() -> Weight {
		(23826000 as Weight)
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	// WARNING! Some components were not used: ["c"]
	fn set_validator_count() -> Weight {
		(1962000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	// WARNING! Some components were not used: ["i"]
	fn force_no_eras() -> Weight {
		(2000000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	// WARNING! Some components were not used: ["i"]
	fn force_new_era() -> Weight {
		(2000000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	// WARNING! Some components were not used: ["i"]
	fn force_new_era_always() -> Weight {
		(2000000 as Weight)
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn set_invulnerables(v: u32, ) -> Weight {
		(1955000 as Weight)
			.saturating_add((4000 as Weight).saturating_mul(v as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn force_unstake(s: u32, ) -> Weight {
		(38402000 as Weight)
			.saturating_add((1711000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn cancel_deferred_slash(s: u32, ) -> Weight {
		(410638000 as Weight)
			.saturating_add((710000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().writes(1 as Weight))
	}
	fn payout_stakers(n: u32, ) -> Weight {
		(31790000 as Weight)
			.saturating_add((40680000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(5 as Weight))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes(1 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(n as Weight)))
	}
	fn payout_stakers_alive_controller(n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((55362000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(1 as Weight))
			.saturating_add(DbWeight::get().reads((5 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn rebond(l: u32, ) -> Weight {
		(35025000 as Weight)
			.saturating_add((28000 as Weight).saturating_mul(l as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(3 as Weight))
	}
	fn set_history_depth(e: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((43889000 as Weight).saturating_mul(e as Weight))
			.saturating_add(DbWeight::get().reads(2 as Weight))
			.saturating_add(DbWeight::get().writes(4 as Weight))
			.saturating_add(DbWeight::get().writes((7 as Weight).saturating_mul(e as Weight)))
	}
	fn reap_stash(s: u32, ) -> Weight {
		(69698000 as Weight)
			.saturating_add((1680000 as Weight).saturating_mul(s as Weight))
			.saturating_add(DbWeight::get().reads(4 as Weight))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn new_era(v: u32, n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((462131000 as Weight).saturating_mul(v as Weight))
			.saturating_add((75480000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(10 as Weight))
			.saturating_add(DbWeight::get().reads((4 as Weight).saturating_mul(v as Weight)))
			.saturating_add(DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes(8 as Weight))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(v as Weight)))
	}
	// WARNING! Some components were not used: ["l"]
	fn do_slash() -> Weight {
		(47783000 as Weight)
			.saturating_add(DbWeight::get().reads(3 as Weight))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn payout_all(v: u32, n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1841741000 as Weight).saturating_mul(v as Weight))
			.saturating_add((181891000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads((15 as Weight).saturating_mul(v as Weight)))
			.saturating_add(DbWeight::get().reads((5 as Weight).saturating_mul(n as Weight)))
			.saturating_add(DbWeight::get().writes((8 as Weight).saturating_mul(v as Weight)))
			.saturating_add(DbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn submit_solution_initial(v: u32, n: u32, a: u32, w: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((762000 as Weight).saturating_mul(v as Weight))
			.saturating_add((868000 as Weight).saturating_mul(n as Weight))
			.saturating_add((66802000 as Weight).saturating_mul(a as Weight))
			.saturating_add((6474000 as Weight).saturating_mul(w as Weight))
			.saturating_add(DbWeight::get().reads(6 as Weight))
			.saturating_add(DbWeight::get().reads((4 as Weight).saturating_mul(a as Weight)))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(w as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn submit_solution_better(v: u32, n: u32, a: u32, w: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((784000 as Weight).saturating_mul(v as Weight))
			.saturating_add((640000 as Weight).saturating_mul(n as Weight))
			.saturating_add((68830000 as Weight).saturating_mul(a as Weight))
			.saturating_add((8181000 as Weight).saturating_mul(w as Weight))
			.saturating_add(DbWeight::get().reads(6 as Weight))
			.saturating_add(DbWeight::get().reads((4 as Weight).saturating_mul(a as Weight)))
			.saturating_add(DbWeight::get().reads((1 as Weight).saturating_mul(w as Weight)))
			.saturating_add(DbWeight::get().writes(2 as Weight))
	}
	fn submit_solution_weaker(v: u32, n: u32, ) -> Weight {
		(11244000 as Weight)
			.saturating_add((28000 as Weight).saturating_mul(v as Weight))
			.saturating_add((12000 as Weight).saturating_mul(n as Weight))
			.saturating_add(DbWeight::get().reads(3 as Weight))
	}
}


#[cfg(feature = "std")]
impl crate::WeightInfo for () {
	fn bond() -> Weight { 1_000_000_000 }
	fn bond_extra() -> Weight { 1_000_000_000 }
	fn unbond() -> Weight { 1_000_000_000 }
	fn withdraw_unbonded_update(_s: u32, ) -> Weight { 1_000_000_000 }
	fn withdraw_unbonded_kill(_s: u32, ) -> Weight { 1_000_000_000 }
	fn validate() -> Weight { 1_000_000_000 }
	fn nominate(_n: u32) -> Weight { 1_000_000_000 }
	fn chill() -> Weight { 1_000_000_000 }
	fn set_payee() -> Weight { 1_000_000_000 }
	fn set_controller() -> Weight { 1_000_000_000 }
	fn set_validator_count() -> Weight { 1_000_000_000 }
	fn force_no_eras() -> Weight { 1_000_000_000 }
	fn force_new_era() -> Weight { 1_000_000_000 }
	fn force_new_era_always() -> Weight { 1_000_000_000 }
	fn set_invulnerables(_v: u32, ) -> Weight { 1_000_000_000 }
	fn force_unstake(_s: u32, ) -> Weight { 1_000_000_000 }
	fn cancel_deferred_slash(_s: u32, ) -> Weight { 1_000_000_000 }
	fn payout_stakers(_n: u32, ) -> Weight { 1_000_000_000 }
	fn payout_stakers_alive_controller(_n: u32, ) -> Weight { 1_000_000_000 }
	fn rebond(_l: u32, ) -> Weight { 1_000_000_000 }
	fn set_history_depth(_e: u32, ) -> Weight { 1_000_000_000 }
	fn reap_stash(_s: u32, ) -> Weight { 1_000_000_000 }
	fn new_era(_v: u32, _n: u32, ) -> Weight { 1_000_000_000 }
	fn do_slash() -> Weight { 1_000_000_000 }
	fn payout_all(_v: u32, _n: u32, ) -> Weight { 1_000_000_000 }
	fn submit_solution_initial(_v: u32, _n: u32, _a: u32, _w: u32, ) -> Weight { 1_000_000_000 }
	fn submit_solution_better(_v: u32, _n: u32, _a: u32, _w: u32, ) -> Weight { 1_000_000_000 }
	fn submit_solution_weaker(_v: u32, _n: u32, ) -> Weight { 1_000_000_000 }
}
