// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Autogenerated weights for pallet_staking
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 3.0.0
//! DATE: 2021-03-14, STEPS: `[50, ]`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_staking
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/staking/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_staking.
pub trait WeightInfo {
	fn bond() -> Weight;
	fn bond_extra() -> Weight;
	fn unbond() -> Weight;
	fn withdraw_unbonded_update(s: u32, ) -> Weight;
	fn withdraw_unbonded_kill(s: u32, ) -> Weight;
	fn validate() -> Weight;
	fn kick(k: u32, ) -> Weight;
	fn nominate(n: u32, ) -> Weight;
	fn chill() -> Weight;
	fn set_payee() -> Weight;
	fn set_controller() -> Weight;
	fn set_validator_count() -> Weight;
	fn force_no_eras() -> Weight;
	fn force_new_era() -> Weight;
	fn force_new_era_always() -> Weight;
	fn set_invulnerables(v: u32, ) -> Weight;
	fn force_unstake(s: u32, ) -> Weight;
	fn cancel_deferred_slash(s: u32, ) -> Weight;
	fn payout_stakers_dead_controller(n: u32, ) -> Weight;
	fn payout_stakers_alive_staked(n: u32, ) -> Weight;
	fn rebond(l: u32, ) -> Weight;
	fn set_history_depth(e: u32, ) -> Weight;
	fn reap_stash(s: u32, ) -> Weight;
	fn new_era(v: u32, n: u32, ) -> Weight;
	fn submit_solution_better(v: u32, n: u32, a: u32, w: u32, ) -> Weight;
	fn get_npos_voters(v: u32, n: u32, s: u32, ) -> Weight;
	fn get_npos_targets(v: u32, ) -> Weight;
}

/// Weights for pallet_staking using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	fn bond() -> Weight {
		(80_317_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
	}
	fn bond_extra() -> Weight {
		(64_495_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn unbond() -> Weight {
		(59_679_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	fn withdraw_unbonded_update(s: u32, ) -> Weight {
		(61_078_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((40_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	fn withdraw_unbonded_kill(s: u32, ) -> Weight {
		(95_129_000 as Weight)
			// Standard Error: 2_000
			.saturating_add((2_755_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(7 as Weight))
			.saturating_add(T::DbWeight::get().writes(8 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn validate() -> Weight {
		(20_608_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn kick(k: u32, ) -> Weight {
		(33_365_000 as Weight)
			// Standard Error: 11_000
			.saturating_add((18_830_000 as Weight).saturating_mul(k as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(k as Weight)))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(k as Weight)))
	}
	fn nominate(n: u32, ) -> Weight {
		(33_885_000 as Weight)
			// Standard Error: 22_000
			.saturating_add((5_562_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(n as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn chill() -> Weight {
		(19_741_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn set_payee() -> Weight {
		(13_674_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn set_controller() -> Weight {
		(29_691_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	fn set_validator_count() -> Weight {
		(2_375_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn force_no_eras() -> Weight {
		(2_601_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn force_new_era() -> Weight {
		(2_605_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn force_new_era_always() -> Weight {
		(2_584_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn set_invulnerables(v: u32, ) -> Weight {
		(2_725_000 as Weight)
			// Standard Error: 0
			.saturating_add((35_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn force_unstake(s: u32, ) -> Weight {
		(63_551_000 as Weight)
			// Standard Error: 7_000
			.saturating_add((2_844_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(8 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn cancel_deferred_slash(s: u32, ) -> Weight {
		(5_905_400_000 as Weight)
			// Standard Error: 391_000
			.saturating_add((34_785_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn payout_stakers_dead_controller(n: u32, ) -> Weight {
		(142_264_000 as Weight)
			// Standard Error: 22_000
			.saturating_add((52_542_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(11 as Weight))
			.saturating_add(T::DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(n as Weight)))
	}
	fn payout_stakers_alive_staked(n: u32, ) -> Weight {
		(180_166_000 as Weight)
			// Standard Error: 23_000
			.saturating_add((66_767_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(12 as Weight))
			.saturating_add(T::DbWeight::get().reads((5 as Weight).saturating_mul(n as Weight)))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
			.saturating_add(T::DbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn rebond(l: u32, ) -> Weight {
		(42_577_000 as Weight)
			// Standard Error: 12_000
			.saturating_add((60_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	fn set_history_depth(e: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 68_000
			.saturating_add((33_362_000 as Weight).saturating_mul(e as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
			.saturating_add(T::DbWeight::get().writes((7 as Weight).saturating_mul(e as Weight)))
	}
	fn reap_stash(s: u32, ) -> Weight {
		(68_474_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((2_770_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(8 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn new_era(v: u32, n: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 903_000
			.saturating_add((594_145_000 as Weight).saturating_mul(v as Weight))
			// Standard Error: 45_000
			.saturating_add((83_373_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(9 as Weight))
			.saturating_add(T::DbWeight::get().reads((4 as Weight).saturating_mul(v as Weight)))
			.saturating_add(T::DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(T::DbWeight::get().writes(13 as Weight))
			.saturating_add(T::DbWeight::get().writes((3 as Weight).saturating_mul(v as Weight)))
	}
	fn submit_solution_better(v: u32, n: u32, a: u32, w: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 52_000
			.saturating_add((1_460_000 as Weight).saturating_mul(v as Weight))
			// Standard Error: 20_000
			.saturating_add((754_000 as Weight).saturating_mul(n as Weight))
			// Standard Error: 52_000
			.saturating_add((74_798_000 as Weight).saturating_mul(a as Weight))
			// Standard Error: 108_000
			.saturating_add((8_108_000 as Weight).saturating_mul(w as Weight))
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().reads((4 as Weight).saturating_mul(a as Weight)))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(w as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn get_npos_voters(v: u32, n: u32, s: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 94_000
			.saturating_add((29_321_000 as Weight).saturating_mul(v as Weight))
			// Standard Error: 94_000
			.saturating_add((66_885_000 as Weight).saturating_mul(n as Weight))
			// Standard Error: 1_283_000
			.saturating_add((22_991_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((4 as Weight).saturating_mul(v as Weight)))
			.saturating_add(T::DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
	}
	fn get_npos_targets(v: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 26_000
			.saturating_add((10_972_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(v as Weight)))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn bond() -> Weight {
		(80_317_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
	}
	fn bond_extra() -> Weight {
		(64_495_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn unbond() -> Weight {
		(59_679_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	fn withdraw_unbonded_update(s: u32, ) -> Weight {
		(61_078_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((40_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	fn withdraw_unbonded_kill(s: u32, ) -> Weight {
		(95_129_000 as Weight)
			// Standard Error: 2_000
			.saturating_add((2_755_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(7 as Weight))
			.saturating_add(RocksDbWeight::get().writes(8 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn validate() -> Weight {
		(20_608_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn kick(k: u32, ) -> Weight {
		(33_365_000 as Weight)
			// Standard Error: 11_000
			.saturating_add((18_830_000 as Weight).saturating_mul(k as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(k as Weight)))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(k as Weight)))
	}
	fn nominate(n: u32, ) -> Weight {
		(33_885_000 as Weight)
			// Standard Error: 22_000
			.saturating_add((5_562_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn chill() -> Weight {
		(19_741_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn set_payee() -> Weight {
		(13_674_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	fn set_controller() -> Weight {
		(29_691_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	fn set_validator_count() -> Weight {
		(2_375_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	fn force_no_eras() -> Weight {
		(2_601_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	fn force_new_era() -> Weight {
		(2_605_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	fn force_new_era_always() -> Weight {
		(2_584_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	fn set_invulnerables(v: u32, ) -> Weight {
		(2_725_000 as Weight)
			// Standard Error: 0
			.saturating_add((35_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	fn force_unstake(s: u32, ) -> Weight {
		(63_551_000 as Weight)
			// Standard Error: 7_000
			.saturating_add((2_844_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(8 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn cancel_deferred_slash(s: u32, ) -> Weight {
		(5_905_400_000 as Weight)
			// Standard Error: 391_000
			.saturating_add((34_785_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	fn payout_stakers_dead_controller(n: u32, ) -> Weight {
		(142_264_000 as Weight)
			// Standard Error: 22_000
			.saturating_add((52_542_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(11 as Weight))
			.saturating_add(RocksDbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(n as Weight)))
	}
	fn payout_stakers_alive_staked(n: u32, ) -> Weight {
		(180_166_000 as Weight)
			// Standard Error: 23_000
			.saturating_add((66_767_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(12 as Weight))
			.saturating_add(RocksDbWeight::get().reads((5 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn rebond(l: u32, ) -> Weight {
		(42_577_000 as Weight)
			// Standard Error: 12_000
			.saturating_add((60_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	fn set_history_depth(e: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 68_000
			.saturating_add((33_362_000 as Weight).saturating_mul(e as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes((7 as Weight).saturating_mul(e as Weight)))
	}
	fn reap_stash(s: u32, ) -> Weight {
		(68_474_000 as Weight)
			// Standard Error: 1_000
			.saturating_add((2_770_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(8 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn new_era(v: u32, n: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 903_000
			.saturating_add((594_145_000 as Weight).saturating_mul(v as Weight))
			// Standard Error: 45_000
			.saturating_add((83_373_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(9 as Weight))
			.saturating_add(RocksDbWeight::get().reads((4 as Weight).saturating_mul(v as Weight)))
			.saturating_add(RocksDbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(13 as Weight))
			.saturating_add(RocksDbWeight::get().writes((3 as Weight).saturating_mul(v as Weight)))
	}
	fn submit_solution_better(v: u32, n: u32, a: u32, w: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 52_000
			.saturating_add((1_460_000 as Weight).saturating_mul(v as Weight))
			// Standard Error: 20_000
			.saturating_add((754_000 as Weight).saturating_mul(n as Weight))
			// Standard Error: 52_000
			.saturating_add((74_798_000 as Weight).saturating_mul(a as Weight))
			// Standard Error: 108_000
			.saturating_add((8_108_000 as Weight).saturating_mul(w as Weight))
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().reads((4 as Weight).saturating_mul(a as Weight)))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(w as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn get_npos_voters(v: u32, n: u32, s: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 94_000
			.saturating_add((29_321_000 as Weight).saturating_mul(v as Weight))
			// Standard Error: 94_000
			.saturating_add((66_885_000 as Weight).saturating_mul(n as Weight))
			// Standard Error: 1_283_000
			.saturating_add((22_991_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((4 as Weight).saturating_mul(v as Weight)))
			.saturating_add(RocksDbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
	}
	fn get_npos_targets(v: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 26_000
			.saturating_add((10_972_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(v as Weight)))
	}
}
