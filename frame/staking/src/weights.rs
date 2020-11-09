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

//! Weights for pallet_staking
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-10-27, STEPS: [50, ], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []
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
	fn withdraw_unbonded_update(_s: u32, ) -> Weight;
	fn withdraw_unbonded_kill(_s: u32, ) -> Weight;
	fn validate() -> Weight;
	fn nominate(_n: u32, ) -> Weight;
	fn chill() -> Weight;
	fn set_payee() -> Weight;
	fn set_controller() -> Weight;
	fn set_validator_count() -> Weight;
	fn force_no_eras() -> Weight;
	fn force_new_era() -> Weight;
	fn force_new_era_always() -> Weight;
	fn set_invulnerables(_v: u32, ) -> Weight;
	fn force_unstake(_s: u32, ) -> Weight;
	fn cancel_deferred_slash(_s: u32, ) -> Weight;
	fn payout_stakers_dead_controller(_n: u32, ) -> Weight;
	fn payout_stakers_alive_staked(_n: u32, ) -> Weight;
	fn rebond(_l: u32, ) -> Weight;
	fn set_history_depth(_e: u32, ) -> Weight;
	fn reap_stash(_s: u32, ) -> Weight;
	fn new_era(_v: u32, _n: u32, ) -> Weight;
	fn submit_solution_better(_v: u32, _n: u32, _a: u32, _w: u32, ) -> Weight;

}

/// Weights for pallet_staking using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Trait> WeightInfo for SubstrateWeight<T> {
	fn bond() -> Weight {
		(99_659_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))

	}
	fn bond_extra() -> Weight {
		(79_045_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}
	fn unbond() -> Weight {
		(71_716_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn withdraw_unbonded_update(s: u32, ) -> Weight {
		(72_835_000 as Weight)
			.saturating_add((63_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn withdraw_unbonded_kill(s: u32, ) -> Weight {
		(118_239_000 as Weight)
			.saturating_add((3_910_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(7 as Weight))
			.saturating_add(T::DbWeight::get().writes(8 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn validate() -> Weight {
		(25_691_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}
	fn nominate(n: u32, ) -> Weight {
		(35_374_000 as Weight)
			.saturating_add((203_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}
	fn chill() -> Weight {
		(25_227_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}
	fn set_payee() -> Weight {
		(17_601_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn set_controller() -> Weight {
		(37_514_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn set_validator_count() -> Weight {
		(3_338_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn force_no_eras() -> Weight {
		(3_869_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn force_new_era() -> Weight {
		(3_795_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn force_new_era_always() -> Weight {
		(3_829_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn set_invulnerables(v: u32, ) -> Weight {
		(4_087_000 as Weight)
			.saturating_add((9_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn force_unstake(s: u32, ) -> Weight {
		(81_063_000 as Weight)
			.saturating_add((3_872_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(8 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn cancel_deferred_slash(s: u32, ) -> Weight {
		(5_840_640_000 as Weight)
			.saturating_add((34_806_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn payout_stakers_dead_controller(n: u32, ) -> Weight {
		(153_024_000 as Weight)
			.saturating_add((59_909_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(11 as Weight))
			.saturating_add(T::DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(n as Weight)))
	}
	fn payout_stakers_alive_staked(n: u32, ) -> Weight {
		(196_058_000 as Weight)
			.saturating_add((78_955_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(12 as Weight))
			.saturating_add(T::DbWeight::get().reads((5 as Weight).saturating_mul(n as Weight)))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
			.saturating_add(T::DbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn rebond(l: u32, ) -> Weight {
		(49_966_000 as Weight)
			.saturating_add((92_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn set_history_depth(e: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((38_529_000 as Weight).saturating_mul(e as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
			.saturating_add(T::DbWeight::get().writes((7 as Weight).saturating_mul(e as Weight)))
	}
	fn reap_stash(s: u32, ) -> Weight {
		(101_457_000 as Weight)
			.saturating_add((3_914_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(8 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn new_era(v: u32, n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((948_467_000 as Weight).saturating_mul(v as Weight))
			.saturating_add((117_579_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(10 as Weight))
			.saturating_add(T::DbWeight::get().reads((4 as Weight).saturating_mul(v as Weight)))
			.saturating_add(T::DbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(T::DbWeight::get().writes(8 as Weight))
			.saturating_add(T::DbWeight::get().writes((3 as Weight).saturating_mul(v as Weight)))
	}
	fn submit_solution_better(v: u32, n: u32, a: u32, w: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1_728_000 as Weight).saturating_mul(v as Weight))
			.saturating_add((907_000 as Weight).saturating_mul(n as Weight))
			.saturating_add((99_762_000 as Weight).saturating_mul(a as Weight))
			.saturating_add((9_017_000 as Weight).saturating_mul(w as Weight))
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().reads((4 as Weight).saturating_mul(a as Weight)))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(w as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}

}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn bond() -> Weight {
		(99_659_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))

	}
	fn bond_extra() -> Weight {
		(79_045_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}
	fn unbond() -> Weight {
		(71_716_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn withdraw_unbonded_update(s: u32, ) -> Weight {
		(72_835_000 as Weight)
			.saturating_add((63_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn withdraw_unbonded_kill(s: u32, ) -> Weight {
		(118_239_000 as Weight)
			.saturating_add((3_910_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(7 as Weight))
			.saturating_add(RocksDbWeight::get().writes(8 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn validate() -> Weight {
		(25_691_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}
	fn nominate(n: u32, ) -> Weight {
		(35_374_000 as Weight)
			.saturating_add((203_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}
	fn chill() -> Weight {
		(25_227_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}
	fn set_payee() -> Weight {
		(17_601_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn set_controller() -> Weight {
		(37_514_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn set_validator_count() -> Weight {
		(3_338_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn force_no_eras() -> Weight {
		(3_869_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn force_new_era() -> Weight {
		(3_795_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn force_new_era_always() -> Weight {
		(3_829_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn set_invulnerables(v: u32, ) -> Weight {
		(4_087_000 as Weight)
			.saturating_add((9_000 as Weight).saturating_mul(v as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn force_unstake(s: u32, ) -> Weight {
		(81_063_000 as Weight)
			.saturating_add((3_872_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(8 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn cancel_deferred_slash(s: u32, ) -> Weight {
		(5_840_640_000 as Weight)
			.saturating_add((34_806_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn payout_stakers_dead_controller(n: u32, ) -> Weight {
		(153_024_000 as Weight)
			.saturating_add((59_909_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(11 as Weight))
			.saturating_add(RocksDbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(n as Weight)))
	}
	fn payout_stakers_alive_staked(n: u32, ) -> Weight {
		(196_058_000 as Weight)
			.saturating_add((78_955_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(12 as Weight))
			.saturating_add(RocksDbWeight::get().reads((5 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((3 as Weight).saturating_mul(n as Weight)))
	}
	fn rebond(l: u32, ) -> Weight {
		(49_966_000 as Weight)
			.saturating_add((92_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn set_history_depth(e: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((38_529_000 as Weight).saturating_mul(e as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes((7 as Weight).saturating_mul(e as Weight)))
	}
	fn reap_stash(s: u32, ) -> Weight {
		(101_457_000 as Weight)
			.saturating_add((3_914_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(8 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn new_era(v: u32, n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((948_467_000 as Weight).saturating_mul(v as Weight))
			.saturating_add((117_579_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(10 as Weight))
			.saturating_add(RocksDbWeight::get().reads((4 as Weight).saturating_mul(v as Weight)))
			.saturating_add(RocksDbWeight::get().reads((3 as Weight).saturating_mul(n as Weight)))
			.saturating_add(RocksDbWeight::get().writes(8 as Weight))
			.saturating_add(RocksDbWeight::get().writes((3 as Weight).saturating_mul(v as Weight)))
	}
	fn submit_solution_better(v: u32, n: u32, a: u32, w: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((1_728_000 as Weight).saturating_mul(v as Weight))
			.saturating_add((907_000 as Weight).saturating_mul(n as Weight))
			.saturating_add((99_762_000 as Weight).saturating_mul(a as Weight))
			.saturating_add((9_017_000 as Weight).saturating_mul(w as Weight))
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().reads((4 as Weight).saturating_mul(a as Weight)))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(w as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}

}
