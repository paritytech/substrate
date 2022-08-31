// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Autogenerated weights for pallet_vesting
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-05-24, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_vesting
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --template=./.maintain/frame-weight-template.hbs
// --output=./frame/vesting/src/weights.rs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{RefTimeWeight, Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_vesting.
pub trait WeightInfo {
	fn vest_locked(l: u32, s: u32, ) -> Weight;
	fn vest_unlocked(l: u32, s: u32, ) -> Weight;
	fn vest_other_locked(l: u32, s: u32, ) -> Weight;
	fn vest_other_unlocked(l: u32, s: u32, ) -> Weight;
	fn vested_transfer(l: u32, s: u32, ) -> Weight;
	fn force_vested_transfer(l: u32, s: u32, ) -> Weight;
	fn not_unlocking_merge_schedules(l: u32, s: u32, ) -> Weight;
	fn unlocking_merge_schedules(l: u32, s: u32, ) -> Weight;
}

/// Weights for pallet_vesting using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	fn vest_locked(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(32_978_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(82_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(88_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(2 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	fn vest_unlocked(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(32_856_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(79_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(56_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(2 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn vest_other_locked(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(33_522_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(74_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(72_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(3 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(3 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn vest_other_unlocked(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(32_558_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(78_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(61_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(3 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(3 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	fn vested_transfer(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(49_260_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(80_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 3_000
			.saturating_add(Weight::from_ref_time(55_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(3 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(3 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: System Account (r:2 w:2)
	// Storage: Balances Locks (r:1 w:1)
	fn force_vested_transfer(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(49_166_000 as RefTimeWeight)
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(77_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 4_000
			.saturating_add(Weight::from_ref_time(43_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(4 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(4 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn not_unlocking_merge_schedules(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(34_042_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(83_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(80_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(3 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(3 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn unlocking_merge_schedules(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(33_937_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(78_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(73_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(3 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(3 as RefTimeWeight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	fn vest_locked(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(32_978_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(82_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(88_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(2 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	fn vest_unlocked(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(32_856_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(79_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(56_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(2 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn vest_other_locked(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(33_522_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(74_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(72_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(3 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(3 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn vest_other_unlocked(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(32_558_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(78_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(61_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(3 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(3 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	fn vested_transfer(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(49_260_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(80_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 3_000
			.saturating_add(Weight::from_ref_time(55_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(3 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(3 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: System Account (r:2 w:2)
	// Storage: Balances Locks (r:1 w:1)
	fn force_vested_transfer(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(49_166_000 as RefTimeWeight)
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(77_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 4_000
			.saturating_add(Weight::from_ref_time(43_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(4 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(4 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn not_unlocking_merge_schedules(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(34_042_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(83_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(80_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(3 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(3 as RefTimeWeight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn unlocking_merge_schedules(l: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(33_937_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(78_000 as RefTimeWeight).scalar_saturating_mul(l as RefTimeWeight))
			// Standard Error: 2_000
			.saturating_add(Weight::from_ref_time(73_000 as RefTimeWeight).scalar_saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(3 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(3 as RefTimeWeight))
	}
}
