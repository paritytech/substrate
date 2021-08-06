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

//! Autogenerated weights for pallet_vesting
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2021-08-06, STEPS: `50`, REPEAT: 1, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --internal-repeat=20
// --pallet=pallet_vesting
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/vesting/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_vesting.
pub trait WeightInfo {
	fn vest_locked(l: u32, ) -> Weight;
	fn vest_unlocked(l: u32, ) -> Weight;
	fn vest_other_locked(l: u32, ) -> Weight;
	fn vest_other_unlocked(l: u32, ) -> Weight;
	fn vested_transfer(l: u32, ) -> Weight;
	fn force_vested_transfer(l: u32, ) -> Weight;
}

/// Weights for pallet_vesting using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Vesting Vesting (r:1 w:0)
	fn vest_locked(l: u32, ) -> Weight {
		(44_798_000 as Weight)
			// Standard Error: 11_000
			.saturating_add((199_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Vesting Vesting (r:1 w:1)
	fn vest_unlocked(l: u32, ) -> Weight {
		(47_826_000 as Weight)
			// Standard Error: 10_000
			.saturating_add((176_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	// Storage: Vesting Vesting (r:1 w:0)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn vest_other_locked(l: u32, ) -> Weight {
		(44_204_000 as Weight)
			// Standard Error: 14_000
			.saturating_add((218_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn vest_other_unlocked(l: u32, ) -> Weight {
		(47_846_000 as Weight)
			// Standard Error: 7_000
			.saturating_add((164_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn vested_transfer(l: u32, ) -> Weight {
		(100_416_000 as Weight)
			// Standard Error: 15_000
			.saturating_add((202_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: System Account (r:2 w:2)
	fn force_vested_transfer(l: u32, ) -> Weight {
		(98_783_000 as Weight)
			// Standard Error: 14_000
			.saturating_add((220_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Vesting Vesting (r:1 w:0)
	fn vest_locked(l: u32, ) -> Weight {
		(44_798_000 as Weight)
			// Standard Error: 11_000
			.saturating_add((199_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Vesting Vesting (r:1 w:1)
	fn vest_unlocked(l: u32, ) -> Weight {
		(47_826_000 as Weight)
			// Standard Error: 10_000
			.saturating_add((176_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	// Storage: Vesting Vesting (r:1 w:0)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn vest_other_locked(l: u32, ) -> Weight {
		(44_204_000 as Weight)
			// Standard Error: 14_000
			.saturating_add((218_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn vest_other_unlocked(l: u32, ) -> Weight {
		(47_846_000 as Weight)
			// Standard Error: 7_000
			.saturating_add((164_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn vested_transfer(l: u32, ) -> Weight {
		(100_416_000 as Weight)
			// Standard Error: 15_000
			.saturating_add((202_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Vesting Vesting (r:1 w:1)
	// Storage: System Account (r:2 w:2)
	fn force_vested_transfer(l: u32, ) -> Weight {
		(98_783_000 as Weight)
			// Standard Error: 14_000
			.saturating_add((220_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
	}
}
