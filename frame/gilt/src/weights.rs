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

//! Autogenerated weights for pallet_gilt
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 3.0.0
//! DATE: 2021-02-23, STEPS: [50, ], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_gilt
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/gilt/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_gilt.
pub trait WeightInfo {
	fn place_bid(l: u32, ) -> Weight;
	fn place_bid_max() -> Weight;
	fn retract_bid(l: u32, ) -> Weight;
	fn set_target() -> Weight;
	fn thaw() -> Weight;
	fn pursue_target_noop() -> Weight;
	fn pursue_target_per_item(b: u32, ) -> Weight;
	fn pursue_target_per_queue(q: u32, ) -> Weight;
}

/// Weights for pallet_gilt using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	fn place_bid(l: u32, ) -> Weight {
		(79_274_000 as Weight)
			// Standard Error: 0
			.saturating_add((289_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn place_bid_max() -> Weight {
		(297_825_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn retract_bid(l: u32, ) -> Weight {
		(79_731_000 as Weight)
			// Standard Error: 0
			.saturating_add((231_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn set_target() -> Weight {
		(6_113_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn thaw() -> Weight {
		(74_792_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn pursue_target_noop() -> Weight {
		(3_468_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
	}
	fn pursue_target_per_item(b: u32, ) -> Weight {
		(65_792_000 as Weight)
			// Standard Error: 2_000
			.saturating_add((11_402_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(b as Weight)))
	}
	fn pursue_target_per_queue(q: u32, ) -> Weight {
		(32_391_000 as Weight)
			// Standard Error: 7_000
			.saturating_add((18_500_000 as Weight).saturating_mul(q as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(q as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((2 as Weight).saturating_mul(q as Weight)))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn place_bid(l: u32, ) -> Weight {
		(79_274_000 as Weight)
			// Standard Error: 0
			.saturating_add((289_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn place_bid_max() -> Weight {
		(297_825_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn retract_bid(l: u32, ) -> Weight {
		(79_731_000 as Weight)
			// Standard Error: 0
			.saturating_add((231_000 as Weight).saturating_mul(l as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn set_target() -> Weight {
		(6_113_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	fn thaw() -> Weight {
		(74_792_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn pursue_target_noop() -> Weight {
		(3_468_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
	}
	fn pursue_target_per_item(b: u32, ) -> Weight {
		(65_792_000 as Weight)
			// Standard Error: 2_000
			.saturating_add((11_402_000 as Weight).saturating_mul(b as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(b as Weight)))
	}
	fn pursue_target_per_queue(q: u32, ) -> Weight {
		(32_391_000 as Weight)
			// Standard Error: 7_000
			.saturating_add((18_500_000 as Weight).saturating_mul(q as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(q as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((2 as Weight).saturating_mul(q as Weight)))
	}
}
