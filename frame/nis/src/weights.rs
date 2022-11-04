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

//! Autogenerated weights for pallet_nis
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-05-23, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_nis
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --template=./.maintain/frame-weight-template.hbs
// --output=./frame/nis/src/weights.rs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_nis.
pub trait WeightInfo {
	fn place_bid(l: u32, ) -> Weight;
	fn place_bid_max() -> Weight;
	fn retract_bid(l: u32, ) -> Weight;
	fn thaw() -> Weight;
	fn fund_deficit() -> Weight;
	fn process_queues() -> Weight;
	fn process_queue() -> Weight;
	fn process_bid() -> Weight;
}

/// Weights for pallet_nis using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: Nis Queues (r:1 w:1)
	// Storage: Nis QueueTotals (r:1 w:1)
	fn place_bid(l: u32, ) -> Weight {
		Weight::from_ref_time(41_605_000 as u64)
			// Standard Error: 0
			.saturating_add(Weight::from_ref_time(62_000 as u64).saturating_mul(l as u64))
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: Nis Queues (r:1 w:1)
	// Storage: Nis QueueTotals (r:1 w:1)
	fn place_bid_max() -> Weight {
		Weight::from_ref_time(97_715_000 as u64)
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: Nis Queues (r:1 w:1)
	// Storage: Nis QueueTotals (r:1 w:1)
	fn retract_bid(l: u32, ) -> Weight {
		Weight::from_ref_time(42_061_000 as u64)
			// Standard Error: 0
			.saturating_add(Weight::from_ref_time(52_000 as u64).saturating_mul(l as u64))
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: Nis Active (r:1 w:1)
	// Storage: Nis ActiveTotal (r:1 w:1)
	fn thaw() -> Weight {
		Weight::from_ref_time(47_753_000 as u64)
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: Nis Active (r:1 w:1)
	// Storage: Nis ActiveTotal (r:1 w:1)
	fn fund_deficit() -> Weight {
		Weight::from_ref_time(47_753_000 as u64)
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: Nis ActiveTotal (r:1 w:0)
	fn process_queues() -> Weight {
		Weight::from_ref_time(1_663_000 as u64)
			.saturating_add(T::DbWeight::get().reads(1 as u64))
	}
	// Storage: Nis ActiveTotal (r:1 w:1)
	// Storage: Nis QueueTotals (r:1 w:1)
	// Storage: Nis Queues (r:1 w:1)
	// Storage: Nis Active (r:0 w:1)
	fn process_queue() -> Weight {
		Weight::from_ref_time(40_797_000 as u64)
			// Standard Error: 1_000
			.saturating_add(T::DbWeight::get().reads(3 as u64))
			.saturating_add(T::DbWeight::get().writes(3 as u64))
	}
	// Storage: Nis ActiveTotal (r:1 w:1)
	// Storage: Nis QueueTotals (r:1 w:1)
	// Storage: Nis Queues (r:1 w:1)
	// Storage: Nis Active (r:0 w:1)
	fn process_bid() -> Weight {
		Weight::from_ref_time(14_944_000 as u64)
			// Standard Error: 6_000
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: Nis Queues (r:1 w:1)
	// Storage: Nis QueueTotals (r:1 w:1)
	fn place_bid(l: u32, ) -> Weight {
		Weight::from_ref_time(41_605_000 as u64)
			// Standard Error: 0
			.saturating_add(Weight::from_ref_time(62_000 as u64).saturating_mul(l as u64))
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	// Storage: Nis Queues (r:1 w:1)
	// Storage: Nis QueueTotals (r:1 w:1)
	fn place_bid_max() -> Weight {
		Weight::from_ref_time(97_715_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	// Storage: Nis Queues (r:1 w:1)
	// Storage: Nis QueueTotals (r:1 w:1)
	fn retract_bid(l: u32, ) -> Weight {
		Weight::from_ref_time(42_061_000 as u64)
			// Standard Error: 0
			.saturating_add(Weight::from_ref_time(52_000 as u64).saturating_mul(l as u64))
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	// Storage: Nis Active (r:1 w:1)
	// Storage: Nis ActiveTotal (r:1 w:1)
	fn thaw() -> Weight {
		Weight::from_ref_time(47_753_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	// Storage: Nis Active (r:1 w:1)
	// Storage: Nis ActiveTotal (r:1 w:1)
	fn fund_deficit() -> Weight {
		Weight::from_ref_time(47_753_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	// Storage: Nis ActiveTotal (r:1 w:0)
	fn process_queues() -> Weight {
		Weight::from_ref_time(1_663_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
	}
	// Storage: Nis ActiveTotal (r:1 w:1)
	// Storage: Nis QueueTotals (r:1 w:1)
	// Storage: Nis Queues (r:1 w:1)
	// Storage: Nis Active (r:0 w:1)
	fn process_queue() -> Weight {
		Weight::from_ref_time(40_797_000 as u64)
			// Standard Error: 1_000
			.saturating_add(RocksDbWeight::get().reads(3 as u64))
			.saturating_add(RocksDbWeight::get().writes(3 as u64))
	}
	// Storage: Nis ActiveTotal (r:1 w:1)
	// Storage: Nis QueueTotals (r:1 w:1)
	// Storage: Nis Queues (r:1 w:1)
	// Storage: Nis Active (r:0 w:1)
	fn process_bid() -> Weight {
		Weight::from_ref_time(14_944_000 as u64)
			// Standard Error: 6_000
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
}
