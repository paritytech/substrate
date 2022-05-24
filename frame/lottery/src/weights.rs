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

//! Autogenerated weights for pallet_lottery
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-05-22, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_lottery
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --template=./.maintain/frame-weight-template.hbs
// --output=./frame/lottery/src/weights.rs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_lottery.
pub trait WeightInfo {
	fn buy_ticket() -> Weight;
	fn set_calls(n: u32, ) -> Weight;
	fn start_lottery() -> Weight;
	fn stop_repeat() -> Weight;
	fn on_initialize_end() -> Weight;
	fn on_initialize_repeat() -> Weight;
}

/// Weights for pallet_lottery using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: Lottery Lottery (r:1 w:0)
	// Storage: Lottery CallIndices (r:1 w:0)
	// Storage: Lottery TicketsCount (r:1 w:1)
	// Storage: Lottery Participants (r:1 w:1)
	// Storage: Lottery LotteryIndex (r:1 w:0)
	// Storage: System Account (r:1 w:1)
	// Storage: Lottery Tickets (r:0 w:1)
	fn buy_ticket() -> Weight {
		(39_387_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
	}
	// Storage: Lottery CallIndices (r:0 w:1)
	fn set_calls(n: u32, ) -> Weight {
		(9_353_000 as Weight)
			// Standard Error: 4_000
			.saturating_add((297_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: Lottery Lottery (r:1 w:1)
	// Storage: Lottery LotteryIndex (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn start_lottery() -> Weight {
		(33_157_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	// Storage: Lottery Lottery (r:1 w:1)
	fn stop_repeat() -> Weight {
		(4_015_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	// Storage: RandomnessCollectiveFlip RandomMaterial (r:1 w:0)
	// Storage: Lottery Lottery (r:1 w:1)
	// Storage: System Account (r:2 w:2)
	// Storage: Lottery TicketsCount (r:1 w:1)
	// Storage: Lottery Tickets (r:1 w:0)
	fn on_initialize_end() -> Weight {
		(53_539_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))
	}
	// Storage: RandomnessCollectiveFlip RandomMaterial (r:1 w:0)
	// Storage: Lottery Lottery (r:1 w:1)
	// Storage: System Account (r:2 w:2)
	// Storage: Lottery TicketsCount (r:1 w:1)
	// Storage: Lottery Tickets (r:1 w:0)
	// Storage: Lottery LotteryIndex (r:1 w:1)
	fn on_initialize_repeat() -> Weight {
		(56_103_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(7 as Weight))
			.saturating_add(T::DbWeight::get().writes(5 as Weight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: Lottery Lottery (r:1 w:0)
	// Storage: Lottery CallIndices (r:1 w:0)
	// Storage: Lottery TicketsCount (r:1 w:1)
	// Storage: Lottery Participants (r:1 w:1)
	// Storage: Lottery LotteryIndex (r:1 w:0)
	// Storage: System Account (r:1 w:1)
	// Storage: Lottery Tickets (r:0 w:1)
	fn buy_ticket() -> Weight {
		(39_387_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
	}
	// Storage: Lottery CallIndices (r:0 w:1)
	fn set_calls(n: u32, ) -> Weight {
		(9_353_000 as Weight)
			// Standard Error: 4_000
			.saturating_add((297_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: Lottery Lottery (r:1 w:1)
	// Storage: Lottery LotteryIndex (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn start_lottery() -> Weight {
		(33_157_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	// Storage: Lottery Lottery (r:1 w:1)
	fn stop_repeat() -> Weight {
		(4_015_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	// Storage: RandomnessCollectiveFlip RandomMaterial (r:1 w:0)
	// Storage: Lottery Lottery (r:1 w:1)
	// Storage: System Account (r:2 w:2)
	// Storage: Lottery TicketsCount (r:1 w:1)
	// Storage: Lottery Tickets (r:1 w:0)
	fn on_initialize_end() -> Weight {
		(53_539_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))
	}
	// Storage: RandomnessCollectiveFlip RandomMaterial (r:1 w:0)
	// Storage: Lottery Lottery (r:1 w:1)
	// Storage: System Account (r:2 w:2)
	// Storage: Lottery TicketsCount (r:1 w:1)
	// Storage: Lottery Tickets (r:1 w:0)
	// Storage: Lottery LotteryIndex (r:1 w:1)
	fn on_initialize_repeat() -> Weight {
		(56_103_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(7 as Weight))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
	}
}
