// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Autogenerated weights for pallet_example_basic
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-10-09, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! HOSTNAME: `Shawns-MacBook-Pro.local`, CPU: `<UNKNOWN>`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/release/substrate
// benchmark
// pallet
// --chain=dev
// --execution=wasm
// --wasm-execution=compiled
// --pallet=pallet_example_basic
// --extrinsic=*
// --steps=50
// --repeat=20
// --output=./
// --template
// ./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_example_basic.
pub trait WeightInfo {
	/// Calculates the weight for `set_dummy`.
	fn set_dummy_benchmark() -> Weight;
	/// Calculates the weight for `accumulate_dummy`.
	fn accumulate_dummy() -> Weight;
	/// Calculates the weight for `sort_vector`.
	fn sort_vector(x: u32, ) -> Weight;
}

/// Weights for pallet_example_basic using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: BasicExample Dummy (r:0 w:1)
	fn set_dummy_benchmark() -> Weight {
		Weight::from_parts(19_000_000 as u64, 0)
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: BasicExample Dummy (r:1 w:1)
	fn accumulate_dummy() -> Weight {
		Weight::from_parts(18_000_000 as u64, 0)
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	/// The range of component `x` is `[0, 10000]`.
	fn sort_vector(x: u32, ) -> Weight {
		Weight::from_parts(0 as u64, 0)
			// Standard Error: 2
			.saturating_add(Weight::from_parts(520 as u64, 0).saturating_mul(x as u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: BasicExample Dummy (r:0 w:1)
	fn set_dummy_benchmark() -> Weight {
		Weight::from_parts(19_000_000 as u64, 0)
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	// Storage: BasicExample Dummy (r:1 w:1)
	fn accumulate_dummy() -> Weight {
		Weight::from_parts(18_000_000 as u64, 0)
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	/// The range of component `x` is `[0, 10000]`.
	fn sort_vector(x: u32, ) -> Weight {
		Weight::from_parts(0 as u64, 0)
			// Standard Error: 2
			.saturating_add(Weight::from_parts(520 as u64, 0).saturating_mul(x as u64))
	}
}
