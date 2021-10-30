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

//! Autogenerated weights for frame_benchmarking
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2021-10-30, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=frame_benchmarking
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/benchmarking/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for frame_benchmarking.
pub trait WeightInfo {
	fn addition(i: u32, ) -> Weight;
	fn subtraction(i: u32, ) -> Weight;
	fn multiplication(i: u32, ) -> Weight;
	fn division(i: u32, ) -> Weight;
	fn hashing(i: u32, ) -> Weight;
	fn storage_read(i: u32, ) -> Weight;
	fn storage_write(i: u32, ) -> Weight;
}

/// Weights for frame_benchmarking using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	fn addition(_i: u32, ) -> Weight {
		(342_000 as Weight)
	}
	fn subtraction(_i: u32, ) -> Weight {
		(333_000 as Weight)
	}
	fn multiplication(_i: u32, ) -> Weight {
		(324_000 as Weight)
	}
	fn division(_i: u32, ) -> Weight {
		(325_000 as Weight)
	}
	fn hashing(_i: u32, ) -> Weight {
		(35_101_542_000 as Weight)
	}
	// Storage: Skipped Metadata (r:0 w:0)
	fn storage_read(i: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 4_000
			.saturating_add((2_800_000 as Weight).saturating_mul(i as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(i as Weight)))
	}
	// Storage: Skipped Metadata (r:0 w:0)
	fn storage_write(i: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 0
			.saturating_add((658_000 as Weight).saturating_mul(i as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(i as Weight)))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn addition(_i: u32, ) -> Weight {
		(342_000 as Weight)
	}
	fn subtraction(_i: u32, ) -> Weight {
		(333_000 as Weight)
	}
	fn multiplication(_i: u32, ) -> Weight {
		(324_000 as Weight)
	}
	fn division(_i: u32, ) -> Weight {
		(325_000 as Weight)
	}
	fn hashing(_i: u32, ) -> Weight {
		(35_101_542_000 as Weight)
	}
	// Storage: Skipped Metadata (r:0 w:0)
	fn storage_read(i: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 4_000
			.saturating_add((2_800_000 as Weight).saturating_mul(i as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(i as Weight)))
	}
	// Storage: Skipped Metadata (r:0 w:0)
	fn storage_write(i: u32, ) -> Weight {
		(0 as Weight)
			// Standard Error: 0
			.saturating_add((658_000 as Weight).saturating_mul(i as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(i as Weight)))
	}
}
