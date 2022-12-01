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

//! Autogenerated weights for pallet_utility
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2021-08-07, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_utility
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/utility/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_utility.
pub trait WeightInfo {
	fn batch(c: u32, ) -> Weight;
	fn as_derivative() -> Weight;
	fn batch_all(c: u32, ) -> Weight;
}

/// Weights for pallet_utility using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	fn batch(c: u32, ) -> Weight {
		(30_319_000 as Weight)
			// Standard Error: 3_000
			.saturating_add((6_759_000 as Weight).saturating_mul(c as Weight))
	}
	fn as_derivative() -> Weight {
		(4_030_000 as Weight)
	}
	fn batch_all(c: u32, ) -> Weight {
		(26_621_000 as Weight)
			// Standard Error: 3_000
			.saturating_add((7_251_000 as Weight).saturating_mul(c as Weight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn batch(c: u32, ) -> Weight {
		(30_319_000 as Weight)
			// Standard Error: 3_000
			.saturating_add((6_759_000 as Weight).saturating_mul(c as Weight))
	}
	fn as_derivative() -> Weight {
		(4_030_000 as Weight)
	}
	fn batch_all(c: u32, ) -> Weight {
		(26_621_000 as Weight)
			// Standard Error: 3_000
			.saturating_add((7_251_000 as Weight).saturating_mul(c as Weight))
	}
}
