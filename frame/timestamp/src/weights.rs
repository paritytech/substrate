// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Autogenerated weights for pallet_timestamp
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-04-25, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `runner-jcyxhmkk-project-145-concurrent-0`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_timestamp
// --no-storage-info
// --no-median-slopes
// --no-min-squares
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/timestamp/src/weights.rs
// --header=./HEADER-APACHE2
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use core::marker::PhantomData;

/// Weight functions needed for pallet_timestamp.
pub trait WeightInfo {
	fn set() -> Weight;
	fn on_finalize() -> Weight;
}

/// Weights for pallet_timestamp using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: Timestamp Now (r:1 w:1)
	/// Proof: Timestamp Now (max_values: Some(1), max_size: Some(8), added: 503, mode: MaxEncodedLen)
	/// Storage: Babe CurrentSlot (r:1 w:0)
	/// Proof: Babe CurrentSlot (max_values: Some(1), max_size: Some(8), added: 503, mode: MaxEncodedLen)
	fn set() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `312`
		//  Estimated: `1493`
		// Minimum execution time: 10_516_000 picoseconds.
		Weight::from_parts(10_974_000, 1493)
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	fn on_finalize() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `161`
		//  Estimated: `0`
		// Minimum execution time: 4_494_000 picoseconds.
		Weight::from_parts(4_614_000, 0)
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// Storage: Timestamp Now (r:1 w:1)
	/// Proof: Timestamp Now (max_values: Some(1), max_size: Some(8), added: 503, mode: MaxEncodedLen)
	/// Storage: Babe CurrentSlot (r:1 w:0)
	/// Proof: Babe CurrentSlot (max_values: Some(1), max_size: Some(8), added: 503, mode: MaxEncodedLen)
	fn set() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `312`
		//  Estimated: `1493`
		// Minimum execution time: 10_516_000 picoseconds.
		Weight::from_parts(10_974_000, 1493)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	fn on_finalize() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `161`
		//  Estimated: `0`
		// Minimum execution time: 4_494_000 picoseconds.
		Weight::from_parts(4_614_000, 0)
	}
}
