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

//! Autogenerated weights for pallet_multisig
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-04-17, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `runner-yu9ayb4d-project-145-concurrent-0`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_multisig
// --no-storage-info
// --no-median-slopes
// --no-min-squares
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/multisig/src/weights.rs
// --header=./HEADER-APACHE2
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use core::marker::PhantomData;

/// Weight functions needed for pallet_multisig.
pub trait WeightInfo {
	fn as_multi_threshold_1(z: u32, ) -> Weight;
	fn as_multi_create(s: u32, z: u32, ) -> Weight;
	fn as_multi_approve(s: u32, z: u32, ) -> Weight;
	fn as_multi_complete(s: u32, z: u32, ) -> Weight;
	fn approve_as_multi_create(s: u32, ) -> Weight;
	fn approve_as_multi_approve(s: u32, ) -> Weight;
	fn cancel_as_multi(s: u32, ) -> Weight;
}

/// Weights for pallet_multisig using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// The range of component `z` is `[0, 10000]`.
	fn as_multi_threshold_1(z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 14_658_000 picoseconds.
		Weight::from_parts(15_399_776, 0)
			// Standard Error: 3
			.saturating_add(Weight::from_parts(600, 0).saturating_mul(z.into()))
	}
	/// Storage: Multisig Multisigs (r:1 w:1)
	/// Proof: Multisig Multisigs (max_values: None, max_size: Some(3346), added: 5821, mode: MaxEncodedLen)
	/// The range of component `s` is `[2, 100]`.
	/// The range of component `z` is `[0, 10000]`.
	fn as_multi_create(s: u32, z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `301 + s * (2 ±0)`
		//  Estimated: `6811`
		// Minimum execution time: 48_599_000 picoseconds.
		Weight::from_parts(38_674_212, 6811)
			// Standard Error: 829
			.saturating_add(Weight::from_parts(121_256, 0).saturating_mul(s.into()))
			// Standard Error: 8
			.saturating_add(Weight::from_parts(1_506, 0).saturating_mul(z.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Multisig Multisigs (r:1 w:1)
	/// Proof: Multisig Multisigs (max_values: None, max_size: Some(3346), added: 5821, mode: MaxEncodedLen)
	/// The range of component `s` is `[3, 100]`.
	/// The range of component `z` is `[0, 10000]`.
	fn as_multi_approve(s: u32, z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `320`
		//  Estimated: `6811`
		// Minimum execution time: 31_791_000 picoseconds.
		Weight::from_parts(21_647_982, 6811)
			// Standard Error: 564
			.saturating_add(Weight::from_parts(115_975, 0).saturating_mul(s.into()))
			// Standard Error: 5
			.saturating_add(Weight::from_parts(1_563, 0).saturating_mul(z.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Multisig Multisigs (r:1 w:1)
	/// Proof: Multisig Multisigs (max_values: None, max_size: Some(3346), added: 5821, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `s` is `[2, 100]`.
	/// The range of component `z` is `[0, 10000]`.
	fn as_multi_complete(s: u32, z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `426 + s * (33 ±0)`
		//  Estimated: `6811`
		// Minimum execution time: 55_226_000 picoseconds.
		Weight::from_parts(41_926_683, 6811)
			// Standard Error: 1_175
			.saturating_add(Weight::from_parts(148_708, 0).saturating_mul(s.into()))
			// Standard Error: 11
			.saturating_add(Weight::from_parts(1_633, 0).saturating_mul(z.into()))
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: Multisig Multisigs (r:1 w:1)
	/// Proof: Multisig Multisigs (max_values: None, max_size: Some(3346), added: 5821, mode: MaxEncodedLen)
	/// The range of component `s` is `[2, 100]`.
	fn approve_as_multi_create(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `301 + s * (2 ±0)`
		//  Estimated: `6811`
		// Minimum execution time: 35_628_000 picoseconds.
		Weight::from_parts(37_320_940, 6811)
			// Standard Error: 1_054
			.saturating_add(Weight::from_parts(116_620, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Multisig Multisigs (r:1 w:1)
	/// Proof: Multisig Multisigs (max_values: None, max_size: Some(3346), added: 5821, mode: MaxEncodedLen)
	/// The range of component `s` is `[2, 100]`.
	fn approve_as_multi_approve(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `320`
		//  Estimated: `6811`
		// Minimum execution time: 20_097_000 picoseconds.
		Weight::from_parts(21_027_596, 6811)
			// Standard Error: 693
			.saturating_add(Weight::from_parts(107_442, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Multisig Multisigs (r:1 w:1)
	/// Proof: Multisig Multisigs (max_values: None, max_size: Some(3346), added: 5821, mode: MaxEncodedLen)
	/// The range of component `s` is `[2, 100]`.
	fn cancel_as_multi(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `492 + s * (1 ±0)`
		//  Estimated: `6811`
		// Minimum execution time: 36_259_000 picoseconds.
		Weight::from_parts(37_892_418, 6811)
			// Standard Error: 1_030
			.saturating_add(Weight::from_parts(124_624, 0).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// The range of component `z` is `[0, 10000]`.
	fn as_multi_threshold_1(z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 14_658_000 picoseconds.
		Weight::from_parts(15_399_776, 0)
			// Standard Error: 3
			.saturating_add(Weight::from_parts(600, 0).saturating_mul(z.into()))
	}
	/// Storage: Multisig Multisigs (r:1 w:1)
	/// Proof: Multisig Multisigs (max_values: None, max_size: Some(3346), added: 5821, mode: MaxEncodedLen)
	/// The range of component `s` is `[2, 100]`.
	/// The range of component `z` is `[0, 10000]`.
	fn as_multi_create(s: u32, z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `301 + s * (2 ±0)`
		//  Estimated: `6811`
		// Minimum execution time: 48_599_000 picoseconds.
		Weight::from_parts(38_674_212, 6811)
			// Standard Error: 829
			.saturating_add(Weight::from_parts(121_256, 0).saturating_mul(s.into()))
			// Standard Error: 8
			.saturating_add(Weight::from_parts(1_506, 0).saturating_mul(z.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Multisig Multisigs (r:1 w:1)
	/// Proof: Multisig Multisigs (max_values: None, max_size: Some(3346), added: 5821, mode: MaxEncodedLen)
	/// The range of component `s` is `[3, 100]`.
	/// The range of component `z` is `[0, 10000]`.
	fn as_multi_approve(s: u32, z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `320`
		//  Estimated: `6811`
		// Minimum execution time: 31_791_000 picoseconds.
		Weight::from_parts(21_647_982, 6811)
			// Standard Error: 564
			.saturating_add(Weight::from_parts(115_975, 0).saturating_mul(s.into()))
			// Standard Error: 5
			.saturating_add(Weight::from_parts(1_563, 0).saturating_mul(z.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Multisig Multisigs (r:1 w:1)
	/// Proof: Multisig Multisigs (max_values: None, max_size: Some(3346), added: 5821, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `s` is `[2, 100]`.
	/// The range of component `z` is `[0, 10000]`.
	fn as_multi_complete(s: u32, z: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `426 + s * (33 ±0)`
		//  Estimated: `6811`
		// Minimum execution time: 55_226_000 picoseconds.
		Weight::from_parts(41_926_683, 6811)
			// Standard Error: 1_175
			.saturating_add(Weight::from_parts(148_708, 0).saturating_mul(s.into()))
			// Standard Error: 11
			.saturating_add(Weight::from_parts(1_633, 0).saturating_mul(z.into()))
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: Multisig Multisigs (r:1 w:1)
	/// Proof: Multisig Multisigs (max_values: None, max_size: Some(3346), added: 5821, mode: MaxEncodedLen)
	/// The range of component `s` is `[2, 100]`.
	fn approve_as_multi_create(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `301 + s * (2 ±0)`
		//  Estimated: `6811`
		// Minimum execution time: 35_628_000 picoseconds.
		Weight::from_parts(37_320_940, 6811)
			// Standard Error: 1_054
			.saturating_add(Weight::from_parts(116_620, 0).saturating_mul(s.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Multisig Multisigs (r:1 w:1)
	/// Proof: Multisig Multisigs (max_values: None, max_size: Some(3346), added: 5821, mode: MaxEncodedLen)
	/// The range of component `s` is `[2, 100]`.
	fn approve_as_multi_approve(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `320`
		//  Estimated: `6811`
		// Minimum execution time: 20_097_000 picoseconds.
		Weight::from_parts(21_027_596, 6811)
			// Standard Error: 693
			.saturating_add(Weight::from_parts(107_442, 0).saturating_mul(s.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Multisig Multisigs (r:1 w:1)
	/// Proof: Multisig Multisigs (max_values: None, max_size: Some(3346), added: 5821, mode: MaxEncodedLen)
	/// The range of component `s` is `[2, 100]`.
	fn cancel_as_multi(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `492 + s * (1 ±0)`
		//  Estimated: `6811`
		// Minimum execution time: 36_259_000 picoseconds.
		Weight::from_parts(37_892_418, 6811)
			// Standard Error: 1_030
			.saturating_add(Weight::from_parts(124_624, 0).saturating_mul(s.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
}
