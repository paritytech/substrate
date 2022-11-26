// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Autogenerated weights for pallet_tips
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-11-07, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! HOSTNAME: `bm2`, CPU: `Intel(R) Core(TM) i7-7700K CPU @ 4.20GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_tips
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/tips/src/weights.rs
// --header=./HEADER-APACHE2
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_tips.
pub trait WeightInfo {
	fn report_awesome(r: u32, ) -> Weight;
	fn retract_tip() -> Weight;
	fn tip_new(r: u32, t: u32, ) -> Weight;
	fn tip(t: u32, ) -> Weight;
	fn close_tip(t: u32, ) -> Weight;
	fn slash_tip(t: u32, ) -> Weight;
}

/// Weights for pallet_tips using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: Tips Reasons (r:1 w:1)
	// Storage: Tips Tips (r:1 w:1)
	/// The range of component `r` is `[0, 300]`.
	fn report_awesome(r: u32, ) -> Weight {
		// Minimum execution time: 35_458 nanoseconds.
		Weight::from_ref_time(36_920_009 as u64)
			// Standard Error: 252
			.saturating_add(Weight::from_ref_time(1_835 as u64).saturating_mul(r as u64))
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: Tips Tips (r:1 w:1)
	// Storage: Tips Reasons (r:0 w:1)
	fn retract_tip() -> Weight {
		// Minimum execution time: 34_322 nanoseconds.
		Weight::from_ref_time(35_292_000 as u64)
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: Elections Members (r:1 w:0)
	// Storage: Tips Reasons (r:1 w:1)
	// Storage: Tips Tips (r:0 w:1)
	/// The range of component `r` is `[0, 300]`.
	/// The range of component `t` is `[1, 13]`.
	fn tip_new(r: u32, t: u32, ) -> Weight {
		// Minimum execution time: 26_691 nanoseconds.
		Weight::from_ref_time(27_313_497 as u64)
			// Standard Error: 141
			.saturating_add(Weight::from_ref_time(818 as u64).saturating_mul(r as u64))
			// Standard Error: 3_352
			.saturating_add(Weight::from_ref_time(108_557 as u64).saturating_mul(t as u64))
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
	// Storage: Elections Members (r:1 w:0)
	// Storage: Tips Tips (r:1 w:1)
	/// The range of component `t` is `[1, 13]`.
	fn tip(t: u32, ) -> Weight {
		// Minimum execution time: 17_464 nanoseconds.
		Weight::from_ref_time(17_621_090 as u64)
			// Standard Error: 3_702
			.saturating_add(Weight::from_ref_time(269_919 as u64).saturating_mul(t as u64))
			.saturating_add(T::DbWeight::get().reads(2 as u64))
			.saturating_add(T::DbWeight::get().writes(1 as u64))
	}
	// Storage: Tips Tips (r:1 w:1)
	// Storage: Elections Members (r:1 w:0)
	// Storage: System Account (r:1 w:1)
	// Storage: Tips Reasons (r:0 w:1)
	/// The range of component `t` is `[1, 13]`.
	fn close_tip(t: u32, ) -> Weight {
		// Minimum execution time: 52_221 nanoseconds.
		Weight::from_ref_time(53_168_303 as u64)
			// Standard Error: 6_591
			.saturating_add(Weight::from_ref_time(243_706 as u64).saturating_mul(t as u64))
			.saturating_add(T::DbWeight::get().reads(3 as u64))
			.saturating_add(T::DbWeight::get().writes(3 as u64))
	}
	// Storage: Tips Tips (r:1 w:1)
	// Storage: Tips Reasons (r:0 w:1)
	/// The range of component `t` is `[1, 13]`.
	fn slash_tip(t: u32, ) -> Weight {
		// Minimum execution time: 22_911 nanoseconds.
		Weight::from_ref_time(23_750_488 as u64)
			// Standard Error: 2_561
			.saturating_add(Weight::from_ref_time(12_282 as u64).saturating_mul(t as u64))
			.saturating_add(T::DbWeight::get().reads(1 as u64))
			.saturating_add(T::DbWeight::get().writes(2 as u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: Tips Reasons (r:1 w:1)
	// Storage: Tips Tips (r:1 w:1)
	/// The range of component `r` is `[0, 300]`.
	fn report_awesome(r: u32, ) -> Weight {
		// Minimum execution time: 35_458 nanoseconds.
		Weight::from_ref_time(36_920_009 as u64)
			// Standard Error: 252
			.saturating_add(Weight::from_ref_time(1_835 as u64).saturating_mul(r as u64))
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	// Storage: Tips Tips (r:1 w:1)
	// Storage: Tips Reasons (r:0 w:1)
	fn retract_tip() -> Weight {
		// Minimum execution time: 34_322 nanoseconds.
		Weight::from_ref_time(35_292_000 as u64)
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	// Storage: Elections Members (r:1 w:0)
	// Storage: Tips Reasons (r:1 w:1)
	// Storage: Tips Tips (r:0 w:1)
	/// The range of component `r` is `[0, 300]`.
	/// The range of component `t` is `[1, 13]`.
	fn tip_new(r: u32, t: u32, ) -> Weight {
		// Minimum execution time: 26_691 nanoseconds.
		Weight::from_ref_time(27_313_497 as u64)
			// Standard Error: 141
			.saturating_add(Weight::from_ref_time(818 as u64).saturating_mul(r as u64))
			// Standard Error: 3_352
			.saturating_add(Weight::from_ref_time(108_557 as u64).saturating_mul(t as u64))
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
	// Storage: Elections Members (r:1 w:0)
	// Storage: Tips Tips (r:1 w:1)
	/// The range of component `t` is `[1, 13]`.
	fn tip(t: u32, ) -> Weight {
		// Minimum execution time: 17_464 nanoseconds.
		Weight::from_ref_time(17_621_090 as u64)
			// Standard Error: 3_702
			.saturating_add(Weight::from_ref_time(269_919 as u64).saturating_mul(t as u64))
			.saturating_add(RocksDbWeight::get().reads(2 as u64))
			.saturating_add(RocksDbWeight::get().writes(1 as u64))
	}
	// Storage: Tips Tips (r:1 w:1)
	// Storage: Elections Members (r:1 w:0)
	// Storage: System Account (r:1 w:1)
	// Storage: Tips Reasons (r:0 w:1)
	/// The range of component `t` is `[1, 13]`.
	fn close_tip(t: u32, ) -> Weight {
		// Minimum execution time: 52_221 nanoseconds.
		Weight::from_ref_time(53_168_303 as u64)
			// Standard Error: 6_591
			.saturating_add(Weight::from_ref_time(243_706 as u64).saturating_mul(t as u64))
			.saturating_add(RocksDbWeight::get().reads(3 as u64))
			.saturating_add(RocksDbWeight::get().writes(3 as u64))
	}
	// Storage: Tips Tips (r:1 w:1)
	// Storage: Tips Reasons (r:0 w:1)
	/// The range of component `t` is `[1, 13]`.
	fn slash_tip(t: u32, ) -> Weight {
		// Minimum execution time: 22_911 nanoseconds.
		Weight::from_ref_time(23_750_488 as u64)
			// Standard Error: 2_561
			.saturating_add(Weight::from_ref_time(12_282 as u64).saturating_mul(t as u64))
			.saturating_add(RocksDbWeight::get().reads(1 as u64))
			.saturating_add(RocksDbWeight::get().writes(2 as u64))
	}
}
