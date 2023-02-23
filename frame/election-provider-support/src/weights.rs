// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

//! Autogenerated weights for frame_election_provider_support
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-02-22, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `runner-ehxwxxsd-project-145-concurrent-0`, CPU: `Intel(R) Xeon(R) CPU @ 2.60GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// target/production/substrate
// benchmark
// pallet
// --steps=50
// --repeat=20
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --json-file=/builds/parity/mirrors/substrate/.git/.artifacts/bench.json
// --pallet=frame_election_provider_support
// --chain=dev
// --header=./HEADER-APACHE2
// --output=./frame/election-provider-support/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for frame_election_provider_support.
pub trait WeightInfo {
	fn phragmen(v: u32, t: u32, d: u32, ) -> Weight;
	fn phragmms(v: u32, t: u32, d: u32, ) -> Weight;
	fn approval_voting(v: u32, t: u32, d: u32, ) -> Weight;
}

/// Weights for frame_election_provider_support using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// The range of component `v` is `[1000, 2000]`.
	/// The range of component `t` is `[500, 1000]`.
	/// The range of component `d` is `[5, 16]`.
	fn phragmen(v: u32, _t: u32, d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_789_174 nanoseconds.
		Weight::from_ref_time(5_826_449_000)
			.saturating_add(Weight::from_proof_size(0))
			// Standard Error: 130_342
			.saturating_add(Weight::from_ref_time(5_332_741).saturating_mul(v.into()))
			// Standard Error: 13_325_769
			.saturating_add(Weight::from_ref_time(1_416_874_101).saturating_mul(d.into()))
	}
	/// The range of component `v` is `[1000, 2000]`.
	/// The range of component `t` is `[500, 1000]`.
	/// The range of component `d` is `[5, 16]`.
	fn phragmms(v: u32, _t: u32, d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 4_151_790 nanoseconds.
		Weight::from_ref_time(4_215_936_000)
			.saturating_add(Weight::from_proof_size(0))
			// Standard Error: 125_135
			.saturating_add(Weight::from_ref_time(4_730_609).saturating_mul(v.into()))
			// Standard Error: 12_793_390
			.saturating_add(Weight::from_ref_time(1_474_383_961).saturating_mul(d.into()))
	}
	/// The range of component `v` is `[1000, 2000]`.
	/// The range of component `t` is `[500, 1000]`.
	/// The range of component `d` is `[5, 16]`.
	fn approval_voting(v: u32, _t: u32, d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 1_800_445 nanoseconds.
		Weight::from_ref_time(1_824_645_000)
			.saturating_add(Weight::from_proof_size(0))
			// Standard Error: 26_266
			.saturating_add(Weight::from_ref_time(1_229_576).saturating_mul(v.into()))
			// Standard Error: 2_685_343
			.saturating_add(Weight::from_ref_time(213_080_804).saturating_mul(d.into()))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// The range of component `v` is `[1000, 2000]`.
	/// The range of component `t` is `[500, 1000]`.
	/// The range of component `d` is `[5, 16]`.
	fn phragmen(v: u32, _t: u32, d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_789_174 nanoseconds.
		Weight::from_ref_time(5_826_449_000)
			.saturating_add(Weight::from_proof_size(0))
			// Standard Error: 130_342
			.saturating_add(Weight::from_ref_time(5_332_741).saturating_mul(v.into()))
			// Standard Error: 13_325_769
			.saturating_add(Weight::from_ref_time(1_416_874_101).saturating_mul(d.into()))
	}
	/// The range of component `v` is `[1000, 2000]`.
	/// The range of component `t` is `[500, 1000]`.
	/// The range of component `d` is `[5, 16]`.
	fn phragmms(v: u32, _t: u32, d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 4_151_790 nanoseconds.
		Weight::from_ref_time(4_215_936_000)
			.saturating_add(Weight::from_proof_size(0))
			// Standard Error: 125_135
			.saturating_add(Weight::from_ref_time(4_730_609).saturating_mul(v.into()))
			// Standard Error: 12_793_390
			.saturating_add(Weight::from_ref_time(1_474_383_961).saturating_mul(d.into()))
	}
	/// The range of component `v` is `[1000, 2000]`.
	/// The range of component `t` is `[500, 1000]`.
	/// The range of component `d` is `[5, 16]`.
	fn approval_voting(v: u32, _t: u32, d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 1_800_445 nanoseconds.
		Weight::from_ref_time(1_824_645_000)
			.saturating_add(Weight::from_proof_size(0))
			// Standard Error: 26_266
			.saturating_add(Weight::from_ref_time(1_229_576).saturating_mul(v.into()))
			// Standard Error: 2_685_343
			.saturating_add(Weight::from_ref_time(213_080_804).saturating_mul(d.into()))
	}
}
