// This file is part of Substrate.

// Copyright (C) 2022-2023 Parity Technologies (UK) Ltd.
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

//! Autogenerated weights for pallet_election_provider_support_benchmarking
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-04-23, STEPS: `1`, REPEAT: 1, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// target/release/substrate
// benchmark
// pallet
// --chain=dev
// --steps=1
// --repeat=1
// --pallet=pallet_election_provider_support_benchmarking
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=frame/election-provider-support/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_election_provider_support_benchmarking.
pub trait WeightInfo {
	fn phragmen(v: u32, t: u32, d: u32, ) -> Weight;
	fn phragmms(v: u32, t: u32, d: u32, ) -> Weight;
}

/// Weights for pallet_election_provider_support_benchmarking using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	fn phragmen(v: u32, t: u32, d: u32, ) -> Weight {
		Weight::from_ref_time(0 as u64)
			// Standard Error: 667_000
			.saturating_add(Weight::from_ref_time(32_973_000 as u64).saturating_mul(v as u64))
			// Standard Error: 1_334_000
			.saturating_add(Weight::from_ref_time(1_334_000 as u64).saturating_mul(t as u64))
			// Standard Error: 60_644_000
			.saturating_add(Weight::from_ref_time(2_636_364_000 as u64).saturating_mul(d as u64))
	}
	fn phragmms(v: u32, t: u32, d: u32, ) -> Weight {
		Weight::from_ref_time(0 as u64)
			// Standard Error: 73_000
			.saturating_add(Weight::from_ref_time(21_073_000 as u64).saturating_mul(v as u64))
			// Standard Error: 146_000
			.saturating_add(Weight::from_ref_time(65_000 as u64).saturating_mul(t as u64))
			// Standard Error: 6_649_000
			.saturating_add(Weight::from_ref_time(1_711_424_000 as u64).saturating_mul(d as u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn phragmen(v: u32, t: u32, d: u32, ) -> Weight {
		Weight::from_ref_time(0 as u64)
			// Standard Error: 667_000
			.saturating_add(Weight::from_ref_time(32_973_000 as u64).saturating_mul(v as u64))
			// Standard Error: 1_334_000
			.saturating_add(Weight::from_ref_time(1_334_000 as u64).saturating_mul(t as u64))
			// Standard Error: 60_644_000
			.saturating_add(Weight::from_ref_time(2_636_364_000 as u64).saturating_mul(d as u64))
	}
	fn phragmms(v: u32, t: u32, d: u32, ) -> Weight {
		Weight::from_ref_time(0 as u64)
			// Standard Error: 73_000
			.saturating_add(Weight::from_ref_time(21_073_000 as u64).saturating_mul(v as u64))
			// Standard Error: 146_000
			.saturating_add(Weight::from_ref_time(65_000 as u64).saturating_mul(t as u64))
			// Standard Error: 6_649_000
			.saturating_add(Weight::from_ref_time(1_711_424_000 as u64).saturating_mul(d as u64))
	}
}
