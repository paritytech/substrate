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

//! Autogenerated weights for pallet_session
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
// --pallet=pallet_session
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --template=./.maintain/frame-weight-template.hbs
// --output=./frame/session/src/weights.rs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_session.
pub trait WeightInfo {
	fn set_keys() -> Weight;
	fn purge_keys() -> Weight;
}

/// Weights for pallet_session using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Session NextKeys (r:1 w:1)
	// Storage: Session KeyOwner (r:4 w:4)
	fn set_keys() -> Weight {
		(48_484_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(5 as Weight))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Session NextKeys (r:1 w:1)
	// Storage: Session KeyOwner (r:0 w:4)
	fn purge_keys() -> Weight {
		(38_003_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(5 as Weight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Session NextKeys (r:1 w:1)
	// Storage: Session KeyOwner (r:4 w:4)
	fn set_keys() -> Weight {
		(48_484_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Session NextKeys (r:1 w:1)
	// Storage: Session KeyOwner (r:0 w:4)
	fn purge_keys() -> Weight {
		(38_003_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
	}
}
