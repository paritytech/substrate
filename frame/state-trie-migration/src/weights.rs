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

//! Autogenerated weights for pallet_state_trie_migration
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-05-24, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_state_trie_migration
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --template=./.maintain/frame-weight-template.hbs
// --output=./frame/state-trie-migration/src/weights.rs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{RefTimeWeight, Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_state_trie_migration.
pub trait WeightInfo {
	fn continue_migrate() -> Weight;
	fn continue_migrate_wrong_witness() -> Weight;
	fn migrate_custom_top_success() -> Weight;
	fn migrate_custom_top_fail() -> Weight;
	fn migrate_custom_child_success() -> Weight;
	fn migrate_custom_child_fail() -> Weight;
	fn process_top_key(v: u32, ) -> Weight;
}

/// Weights for pallet_state_trie_migration using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: StateTrieMigration SignedMigrationMaxLimits (r:1 w:0)
	// Storage: StateTrieMigration MigrationProcess (r:1 w:1)
	fn continue_migrate() -> Weight {
		Weight::from_ref_time(19_019_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: StateTrieMigration SignedMigrationMaxLimits (r:1 w:0)
	fn continue_migrate_wrong_witness() -> Weight {
		Weight::from_ref_time(1_874_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
	}
	fn migrate_custom_top_success() -> Weight {
		Weight::from_ref_time(16_381_000 as RefTimeWeight)
	}
	// Storage: unknown [0x666f6f] (r:1 w:1)
	fn migrate_custom_top_fail() -> Weight {
		Weight::from_ref_time(25_966_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
	fn migrate_custom_child_success() -> Weight {
		Weight::from_ref_time(16_712_000 as RefTimeWeight)
	}
	// Storage: unknown [0x666f6f] (r:1 w:1)
	fn migrate_custom_child_fail() -> Weight {
		Weight::from_ref_time(29_885_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: unknown [0x6b6579] (r:1 w:1)
	fn process_top_key(v: u32, ) -> Weight {
		Weight::from_ref_time(0 as RefTimeWeight)
			// Standard Error: 0
			.saturating_add(Weight::from_ref_time(2_000 as RefTimeWeight).saturating_mul(v as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: StateTrieMigration SignedMigrationMaxLimits (r:1 w:0)
	// Storage: StateTrieMigration MigrationProcess (r:1 w:1)
	fn continue_migrate() -> Weight {
		Weight::from_ref_time(19_019_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: StateTrieMigration SignedMigrationMaxLimits (r:1 w:0)
	fn continue_migrate_wrong_witness() -> Weight {
		Weight::from_ref_time(1_874_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
	}
	fn migrate_custom_top_success() -> Weight {
		Weight::from_ref_time(16_381_000 as RefTimeWeight)
	}
	// Storage: unknown [0x666f6f] (r:1 w:1)
	fn migrate_custom_top_fail() -> Weight {
		Weight::from_ref_time(25_966_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
	fn migrate_custom_child_success() -> Weight {
		Weight::from_ref_time(16_712_000 as RefTimeWeight)
	}
	// Storage: unknown [0x666f6f] (r:1 w:1)
	fn migrate_custom_child_fail() -> Weight {
		Weight::from_ref_time(29_885_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: unknown [0x6b6579] (r:1 w:1)
	fn process_top_key(v: u32, ) -> Weight {
		Weight::from_ref_time(0 as RefTimeWeight)
			// Standard Error: 0
			.saturating_add(Weight::from_ref_time(2_000 as RefTimeWeight).saturating_mul(v as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
}
