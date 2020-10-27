// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Weights for frame_system
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-10-27, STEPS: [50, ], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=frame_system
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/system/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for frame_system.
pub trait WeightInfo {
	fn remark(_b: u32, ) -> Weight;
	fn set_heap_pages() -> Weight;
	fn set_changes_trie_config() -> Weight;
	fn set_storage(_i: u32, ) -> Weight;
	fn kill_storage(_i: u32, ) -> Weight;
	fn kill_prefix(_p: u32, ) -> Weight;
	fn suicide() -> Weight;

}

/// Weights for frame_system using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: crate::Trait> WeightInfo for SubstrateWeight<T> {
	fn remark(_b: u32, ) -> Weight {
		(1_906_000 as Weight)

	}
	fn set_heap_pages() -> Weight {
		(2_792_000 as Weight)
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn set_changes_trie_config() -> Weight {
		(12_029_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}
	fn set_storage(i: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((842_000 as Weight).saturating_mul(i as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(i as Weight)))
	}
	fn kill_storage(i: u32, ) -> Weight {
		(1_120_000 as Weight)
			.saturating_add((599_000 as Weight).saturating_mul(i as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(i as Weight)))
	}
	fn kill_prefix(p: u32, ) -> Weight {
		(9_470_000 as Weight)
			.saturating_add((861_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn suicide() -> Weight {
		(38_469_000 as Weight)

	}

}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn remark(_b: u32, ) -> Weight {
		(1_906_000 as Weight)

	}
	fn set_heap_pages() -> Weight {
		(2_792_000 as Weight)
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn set_changes_trie_config() -> Weight {
		(12_029_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}
	fn set_storage(i: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((842_000 as Weight).saturating_mul(i as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(i as Weight)))
	}
	fn kill_storage(i: u32, ) -> Weight {
		(1_120_000 as Weight)
			.saturating_add((599_000 as Weight).saturating_mul(i as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(i as Weight)))
	}
	fn kill_prefix(p: u32, ) -> Weight {
		(9_470_000 as Weight)
			.saturating_add((861_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn suicide() -> Weight {
		(38_469_000 as Weight)

	}

}
