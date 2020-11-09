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

//! Weights for pallet_multisig
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-10-27, STEPS: [50, ], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_multisig
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/multisig/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_multisig.
pub trait WeightInfo {
	fn as_multi_threshold_1(z: u32, ) -> Weight;
	fn as_multi_create(s: u32, z: u32, ) -> Weight;
	fn as_multi_create_store(s: u32, z: u32, ) -> Weight;
	fn as_multi_approve(s: u32, z: u32, ) -> Weight;
	fn as_multi_approve_store(s: u32, z: u32, ) -> Weight;
	fn as_multi_complete(s: u32, z: u32, ) -> Weight;
	fn approve_as_multi_create(s: u32, ) -> Weight;
	fn approve_as_multi_approve(s: u32, ) -> Weight;
	fn approve_as_multi_complete(s: u32, ) -> Weight;
	fn cancel_as_multi(s: u32, ) -> Weight;
	
}

/// Weights for pallet_multisig using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Trait> WeightInfo for SubstrateWeight<T> {
	fn as_multi_threshold_1(z: u32, ) -> Weight {
		(14_183_000 as Weight)
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
			
	}
	fn as_multi_create(s: u32, z: u32, ) -> Weight {
		(72_350_000 as Weight)
			.saturating_add((64_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn as_multi_create_store(s: u32, z: u32, ) -> Weight {
		(83_175_000 as Weight)
			.saturating_add((72_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn as_multi_approve(s: u32, z: u32, ) -> Weight {
		(43_035_000 as Weight)
			.saturating_add((140_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn as_multi_approve_store(s: u32, z: u32, ) -> Weight {
		(75_190_000 as Weight)
			.saturating_add((127_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn as_multi_complete(s: u32, z: u32, ) -> Weight {
		(92_751_000 as Weight)
			.saturating_add((282_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((5_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
			
	}
	fn approve_as_multi_create(s: u32, ) -> Weight {
		(71_937_000 as Weight)
			.saturating_add((87_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn approve_as_multi_approve(s: u32, ) -> Weight {
		(44_294_000 as Weight)
			.saturating_add((89_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn approve_as_multi_complete(s: u32, ) -> Weight {
		(163_098_000 as Weight)
			.saturating_add((276_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
			
	}
	fn cancel_as_multi(s: u32, ) -> Weight {
		(115_731_000 as Weight)
			.saturating_add((104_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn as_multi_threshold_1(z: u32, ) -> Weight {
		(14_183_000 as Weight)
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
			
	}
	fn as_multi_create(s: u32, z: u32, ) -> Weight {
		(72_350_000 as Weight)
			.saturating_add((64_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn as_multi_create_store(s: u32, z: u32, ) -> Weight {
		(83_175_000 as Weight)
			.saturating_add((72_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn as_multi_approve(s: u32, z: u32, ) -> Weight {
		(43_035_000 as Weight)
			.saturating_add((140_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn as_multi_approve_store(s: u32, z: u32, ) -> Weight {
		(75_190_000 as Weight)
			.saturating_add((127_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((3_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn as_multi_complete(s: u32, z: u32, ) -> Weight {
		(92_751_000 as Weight)
			.saturating_add((282_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((5_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			
	}
	fn approve_as_multi_create(s: u32, ) -> Weight {
		(71_937_000 as Weight)
			.saturating_add((87_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn approve_as_multi_approve(s: u32, ) -> Weight {
		(44_294_000 as Weight)
			.saturating_add((89_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn approve_as_multi_complete(s: u32, ) -> Weight {
		(163_098_000 as Weight)
			.saturating_add((276_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			
	}
	fn cancel_as_multi(s: u32, ) -> Weight {
		(115_731_000 as Weight)
			.saturating_add((104_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	
}
