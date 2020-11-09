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

//! Weights for pallet_collective
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-10-27, STEPS: [50, ], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_collective
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/collective/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_collective.
pub trait WeightInfo {
	fn set_members(_m: u32, _n: u32, _p: u32, ) -> Weight;
	fn execute(_b: u32, _m: u32, ) -> Weight;
	fn propose_execute(_b: u32, _m: u32, ) -> Weight;
	fn propose_proposed(_b: u32, _m: u32, _p: u32, ) -> Weight;
	fn vote(_m: u32, ) -> Weight;
	fn close_early_disapproved(_m: u32, _p: u32, ) -> Weight;
	fn close_early_approved(_b: u32, _m: u32, _p: u32, ) -> Weight;
	fn close_disapproved(_m: u32, _p: u32, ) -> Weight;
	fn close_approved(_b: u32, _m: u32, _p: u32, ) -> Weight;
	fn disapprove_proposal(_p: u32, ) -> Weight;

}

/// Weights for pallet_collective using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Trait> WeightInfo for SubstrateWeight<T> {
	fn set_members(m: u32, n: u32, p: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((20_933_000 as Weight).saturating_mul(m as Weight))
			.saturating_add((254_000 as Weight).saturating_mul(n as Weight))
			.saturating_add((28_233_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(p as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn execute(b: u32, m: u32, ) -> Weight {
		(31_147_000 as Weight)
			.saturating_add((4_000 as Weight).saturating_mul(b as Weight))
			.saturating_add((115_000 as Weight).saturating_mul(m as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))

	}
	fn propose_execute(b: u32, m: u32, ) -> Weight {
		(38_774_000 as Weight)
			.saturating_add((4_000 as Weight).saturating_mul(b as Weight))
			.saturating_add((226_000 as Weight).saturating_mul(m as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))

	}
	fn propose_proposed(b: u32, m: u32, p: u32, ) -> Weight {
		(64_230_000 as Weight)
			.saturating_add((5_000 as Weight).saturating_mul(b as Weight))
			.saturating_add((138_000 as Weight).saturating_mul(m as Weight))
			.saturating_add((637_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))

	}
	fn vote(m: u32, ) -> Weight {
		(57_051_000 as Weight)
			.saturating_add((220_000 as Weight).saturating_mul(m as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))

	}
	fn close_early_disapproved(m: u32, p: u32, ) -> Weight {
		(61_406_000 as Weight)
			.saturating_add((225_000 as Weight).saturating_mul(m as Weight))
			.saturating_add((630_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn close_early_approved(b: u32, m: u32, p: u32, ) -> Weight {
		(92_864_000 as Weight)
			.saturating_add((1_000 as Weight).saturating_mul(b as Weight))
			.saturating_add((233_000 as Weight).saturating_mul(m as Weight))
			.saturating_add((597_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn close_disapproved(m: u32, p: u32, ) -> Weight {
		(67_942_000 as Weight)
			.saturating_add((232_000 as Weight).saturating_mul(m as Weight))
			.saturating_add((636_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn close_approved(b: u32, m: u32, p: u32, ) -> Weight {
		(99_742_000 as Weight)
			.saturating_add((1_000 as Weight).saturating_mul(b as Weight))
			.saturating_add((233_000 as Weight).saturating_mul(m as Weight))
			.saturating_add((598_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn disapprove_proposal(p: u32, ) -> Weight {
		(36_628_000 as Weight)
			.saturating_add((640_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}

}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn set_members(m: u32, n: u32, p: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((20_933_000 as Weight).saturating_mul(m as Weight))
			.saturating_add((254_000 as Weight).saturating_mul(n as Weight))
			.saturating_add((28_233_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(p as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn execute(b: u32, m: u32, ) -> Weight {
		(31_147_000 as Weight)
			.saturating_add((4_000 as Weight).saturating_mul(b as Weight))
			.saturating_add((115_000 as Weight).saturating_mul(m as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))

	}
	fn propose_execute(b: u32, m: u32, ) -> Weight {
		(38_774_000 as Weight)
			.saturating_add((4_000 as Weight).saturating_mul(b as Weight))
			.saturating_add((226_000 as Weight).saturating_mul(m as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))

	}
	fn propose_proposed(b: u32, m: u32, p: u32, ) -> Weight {
		(64_230_000 as Weight)
			.saturating_add((5_000 as Weight).saturating_mul(b as Weight))
			.saturating_add((138_000 as Weight).saturating_mul(m as Weight))
			.saturating_add((637_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))

	}
	fn vote(m: u32, ) -> Weight {
		(57_051_000 as Weight)
			.saturating_add((220_000 as Weight).saturating_mul(m as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))

	}
	fn close_early_disapproved(m: u32, p: u32, ) -> Weight {
		(61_406_000 as Weight)
			.saturating_add((225_000 as Weight).saturating_mul(m as Weight))
			.saturating_add((630_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn close_early_approved(b: u32, m: u32, p: u32, ) -> Weight {
		(92_864_000 as Weight)
			.saturating_add((1_000 as Weight).saturating_mul(b as Weight))
			.saturating_add((233_000 as Weight).saturating_mul(m as Weight))
			.saturating_add((597_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn close_disapproved(m: u32, p: u32, ) -> Weight {
		(67_942_000 as Weight)
			.saturating_add((232_000 as Weight).saturating_mul(m as Weight))
			.saturating_add((636_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn close_approved(b: u32, m: u32, p: u32, ) -> Weight {
		(99_742_000 as Weight)
			.saturating_add((1_000 as Weight).saturating_mul(b as Weight))
			.saturating_add((233_000 as Weight).saturating_mul(m as Weight))
			.saturating_add((598_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn disapprove_proposal(p: u32, ) -> Weight {
		(36_628_000 as Weight)
			.saturating_add((640_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}

}
