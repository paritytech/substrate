// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Weights for pallet_identity
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-10-27, STEPS: `[50, ]`, REPEAT: 20, LOW RANGE: [], HIGH RANGE: []
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_identity
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/identity/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_identity.
pub trait WeightInfo {
	fn add_registrar(_r: u32, ) -> Weight;
	fn set_identity(_r: u32, _x: u32, ) -> Weight;
	fn set_subs_new(_s: u32, ) -> Weight;
	fn set_subs_old(_p: u32, ) -> Weight;
	fn clear_identity(_r: u32, _s: u32, _x: u32, ) -> Weight;
	fn request_judgement(_r: u32, _x: u32, ) -> Weight;
	fn cancel_request(_r: u32, _x: u32, ) -> Weight;
	fn set_fee(_r: u32, ) -> Weight;
	fn set_account_id(_r: u32, ) -> Weight;
	fn set_fields(_r: u32, ) -> Weight;
	fn provide_judgement(_r: u32, _x: u32, ) -> Weight;
	fn kill_identity(_r: u32, _s: u32, _x: u32, ) -> Weight;
	fn add_sub(_s: u32, ) -> Weight;
	fn rename_sub(_s: u32, ) -> Weight;
	fn remove_sub(_s: u32, ) -> Weight;
	fn quit_sub(_s: u32, ) -> Weight;
	
}

/// Weights for pallet_identity using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	fn add_registrar(r: u32, ) -> Weight {
		(28_965_000 as Weight)
			.saturating_add((421_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn set_identity(r: u32, x: u32, ) -> Weight {
		(71_923_000 as Weight)
			.saturating_add((529_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((1_763_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn set_subs_new(s: u32, ) -> Weight {
		(55_550_000 as Weight)
			.saturating_add((9_760_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().reads((1 as Weight).saturating_mul(s as Weight)))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn set_subs_old(p: u32, ) -> Weight {
		(51_789_000 as Weight)
			.saturating_add((3_484_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn clear_identity(r: u32, s: u32, x: u32, ) -> Weight {
		(65_458_000 as Weight)
			.saturating_add((230_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3_437_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1_023_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn request_judgement(r: u32, x: u32, ) -> Weight {
		(75_299_000 as Weight)
			.saturating_add((493_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((2_014_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn cancel_request(r: u32, x: u32, ) -> Weight {
		(67_492_000 as Weight)
			.saturating_add((225_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((2_003_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn set_fee(r: u32, ) -> Weight {
		(11_375_000 as Weight)
			.saturating_add((382_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn set_account_id(r: u32, ) -> Weight {
		(12_898_000 as Weight)
			.saturating_add((384_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn set_fields(r: u32, ) -> Weight {
		(11_419_000 as Weight)
			.saturating_add((381_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn provide_judgement(r: u32, x: u32, ) -> Weight {
		(51_115_000 as Weight)
			.saturating_add((427_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((2_001_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn kill_identity(_r: u32, s: u32, _x: u32, ) -> Weight {
		(90_911_000 as Weight)
			.saturating_add((3_450_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn add_sub(s: u32, ) -> Weight {
		(76_957_000 as Weight)
			.saturating_add((261_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn rename_sub(s: u32, ) -> Weight {
		(26_219_000 as Weight)
			.saturating_add((84_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn remove_sub(s: u32, ) -> Weight {
		(73_130_000 as Weight)
			.saturating_add((239_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn quit_sub(s: u32, ) -> Weight {
		(48_088_000 as Weight)
			.saturating_add((237_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn add_registrar(r: u32, ) -> Weight {
		(28_965_000 as Weight)
			.saturating_add((421_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn set_identity(r: u32, x: u32, ) -> Weight {
		(71_923_000 as Weight)
			.saturating_add((529_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((1_763_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn set_subs_new(s: u32, ) -> Weight {
		(55_550_000 as Weight)
			.saturating_add((9_760_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().reads((1 as Weight).saturating_mul(s as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn set_subs_old(p: u32, ) -> Weight {
		(51_789_000 as Weight)
			.saturating_add((3_484_000 as Weight).saturating_mul(p as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(p as Weight)))
	}
	fn clear_identity(r: u32, s: u32, x: u32, ) -> Weight {
		(65_458_000 as Weight)
			.saturating_add((230_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((3_437_000 as Weight).saturating_mul(s as Weight))
			.saturating_add((1_023_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn request_judgement(r: u32, x: u32, ) -> Weight {
		(75_299_000 as Weight)
			.saturating_add((493_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((2_014_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn cancel_request(r: u32, x: u32, ) -> Weight {
		(67_492_000 as Weight)
			.saturating_add((225_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((2_003_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn set_fee(r: u32, ) -> Weight {
		(11_375_000 as Weight)
			.saturating_add((382_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn set_account_id(r: u32, ) -> Weight {
		(12_898_000 as Weight)
			.saturating_add((384_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn set_fields(r: u32, ) -> Weight {
		(11_419_000 as Weight)
			.saturating_add((381_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn provide_judgement(r: u32, x: u32, ) -> Weight {
		(51_115_000 as Weight)
			.saturating_add((427_000 as Weight).saturating_mul(r as Weight))
			.saturating_add((2_001_000 as Weight).saturating_mul(x as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn kill_identity(_r: u32, s: u32, _x: u32, ) -> Weight {
		(90_911_000 as Weight)
			.saturating_add((3_450_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
	fn add_sub(s: u32, ) -> Weight {
		(76_957_000 as Weight)
			.saturating_add((261_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn rename_sub(s: u32, ) -> Weight {
		(26_219_000 as Weight)
			.saturating_add((84_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn remove_sub(s: u32, ) -> Weight {
		(73_130_000 as Weight)
			.saturating_add((239_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn quit_sub(s: u32, ) -> Weight {
		(48_088_000 as Weight)
			.saturating_add((237_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	
}
