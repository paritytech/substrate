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

//! Autogenerated weights for pallet_proxy
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-04-04, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `bm3`, CPU: `Intel(R) Core(TM) i7-7700K CPU @ 4.20GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_proxy
// --no-storage-info
// --no-median-slopes
// --no-min-squares
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/proxy/src/weights.rs
// --header=./HEADER-APACHE2
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_proxy.
pub trait WeightInfo {
	fn proxy(p: u32, ) -> Weight;
	fn proxy_announced(a: u32, p: u32, ) -> Weight;
	fn remove_announcement(a: u32, p: u32, ) -> Weight;
	fn reject_announcement(a: u32, p: u32, ) -> Weight;
	fn announce(a: u32, p: u32, ) -> Weight;
	fn add_proxy(p: u32, ) -> Weight;
	fn remove_proxy(p: u32, ) -> Weight;
	fn remove_proxies(p: u32, ) -> Weight;
	fn create_pure(p: u32, ) -> Weight;
	fn kill_pure(p: u32, ) -> Weight;
}

/// Weights for pallet_proxy using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: Proxy Proxies (r:1 w:0)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// The range of component `p` is `[1, 31]`.
	fn proxy(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `161 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 16_285_000 picoseconds.
		Weight::from_parts(16_986_687, 4706)
			// Standard Error: 1_416
			.saturating_add(Weight::from_parts(28_653, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:0)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// Storage: Proxy Announcements (r:1 w:1)
	/// Proof: Proxy Announcements (max_values: None, max_size: Some(2233), added: 4708, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `a` is `[0, 31]`.
	/// The range of component `p` is `[1, 31]`.
	fn proxy_announced(a: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `488 + a * (68 ±0) + p * (37 ±0)`
		//  Estimated: `13997`
		// Minimum execution time: 41_485_000 picoseconds.
		Weight::from_parts(41_514_094, 13997)
			// Standard Error: 4_011
			.saturating_add(Weight::from_parts(130_447, 0).saturating_mul(a.into()))
			// Standard Error: 4_144
			.saturating_add(Weight::from_parts(35_158, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: Proxy Announcements (r:1 w:1)
	/// Proof: Proxy Announcements (max_values: None, max_size: Some(2233), added: 4708, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `a` is `[0, 31]`.
	/// The range of component `p` is `[1, 31]`.
	fn remove_announcement(a: u32, _p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `403 + a * (68 ±0)`
		//  Estimated: `9291`
		// Minimum execution time: 25_319_000 picoseconds.
		Weight::from_parts(26_239_485, 9291)
			// Standard Error: 1_510
			.saturating_add(Weight::from_parts(165_430, 0).saturating_mul(a.into()))
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: Proxy Announcements (r:1 w:1)
	/// Proof: Proxy Announcements (max_values: None, max_size: Some(2233), added: 4708, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `a` is `[0, 31]`.
	/// The range of component `p` is `[1, 31]`.
	fn reject_announcement(a: u32, _p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `403 + a * (68 ±0)`
		//  Estimated: `9291`
		// Minimum execution time: 25_408_000 picoseconds.
		Weight::from_parts(26_298_710, 9291)
			// Standard Error: 2_103
			.saturating_add(Weight::from_parts(165_101, 0).saturating_mul(a.into()))
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:0)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// Storage: Proxy Announcements (r:1 w:1)
	/// Proof: Proxy Announcements (max_values: None, max_size: Some(2233), added: 4708, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `a` is `[0, 31]`.
	/// The range of component `p` is `[1, 31]`.
	fn announce(a: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `420 + a * (68 ±0) + p * (37 ±0)`
		//  Estimated: `13997`
		// Minimum execution time: 36_401_000 picoseconds.
		Weight::from_parts(38_308_693, 13997)
			// Standard Error: 3_919
			.saturating_add(Weight::from_parts(135_882, 0).saturating_mul(a.into()))
			// Standard Error: 4_049
			.saturating_add(Weight::from_parts(27_362, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:1)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// The range of component `p` is `[1, 31]`.
	fn add_proxy(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `161 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 26_475_000 picoseconds.
		Weight::from_parts(27_178_605, 4706)
			// Standard Error: 11_704
			.saturating_add(Weight::from_parts(78_320, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:1)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// The range of component `p` is `[1, 31]`.
	fn remove_proxy(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `161 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 26_586_000 picoseconds.
		Weight::from_parts(27_533_841, 4706)
			// Standard Error: 8_738
			.saturating_add(Weight::from_parts(78_735, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:1)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// The range of component `p` is `[1, 31]`.
	fn remove_proxies(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `161 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 23_544_000 picoseconds.
		Weight::from_parts(24_238_841, 4706)
			// Standard Error: 1_216
			.saturating_add(Weight::from_parts(27_953, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:1)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// The range of component `p` is `[1, 31]`.
	fn create_pure(_p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `173`
		//  Estimated: `4706`
		// Minimum execution time: 28_253_000 picoseconds.
		Weight::from_parts(29_342_429, 4706)
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:1)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// The range of component `p` is `[0, 30]`.
	fn kill_pure(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `198 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 24_550_000 picoseconds.
		Weight::from_parts(25_378_707, 4706)
			// Standard Error: 1_412
			.saturating_add(Weight::from_parts(34_116, 0).saturating_mul(p.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// Storage: Proxy Proxies (r:1 w:0)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// The range of component `p` is `[1, 31]`.
	fn proxy(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `161 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 16_285_000 picoseconds.
		Weight::from_parts(16_986_687, 4706)
			// Standard Error: 1_416
			.saturating_add(Weight::from_parts(28_653, 0).saturating_mul(p.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:0)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// Storage: Proxy Announcements (r:1 w:1)
	/// Proof: Proxy Announcements (max_values: None, max_size: Some(2233), added: 4708, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `a` is `[0, 31]`.
	/// The range of component `p` is `[1, 31]`.
	fn proxy_announced(a: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `488 + a * (68 ±0) + p * (37 ±0)`
		//  Estimated: `13997`
		// Minimum execution time: 41_485_000 picoseconds.
		Weight::from_parts(41_514_094, 13997)
			// Standard Error: 4_011
			.saturating_add(Weight::from_parts(130_447, 0).saturating_mul(a.into()))
			// Standard Error: 4_144
			.saturating_add(Weight::from_parts(35_158, 0).saturating_mul(p.into()))
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: Proxy Announcements (r:1 w:1)
	/// Proof: Proxy Announcements (max_values: None, max_size: Some(2233), added: 4708, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `a` is `[0, 31]`.
	/// The range of component `p` is `[1, 31]`.
	fn remove_announcement(a: u32, _p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `403 + a * (68 ±0)`
		//  Estimated: `9291`
		// Minimum execution time: 25_319_000 picoseconds.
		Weight::from_parts(26_239_485, 9291)
			// Standard Error: 1_510
			.saturating_add(Weight::from_parts(165_430, 0).saturating_mul(a.into()))
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: Proxy Announcements (r:1 w:1)
	/// Proof: Proxy Announcements (max_values: None, max_size: Some(2233), added: 4708, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `a` is `[0, 31]`.
	/// The range of component `p` is `[1, 31]`.
	fn reject_announcement(a: u32, _p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `403 + a * (68 ±0)`
		//  Estimated: `9291`
		// Minimum execution time: 25_408_000 picoseconds.
		Weight::from_parts(26_298_710, 9291)
			// Standard Error: 2_103
			.saturating_add(Weight::from_parts(165_101, 0).saturating_mul(a.into()))
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:0)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// Storage: Proxy Announcements (r:1 w:1)
	/// Proof: Proxy Announcements (max_values: None, max_size: Some(2233), added: 4708, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// The range of component `a` is `[0, 31]`.
	/// The range of component `p` is `[1, 31]`.
	fn announce(a: u32, p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `420 + a * (68 ±0) + p * (37 ±0)`
		//  Estimated: `13997`
		// Minimum execution time: 36_401_000 picoseconds.
		Weight::from_parts(38_308_693, 13997)
			// Standard Error: 3_919
			.saturating_add(Weight::from_parts(135_882, 0).saturating_mul(a.into()))
			// Standard Error: 4_049
			.saturating_add(Weight::from_parts(27_362, 0).saturating_mul(p.into()))
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:1)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// The range of component `p` is `[1, 31]`.
	fn add_proxy(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `161 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 26_475_000 picoseconds.
		Weight::from_parts(27_178_605, 4706)
			// Standard Error: 11_704
			.saturating_add(Weight::from_parts(78_320, 0).saturating_mul(p.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:1)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// The range of component `p` is `[1, 31]`.
	fn remove_proxy(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `161 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 26_586_000 picoseconds.
		Weight::from_parts(27_533_841, 4706)
			// Standard Error: 8_738
			.saturating_add(Weight::from_parts(78_735, 0).saturating_mul(p.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:1)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// The range of component `p` is `[1, 31]`.
	fn remove_proxies(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `161 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 23_544_000 picoseconds.
		Weight::from_parts(24_238_841, 4706)
			// Standard Error: 1_216
			.saturating_add(Weight::from_parts(27_953, 0).saturating_mul(p.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:1)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// The range of component `p` is `[1, 31]`.
	fn create_pure(_p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `173`
		//  Estimated: `4706`
		// Minimum execution time: 28_253_000 picoseconds.
		Weight::from_parts(29_342_429, 4706)
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Proxy Proxies (r:1 w:1)
	/// Proof: Proxy Proxies (max_values: None, max_size: Some(1241), added: 3716, mode: MaxEncodedLen)
	/// The range of component `p` is `[0, 30]`.
	fn kill_pure(p: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `198 + p * (37 ±0)`
		//  Estimated: `4706`
		// Minimum execution time: 24_550_000 picoseconds.
		Weight::from_parts(25_378_707, 4706)
			// Standard Error: 1_412
			.saturating_add(Weight::from_parts(34_116, 0).saturating_mul(p.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
}
