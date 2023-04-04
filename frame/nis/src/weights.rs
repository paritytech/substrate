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

//! Autogenerated weights for pallet_nis
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
// --pallet=pallet_nis
// --no-storage-info
// --no-median-slopes
// --no-min-squares
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/nis/src/weights.rs
// --header=./HEADER-APACHE2
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_nis.
pub trait WeightInfo {
	fn place_bid(l: u32, ) -> Weight;
	fn place_bid_max() -> Weight;
	fn retract_bid(l: u32, ) -> Weight;
	fn fund_deficit() -> Weight;
	fn communify() -> Weight;
	fn privatize() -> Weight;
	fn thaw_private() -> Weight;
	fn thaw_communal() -> Weight;
	fn process_queues() -> Weight;
	fn process_queue() -> Weight;
	fn process_bid() -> Weight;
}

/// Weights for pallet_nis using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: Nis Queues (r:1 w:1)
	/// Proof: Nis Queues (max_values: None, max_size: Some(48022), added: 50497, mode: MaxEncodedLen)
	/// Storage: Balances Holds (r:1 w:1)
	/// Proof: Balances Holds (max_values: None, max_size: Some(66), added: 2541, mode: MaxEncodedLen)
	/// Storage: Nis QueueTotals (r:1 w:1)
	/// Proof: Nis QueueTotals (max_values: Some(1), max_size: Some(6002), added: 6497, mode: MaxEncodedLen)
	/// The range of component `l` is `[0, 999]`.
	fn place_bid(l: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6175 + l * (48 ±0)`
		//  Estimated: `62505`
		// Minimum execution time: 48_746_000 picoseconds.
		Weight::from_parts(54_934_014, 62505)
			// Standard Error: 198
			.saturating_add(Weight::from_parts(44_561, 0).saturating_mul(l.into()))
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: Nis Queues (r:1 w:1)
	/// Proof: Nis Queues (max_values: None, max_size: Some(48022), added: 50497, mode: MaxEncodedLen)
	/// Storage: Balances Holds (r:1 w:1)
	/// Proof: Balances Holds (max_values: None, max_size: Some(66), added: 2541, mode: MaxEncodedLen)
	/// Storage: Nis QueueTotals (r:1 w:1)
	/// Proof: Nis QueueTotals (max_values: Some(1), max_size: Some(6002), added: 6497, mode: MaxEncodedLen)
	fn place_bid_max() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `54177`
		//  Estimated: `62505`
		// Minimum execution time: 111_042_000 picoseconds.
		Weight::from_parts(111_905_000, 62505)
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: Nis Queues (r:1 w:1)
	/// Proof: Nis Queues (max_values: None, max_size: Some(48022), added: 50497, mode: MaxEncodedLen)
	/// Storage: Balances Holds (r:1 w:1)
	/// Proof: Balances Holds (max_values: None, max_size: Some(66), added: 2541, mode: MaxEncodedLen)
	/// Storage: Nis QueueTotals (r:1 w:1)
	/// Proof: Nis QueueTotals (max_values: Some(1), max_size: Some(6002), added: 6497, mode: MaxEncodedLen)
	/// The range of component `l` is `[1, 1000]`.
	fn retract_bid(l: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6175 + l * (48 ±0)`
		//  Estimated: `62505`
		// Minimum execution time: 50_626_000 picoseconds.
		Weight::from_parts(51_568_385, 62505)
			// Standard Error: 156
			.saturating_add(Weight::from_parts(63_532, 0).saturating_mul(l.into()))
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: Nis Summary (r:1 w:0)
	/// Proof: Nis Summary (max_values: Some(1), max_size: Some(40), added: 535, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	fn fund_deficit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `191`
		//  Estimated: `5118`
		// Minimum execution time: 41_007_000 picoseconds.
		Weight::from_parts(41_485_000, 5118)
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Nis Receipts (r:1 w:1)
	/// Proof: Nis Receipts (max_values: None, max_size: Some(81), added: 2556, mode: MaxEncodedLen)
	/// Storage: Balances Holds (r:1 w:1)
	/// Proof: Balances Holds (max_values: None, max_size: Some(66), added: 2541, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Nis Summary (r:1 w:1)
	/// Proof: Nis Summary (max_values: Some(1), max_size: Some(40), added: 535, mode: MaxEncodedLen)
	/// Storage: Assets Asset (r:1 w:1)
	/// Proof: Assets Asset (max_values: None, max_size: Some(210), added: 2685, mode: MaxEncodedLen)
	/// Storage: Assets Account (r:1 w:1)
	/// Proof: Assets Account (max_values: None, max_size: Some(102), added: 2577, mode: MaxEncodedLen)
	fn communify() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `667`
		//  Estimated: `19437`
		// Minimum execution time: 75_029_000 picoseconds.
		Weight::from_parts(75_844_000, 19437)
			.saturating_add(T::DbWeight::get().reads(6_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
	}
	/// Storage: Nis Receipts (r:1 w:1)
	/// Proof: Nis Receipts (max_values: None, max_size: Some(81), added: 2556, mode: MaxEncodedLen)
	/// Storage: Nis Summary (r:1 w:1)
	/// Proof: Nis Summary (max_values: Some(1), max_size: Some(40), added: 535, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Assets Asset (r:1 w:1)
	/// Proof: Assets Asset (max_values: None, max_size: Some(210), added: 2685, mode: MaxEncodedLen)
	/// Storage: Assets Account (r:1 w:1)
	/// Proof: Assets Account (max_values: None, max_size: Some(102), added: 2577, mode: MaxEncodedLen)
	/// Storage: Balances Holds (r:1 w:1)
	/// Proof: Balances Holds (max_values: None, max_size: Some(66), added: 2541, mode: MaxEncodedLen)
	fn privatize() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `828`
		//  Estimated: `19437`
		// Minimum execution time: 91_816_000 picoseconds.
		Weight::from_parts(92_626_000, 19437)
			.saturating_add(T::DbWeight::get().reads(6_u64))
			.saturating_add(T::DbWeight::get().writes(6_u64))
	}
	/// Storage: Nis Receipts (r:1 w:1)
	/// Proof: Nis Receipts (max_values: None, max_size: Some(81), added: 2556, mode: MaxEncodedLen)
	/// Storage: Nis Summary (r:1 w:1)
	/// Proof: Nis Summary (max_values: Some(1), max_size: Some(40), added: 535, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Balances Holds (r:1 w:1)
	/// Proof: Balances Holds (max_values: None, max_size: Some(66), added: 2541, mode: MaxEncodedLen)
	fn thaw_private() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `456`
		//  Estimated: `12195`
		// Minimum execution time: 76_138_000 picoseconds.
		Weight::from_parts(76_810_000, 12195)
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(T::DbWeight::get().writes(4_u64))
	}
	/// Storage: Nis Receipts (r:1 w:1)
	/// Proof: Nis Receipts (max_values: None, max_size: Some(81), added: 2556, mode: MaxEncodedLen)
	/// Storage: Nis Summary (r:1 w:1)
	/// Proof: Nis Summary (max_values: Some(1), max_size: Some(40), added: 535, mode: MaxEncodedLen)
	/// Storage: Assets Asset (r:1 w:1)
	/// Proof: Assets Asset (max_values: None, max_size: Some(210), added: 2685, mode: MaxEncodedLen)
	/// Storage: Assets Account (r:1 w:1)
	/// Proof: Assets Account (max_values: None, max_size: Some(102), added: 2577, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	fn thaw_communal() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `773`
		//  Estimated: `15906`
		// Minimum execution time: 86_809_000 picoseconds.
		Weight::from_parts(87_777_000, 15906)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(5_u64))
	}
	/// Storage: Nis Summary (r:1 w:1)
	/// Proof: Nis Summary (max_values: Some(1), max_size: Some(40), added: 535, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:0)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Nis QueueTotals (r:1 w:1)
	/// Proof: Nis QueueTotals (max_values: Some(1), max_size: Some(6002), added: 6497, mode: MaxEncodedLen)
	fn process_queues() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6624`
		//  Estimated: `12605`
		// Minimum execution time: 22_440_000 picoseconds.
		Weight::from_parts(22_880_000, 12605)
			.saturating_add(T::DbWeight::get().reads(3_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: Nis Queues (r:1 w:1)
	/// Proof: Nis Queues (max_values: None, max_size: Some(48022), added: 50497, mode: MaxEncodedLen)
	fn process_queue() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `42`
		//  Estimated: `51487`
		// Minimum execution time: 4_651_000 picoseconds.
		Weight::from_parts(4_921_000, 51487)
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Nis Receipts (r:0 w:1)
	/// Proof: Nis Receipts (max_values: None, max_size: Some(81), added: 2556, mode: MaxEncodedLen)
	fn process_bid() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 7_964_000 picoseconds.
		Weight::from_parts(8_258_000, 0)
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// Storage: Nis Queues (r:1 w:1)
	/// Proof: Nis Queues (max_values: None, max_size: Some(48022), added: 50497, mode: MaxEncodedLen)
	/// Storage: Balances Holds (r:1 w:1)
	/// Proof: Balances Holds (max_values: None, max_size: Some(66), added: 2541, mode: MaxEncodedLen)
	/// Storage: Nis QueueTotals (r:1 w:1)
	/// Proof: Nis QueueTotals (max_values: Some(1), max_size: Some(6002), added: 6497, mode: MaxEncodedLen)
	/// The range of component `l` is `[0, 999]`.
	fn place_bid(l: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6175 + l * (48 ±0)`
		//  Estimated: `62505`
		// Minimum execution time: 48_746_000 picoseconds.
		Weight::from_parts(54_934_014, 62505)
			// Standard Error: 198
			.saturating_add(Weight::from_parts(44_561, 0).saturating_mul(l.into()))
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: Nis Queues (r:1 w:1)
	/// Proof: Nis Queues (max_values: None, max_size: Some(48022), added: 50497, mode: MaxEncodedLen)
	/// Storage: Balances Holds (r:1 w:1)
	/// Proof: Balances Holds (max_values: None, max_size: Some(66), added: 2541, mode: MaxEncodedLen)
	/// Storage: Nis QueueTotals (r:1 w:1)
	/// Proof: Nis QueueTotals (max_values: Some(1), max_size: Some(6002), added: 6497, mode: MaxEncodedLen)
	fn place_bid_max() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `54177`
		//  Estimated: `62505`
		// Minimum execution time: 111_042_000 picoseconds.
		Weight::from_parts(111_905_000, 62505)
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: Nis Queues (r:1 w:1)
	/// Proof: Nis Queues (max_values: None, max_size: Some(48022), added: 50497, mode: MaxEncodedLen)
	/// Storage: Balances Holds (r:1 w:1)
	/// Proof: Balances Holds (max_values: None, max_size: Some(66), added: 2541, mode: MaxEncodedLen)
	/// Storage: Nis QueueTotals (r:1 w:1)
	/// Proof: Nis QueueTotals (max_values: Some(1), max_size: Some(6002), added: 6497, mode: MaxEncodedLen)
	/// The range of component `l` is `[1, 1000]`.
	fn retract_bid(l: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6175 + l * (48 ±0)`
		//  Estimated: `62505`
		// Minimum execution time: 50_626_000 picoseconds.
		Weight::from_parts(51_568_385, 62505)
			// Standard Error: 156
			.saturating_add(Weight::from_parts(63_532, 0).saturating_mul(l.into()))
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: Nis Summary (r:1 w:0)
	/// Proof: Nis Summary (max_values: Some(1), max_size: Some(40), added: 535, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	fn fund_deficit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `191`
		//  Estimated: `5118`
		// Minimum execution time: 41_007_000 picoseconds.
		Weight::from_parts(41_485_000, 5118)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Nis Receipts (r:1 w:1)
	/// Proof: Nis Receipts (max_values: None, max_size: Some(81), added: 2556, mode: MaxEncodedLen)
	/// Storage: Balances Holds (r:1 w:1)
	/// Proof: Balances Holds (max_values: None, max_size: Some(66), added: 2541, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Nis Summary (r:1 w:1)
	/// Proof: Nis Summary (max_values: Some(1), max_size: Some(40), added: 535, mode: MaxEncodedLen)
	/// Storage: Assets Asset (r:1 w:1)
	/// Proof: Assets Asset (max_values: None, max_size: Some(210), added: 2685, mode: MaxEncodedLen)
	/// Storage: Assets Account (r:1 w:1)
	/// Proof: Assets Account (max_values: None, max_size: Some(102), added: 2577, mode: MaxEncodedLen)
	fn communify() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `667`
		//  Estimated: `19437`
		// Minimum execution time: 75_029_000 picoseconds.
		Weight::from_parts(75_844_000, 19437)
			.saturating_add(RocksDbWeight::get().reads(6_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: Nis Receipts (r:1 w:1)
	/// Proof: Nis Receipts (max_values: None, max_size: Some(81), added: 2556, mode: MaxEncodedLen)
	/// Storage: Nis Summary (r:1 w:1)
	/// Proof: Nis Summary (max_values: Some(1), max_size: Some(40), added: 535, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Assets Asset (r:1 w:1)
	/// Proof: Assets Asset (max_values: None, max_size: Some(210), added: 2685, mode: MaxEncodedLen)
	/// Storage: Assets Account (r:1 w:1)
	/// Proof: Assets Account (max_values: None, max_size: Some(102), added: 2577, mode: MaxEncodedLen)
	/// Storage: Balances Holds (r:1 w:1)
	/// Proof: Balances Holds (max_values: None, max_size: Some(66), added: 2541, mode: MaxEncodedLen)
	fn privatize() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `828`
		//  Estimated: `19437`
		// Minimum execution time: 91_816_000 picoseconds.
		Weight::from_parts(92_626_000, 19437)
			.saturating_add(RocksDbWeight::get().reads(6_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: Nis Receipts (r:1 w:1)
	/// Proof: Nis Receipts (max_values: None, max_size: Some(81), added: 2556, mode: MaxEncodedLen)
	/// Storage: Nis Summary (r:1 w:1)
	/// Proof: Nis Summary (max_values: Some(1), max_size: Some(40), added: 535, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Balances Holds (r:1 w:1)
	/// Proof: Balances Holds (max_values: None, max_size: Some(66), added: 2541, mode: MaxEncodedLen)
	fn thaw_private() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `456`
		//  Estimated: `12195`
		// Minimum execution time: 76_138_000 picoseconds.
		Weight::from_parts(76_810_000, 12195)
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(RocksDbWeight::get().writes(4_u64))
	}
	/// Storage: Nis Receipts (r:1 w:1)
	/// Proof: Nis Receipts (max_values: None, max_size: Some(81), added: 2556, mode: MaxEncodedLen)
	/// Storage: Nis Summary (r:1 w:1)
	/// Proof: Nis Summary (max_values: Some(1), max_size: Some(40), added: 535, mode: MaxEncodedLen)
	/// Storage: Assets Asset (r:1 w:1)
	/// Proof: Assets Asset (max_values: None, max_size: Some(210), added: 2685, mode: MaxEncodedLen)
	/// Storage: Assets Account (r:1 w:1)
	/// Proof: Assets Account (max_values: None, max_size: Some(102), added: 2577, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	fn thaw_communal() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `773`
		//  Estimated: `15906`
		// Minimum execution time: 86_809_000 picoseconds.
		Weight::from_parts(87_777_000, 15906)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(5_u64))
	}
	/// Storage: Nis Summary (r:1 w:1)
	/// Proof: Nis Summary (max_values: Some(1), max_size: Some(40), added: 535, mode: MaxEncodedLen)
	/// Storage: System Account (r:1 w:0)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: Nis QueueTotals (r:1 w:1)
	/// Proof: Nis QueueTotals (max_values: Some(1), max_size: Some(6002), added: 6497, mode: MaxEncodedLen)
	fn process_queues() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `6624`
		//  Estimated: `12605`
		// Minimum execution time: 22_440_000 picoseconds.
		Weight::from_parts(22_880_000, 12605)
			.saturating_add(RocksDbWeight::get().reads(3_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: Nis Queues (r:1 w:1)
	/// Proof: Nis Queues (max_values: None, max_size: Some(48022), added: 50497, mode: MaxEncodedLen)
	fn process_queue() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `42`
		//  Estimated: `51487`
		// Minimum execution time: 4_651_000 picoseconds.
		Weight::from_parts(4_921_000, 51487)
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Nis Receipts (r:0 w:1)
	/// Proof: Nis Receipts (max_values: None, max_size: Some(81), added: 2556, mode: MaxEncodedLen)
	fn process_bid() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 7_964_000 picoseconds.
		Weight::from_parts(8_258_000, 0)
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
}
