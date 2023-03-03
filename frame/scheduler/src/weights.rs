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

//! Autogenerated weights for pallet_scheduler
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-03-03, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
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
// --pallet=pallet_scheduler
// --no-storage-info
// --no-median-slopes
// --no-min-squares
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/scheduler/src/weights.rs
// --header=./HEADER-APACHE2
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_scheduler.
pub trait WeightInfo {
	fn service_agendas_base() -> Weight;
	fn service_agenda_base(s: u32, ) -> Weight;
	fn service_task_base() -> Weight;
	fn service_task_fetched(s: u32, ) -> Weight;
	fn service_task_named() -> Weight;
	fn service_task_periodic() -> Weight;
	fn execute_dispatch_signed() -> Weight;
	fn execute_dispatch_unsigned() -> Weight;
	fn schedule(s: u32, ) -> Weight;
	fn cancel(s: u32, ) -> Weight;
	fn schedule_named(s: u32, ) -> Weight;
	fn cancel_named(s: u32, ) -> Weight;
}

/// Weights for pallet_scheduler using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: Scheduler IncompleteSince (r:1 w:1)
	/// Proof: Scheduler IncompleteSince (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	fn service_agendas_base() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `30`
		//  Estimated: `1489`
		// Minimum execution time: 4_005 nanoseconds.
		Weight::from_ref_time(4_209_000)
			.saturating_add(Weight::from_proof_size(1489))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Scheduler Agenda (r:1 w:1)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// The range of component `s` is `[0, 512]`.
	fn service_agenda_base(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `112 + s * (177 ±0)`
		//  Estimated: `110487`
		// Minimum execution time: 3_538 nanoseconds.
		Weight::from_ref_time(9_147_349)
			.saturating_add(Weight::from_proof_size(110487))
			// Standard Error: 775
			.saturating_add(Weight::from_ref_time(304_816).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	fn service_task_base() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_623 nanoseconds.
		Weight::from_ref_time(5_939_000)
			.saturating_add(Weight::from_proof_size(0))
	}
	/// Storage: Preimage PreimageFor (r:1 w:1)
	/// Proof: Preimage PreimageFor (max_values: None, max_size: Some(4194344), added: 4196819, mode: Measured)
	/// Storage: Preimage StatusFor (r:1 w:1)
	/// Proof: Preimage StatusFor (max_values: None, max_size: Some(91), added: 2566, mode: MaxEncodedLen)
	/// The range of component `s` is `[128, 4194304]`.
	fn service_task_fetched(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `211 + s * (1 ±0)`
		//  Estimated: `7232 + s * (1 ±0)`
		// Minimum execution time: 20_194 nanoseconds.
		Weight::from_ref_time(20_413_000)
			.saturating_add(Weight::from_proof_size(7232))
			// Standard Error: 1
			.saturating_add(Weight::from_ref_time(1_141).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
			.saturating_add(Weight::from_proof_size(1).saturating_mul(s.into()))
	}
	/// Storage: Scheduler Lookup (r:0 w:1)
	/// Proof: Scheduler Lookup (max_values: None, max_size: Some(48), added: 2523, mode: MaxEncodedLen)
	fn service_task_named() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 7_687 nanoseconds.
		Weight::from_ref_time(7_865_000)
			.saturating_add(Weight::from_proof_size(0))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	fn service_task_periodic() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_587 nanoseconds.
		Weight::from_ref_time(5_931_000)
			.saturating_add(Weight::from_proof_size(0))
	}
	fn execute_dispatch_signed() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_774 nanoseconds.
		Weight::from_ref_time(2_888_000)
			.saturating_add(Weight::from_proof_size(0))
	}
	fn execute_dispatch_unsigned() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_614 nanoseconds.
		Weight::from_ref_time(2_785_000)
			.saturating_add(Weight::from_proof_size(0))
	}
	/// Storage: Scheduler Agenda (r:1 w:1)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// The range of component `s` is `[0, 511]`.
	fn schedule(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `112 + s * (177 ±0)`
		//  Estimated: `110487`
		// Minimum execution time: 13_803 nanoseconds.
		Weight::from_ref_time(18_360_818)
			.saturating_add(Weight::from_proof_size(110487))
			// Standard Error: 834
			.saturating_add(Weight::from_ref_time(318_836).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: Scheduler Agenda (r:1 w:1)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// Storage: Scheduler Lookup (r:0 w:1)
	/// Proof: Scheduler Lookup (max_values: None, max_size: Some(48), added: 2523, mode: MaxEncodedLen)
	/// The range of component `s` is `[1, 512]`.
	fn cancel(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `112 + s * (177 ±0)`
		//  Estimated: `110487`
		// Minimum execution time: 17_727 nanoseconds.
		Weight::from_ref_time(18_646_543)
			.saturating_add(Weight::from_proof_size(110487))
			// Standard Error: 698
			.saturating_add(Weight::from_ref_time(485_563).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: Scheduler Lookup (r:1 w:1)
	/// Proof: Scheduler Lookup (max_values: None, max_size: Some(48), added: 2523, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:1 w:1)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// The range of component `s` is `[0, 511]`.
	fn schedule_named(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `627 + s * (178 ±0)`
		//  Estimated: `114000`
		// Minimum execution time: 16_991 nanoseconds.
		Weight::from_ref_time(24_143_960)
			.saturating_add(Weight::from_proof_size(114000))
			// Standard Error: 757
			.saturating_add(Weight::from_ref_time(318_086).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: Scheduler Lookup (r:1 w:1)
	/// Proof: Scheduler Lookup (max_values: None, max_size: Some(48), added: 2523, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:1 w:1)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// The range of component `s` is `[1, 512]`.
	fn cancel_named(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `740 + s * (177 ±0)`
		//  Estimated: `114000`
		// Minimum execution time: 19_602 nanoseconds.
		Weight::from_ref_time(20_805_381)
			.saturating_add(Weight::from_proof_size(114000))
			// Standard Error: 1_539
			.saturating_add(Weight::from_ref_time(492_732).saturating_mul(s.into()))
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// Storage: Scheduler IncompleteSince (r:1 w:1)
	/// Proof: Scheduler IncompleteSince (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	fn service_agendas_base() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `30`
		//  Estimated: `1489`
		// Minimum execution time: 4_005 nanoseconds.
		Weight::from_ref_time(4_209_000)
			.saturating_add(Weight::from_proof_size(1489))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Scheduler Agenda (r:1 w:1)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// The range of component `s` is `[0, 512]`.
	fn service_agenda_base(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `112 + s * (177 ±0)`
		//  Estimated: `110487`
		// Minimum execution time: 3_538 nanoseconds.
		Weight::from_ref_time(9_147_349)
			.saturating_add(Weight::from_proof_size(110487))
			// Standard Error: 775
			.saturating_add(Weight::from_ref_time(304_816).saturating_mul(s.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	fn service_task_base() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_623 nanoseconds.
		Weight::from_ref_time(5_939_000)
			.saturating_add(Weight::from_proof_size(0))
	}
	/// Storage: Preimage PreimageFor (r:1 w:1)
	/// Proof: Preimage PreimageFor (max_values: None, max_size: Some(4194344), added: 4196819, mode: Measured)
	/// Storage: Preimage StatusFor (r:1 w:1)
	/// Proof: Preimage StatusFor (max_values: None, max_size: Some(91), added: 2566, mode: MaxEncodedLen)
	/// The range of component `s` is `[128, 4194304]`.
	fn service_task_fetched(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `211 + s * (1 ±0)`
		//  Estimated: `7232 + s * (1 ±0)`
		// Minimum execution time: 20_194 nanoseconds.
		Weight::from_ref_time(20_413_000)
			.saturating_add(Weight::from_proof_size(7232))
			// Standard Error: 1
			.saturating_add(Weight::from_ref_time(1_141).saturating_mul(s.into()))
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
			.saturating_add(Weight::from_proof_size(1).saturating_mul(s.into()))
	}
	/// Storage: Scheduler Lookup (r:0 w:1)
	/// Proof: Scheduler Lookup (max_values: None, max_size: Some(48), added: 2523, mode: MaxEncodedLen)
	fn service_task_named() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 7_687 nanoseconds.
		Weight::from_ref_time(7_865_000)
			.saturating_add(Weight::from_proof_size(0))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	fn service_task_periodic() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_587 nanoseconds.
		Weight::from_ref_time(5_931_000)
			.saturating_add(Weight::from_proof_size(0))
	}
	fn execute_dispatch_signed() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_774 nanoseconds.
		Weight::from_ref_time(2_888_000)
			.saturating_add(Weight::from_proof_size(0))
	}
	fn execute_dispatch_unsigned() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 2_614 nanoseconds.
		Weight::from_ref_time(2_785_000)
			.saturating_add(Weight::from_proof_size(0))
	}
	/// Storage: Scheduler Agenda (r:1 w:1)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// The range of component `s` is `[0, 511]`.
	fn schedule(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `112 + s * (177 ±0)`
		//  Estimated: `110487`
		// Minimum execution time: 13_803 nanoseconds.
		Weight::from_ref_time(18_360_818)
			.saturating_add(Weight::from_proof_size(110487))
			// Standard Error: 834
			.saturating_add(Weight::from_ref_time(318_836).saturating_mul(s.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: Scheduler Agenda (r:1 w:1)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// Storage: Scheduler Lookup (r:0 w:1)
	/// Proof: Scheduler Lookup (max_values: None, max_size: Some(48), added: 2523, mode: MaxEncodedLen)
	/// The range of component `s` is `[1, 512]`.
	fn cancel(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `112 + s * (177 ±0)`
		//  Estimated: `110487`
		// Minimum execution time: 17_727 nanoseconds.
		Weight::from_ref_time(18_646_543)
			.saturating_add(Weight::from_proof_size(110487))
			// Standard Error: 698
			.saturating_add(Weight::from_ref_time(485_563).saturating_mul(s.into()))
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: Scheduler Lookup (r:1 w:1)
	/// Proof: Scheduler Lookup (max_values: None, max_size: Some(48), added: 2523, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:1 w:1)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// The range of component `s` is `[0, 511]`.
	fn schedule_named(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `627 + s * (178 ±0)`
		//  Estimated: `114000`
		// Minimum execution time: 16_991 nanoseconds.
		Weight::from_ref_time(24_143_960)
			.saturating_add(Weight::from_proof_size(114000))
			// Standard Error: 757
			.saturating_add(Weight::from_ref_time(318_086).saturating_mul(s.into()))
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: Scheduler Lookup (r:1 w:1)
	/// Proof: Scheduler Lookup (max_values: None, max_size: Some(48), added: 2523, mode: MaxEncodedLen)
	/// Storage: Scheduler Agenda (r:1 w:1)
	/// Proof: Scheduler Agenda (max_values: None, max_size: Some(107022), added: 109497, mode: MaxEncodedLen)
	/// The range of component `s` is `[1, 512]`.
	fn cancel_named(s: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `740 + s * (177 ±0)`
		//  Estimated: `114000`
		// Minimum execution time: 19_602 nanoseconds.
		Weight::from_ref_time(20_805_381)
			.saturating_add(Weight::from_proof_size(114000))
			// Standard Error: 1_539
			.saturating_add(Weight::from_ref_time(492_732).saturating_mul(s.into()))
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
}
