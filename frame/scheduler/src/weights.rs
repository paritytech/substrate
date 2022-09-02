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

//! Autogenerated weights for pallet_scheduler
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
// --pallet=pallet_scheduler
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --template=./.maintain/frame-weight-template.hbs
// --output=./frame/scheduler/src/weights.rs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{RefTimeWeight, Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_scheduler.
pub trait WeightInfo {
	fn on_initialize_periodic_named_resolved(s: u32, ) -> Weight;
	fn on_initialize_named_resolved(s: u32, ) -> Weight;
	fn on_initialize_periodic_resolved(s: u32, ) -> Weight;
	fn on_initialize_resolved(s: u32, ) -> Weight;
	fn on_initialize_named_aborted(s: u32, ) -> Weight;
	fn on_initialize_aborted(s: u32, ) -> Weight;
	fn on_initialize_periodic_named(s: u32, ) -> Weight;
	fn on_initialize_periodic(s: u32, ) -> Weight;
	fn on_initialize_named(s: u32, ) -> Weight;
	fn on_initialize(s: u32, ) -> Weight;
	fn schedule(s: u32, ) -> Weight;
	fn cancel(s: u32, ) -> Weight;
	fn schedule_named(s: u32, ) -> Weight;
	fn cancel_named(s: u32, ) -> Weight;
}

/// Weights for pallet_scheduler using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: Scheduler Agenda (r:2 w:2)
	// Storage: Preimage PreimageFor (r:1 w:1)
	// Storage: Preimage StatusFor (r:1 w:1)
	// Storage: Scheduler Lookup (r:0 w:1)
	fn on_initialize_periodic_named_resolved(s: u32, ) -> Weight {
		Weight::from_ref_time(9_994_000 as RefTimeWeight)
			// Standard Error: 20_000
			.saturating_add(Weight::from_ref_time(19_843_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((3 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((4 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	// Storage: Preimage PreimageFor (r:1 w:1)
	// Storage: Preimage StatusFor (r:1 w:1)
	// Storage: Scheduler Lookup (r:0 w:1)
	fn on_initialize_named_resolved(s: u32, ) -> Weight {
		Weight::from_ref_time(10_318_000 as RefTimeWeight)
			// Standard Error: 17_000
			.saturating_add(Weight::from_ref_time(15_451_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((2 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((3 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:2 w:2)
	// Storage: Preimage PreimageFor (r:1 w:1)
	// Storage: Preimage StatusFor (r:1 w:1)
	fn on_initialize_periodic_resolved(s: u32, ) -> Weight {
		Weight::from_ref_time(11_675_000 as RefTimeWeight)
			// Standard Error: 17_000
			.saturating_add(Weight::from_ref_time(17_019_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((3 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((3 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	// Storage: Preimage PreimageFor (r:1 w:1)
	// Storage: Preimage StatusFor (r:1 w:1)
	fn on_initialize_resolved(s: u32, ) -> Weight {
		Weight::from_ref_time(11_934_000 as RefTimeWeight)
			// Standard Error: 11_000
			.saturating_add(Weight::from_ref_time(14_134_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((2 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((2 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:2 w:2)
	// Storage: Preimage PreimageFor (r:1 w:0)
	// Storage: Scheduler Lookup (r:0 w:1)
	fn on_initialize_named_aborted(s: u32, ) -> Weight {
		Weight::from_ref_time(7_279_000 as RefTimeWeight)
			// Standard Error: 5_000
			.saturating_add(Weight::from_ref_time(5_388_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes(2 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:2 w:2)
	// Storage: Preimage PreimageFor (r:1 w:0)
	fn on_initialize_aborted(s: u32, ) -> Weight {
		Weight::from_ref_time(8_619_000 as RefTimeWeight)
			// Standard Error: 4_000
			.saturating_add(Weight::from_ref_time(2_969_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes(2 as RefTimeWeight))
	}
	// Storage: Scheduler Agenda (r:2 w:2)
	// Storage: Scheduler Lookup (r:0 w:1)
	fn on_initialize_periodic_named(s: u32, ) -> Weight {
		Weight::from_ref_time(16_129_000 as RefTimeWeight)
			// Standard Error: 7_000
			.saturating_add(Weight::from_ref_time(9_772_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((2 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:2 w:2)
	fn on_initialize_periodic(s: u32, ) -> Weight {
		Weight::from_ref_time(15_785_000 as RefTimeWeight)
			// Standard Error: 5_000
			.saturating_add(Weight::from_ref_time(7_208_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	// Storage: Scheduler Lookup (r:0 w:1)
	fn on_initialize_named(s: u32, ) -> Weight {
		Weight::from_ref_time(15_778_000 as RefTimeWeight)
			// Standard Error: 3_000
			.saturating_add(Weight::from_ref_time(5_597_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	fn on_initialize(s: u32, ) -> Weight {
		Weight::from_ref_time(15_912_000 as RefTimeWeight)
			// Standard Error: 5_000
			.saturating_add(Weight::from_ref_time(4_530_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	fn schedule(s: u32, ) -> Weight {
		Weight::from_ref_time(18_013_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(87_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	// Storage: Scheduler Lookup (r:0 w:1)
	fn cancel(s: u32, ) -> Weight {
		Weight::from_ref_time(18_131_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(595_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(2 as RefTimeWeight))
	}
	// Storage: Scheduler Lookup (r:1 w:1)
	// Storage: Scheduler Agenda (r:1 w:1)
	fn schedule_named(s: u32, ) -> Weight {
		Weight::from_ref_time(21_230_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(98_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(2 as RefTimeWeight))
	}
	// Storage: Scheduler Lookup (r:1 w:1)
	// Storage: Scheduler Agenda (r:1 w:1)
	fn cancel_named(s: u32, ) -> Weight {
		Weight::from_ref_time(20_139_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(595_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(2 as RefTimeWeight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: Scheduler Agenda (r:2 w:2)
	// Storage: Preimage PreimageFor (r:1 w:1)
	// Storage: Preimage StatusFor (r:1 w:1)
	// Storage: Scheduler Lookup (r:0 w:1)
	fn on_initialize_periodic_named_resolved(s: u32, ) -> Weight {
		Weight::from_ref_time(9_994_000 as RefTimeWeight)
			// Standard Error: 20_000
			.saturating_add(Weight::from_ref_time(19_843_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((3 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((4 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	// Storage: Preimage PreimageFor (r:1 w:1)
	// Storage: Preimage StatusFor (r:1 w:1)
	// Storage: Scheduler Lookup (r:0 w:1)
	fn on_initialize_named_resolved(s: u32, ) -> Weight {
		Weight::from_ref_time(10_318_000 as RefTimeWeight)
			// Standard Error: 17_000
			.saturating_add(Weight::from_ref_time(15_451_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((2 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((3 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:2 w:2)
	// Storage: Preimage PreimageFor (r:1 w:1)
	// Storage: Preimage StatusFor (r:1 w:1)
	fn on_initialize_periodic_resolved(s: u32, ) -> Weight {
		Weight::from_ref_time(11_675_000 as RefTimeWeight)
			// Standard Error: 17_000
			.saturating_add(Weight::from_ref_time(17_019_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((3 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((3 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	// Storage: Preimage PreimageFor (r:1 w:1)
	// Storage: Preimage StatusFor (r:1 w:1)
	fn on_initialize_resolved(s: u32, ) -> Weight {
		Weight::from_ref_time(11_934_000 as RefTimeWeight)
			// Standard Error: 11_000
			.saturating_add(Weight::from_ref_time(14_134_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((2 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((2 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:2 w:2)
	// Storage: Preimage PreimageFor (r:1 w:0)
	// Storage: Scheduler Lookup (r:0 w:1)
	fn on_initialize_named_aborted(s: u32, ) -> Weight {
		Weight::from_ref_time(7_279_000 as RefTimeWeight)
			// Standard Error: 5_000
			.saturating_add(Weight::from_ref_time(5_388_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes(2 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:2 w:2)
	// Storage: Preimage PreimageFor (r:1 w:0)
	fn on_initialize_aborted(s: u32, ) -> Weight {
		Weight::from_ref_time(8_619_000 as RefTimeWeight)
			// Standard Error: 4_000
			.saturating_add(Weight::from_ref_time(2_969_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes(2 as RefTimeWeight))
	}
	// Storage: Scheduler Agenda (r:2 w:2)
	// Storage: Scheduler Lookup (r:0 w:1)
	fn on_initialize_periodic_named(s: u32, ) -> Weight {
		Weight::from_ref_time(16_129_000 as RefTimeWeight)
			// Standard Error: 7_000
			.saturating_add(Weight::from_ref_time(9_772_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((2 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:2 w:2)
	fn on_initialize_periodic(s: u32, ) -> Weight {
		Weight::from_ref_time(15_785_000 as RefTimeWeight)
			// Standard Error: 5_000
			.saturating_add(Weight::from_ref_time(7_208_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	// Storage: Scheduler Lookup (r:0 w:1)
	fn on_initialize_named(s: u32, ) -> Weight {
		Weight::from_ref_time(15_778_000 as RefTimeWeight)
			// Standard Error: 3_000
			.saturating_add(Weight::from_ref_time(5_597_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	fn on_initialize(s: u32, ) -> Weight {
		Weight::from_ref_time(15_912_000 as RefTimeWeight)
			// Standard Error: 5_000
			.saturating_add(Weight::from_ref_time(4_530_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	fn schedule(s: u32, ) -> Weight {
		Weight::from_ref_time(18_013_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(87_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Scheduler Agenda (r:1 w:1)
	// Storage: Scheduler Lookup (r:0 w:1)
	fn cancel(s: u32, ) -> Weight {
		Weight::from_ref_time(18_131_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(595_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(2 as RefTimeWeight))
	}
	// Storage: Scheduler Lookup (r:1 w:1)
	// Storage: Scheduler Agenda (r:1 w:1)
	fn schedule_named(s: u32, ) -> Weight {
		Weight::from_ref_time(21_230_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(98_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(2 as RefTimeWeight))
	}
	// Storage: Scheduler Lookup (r:1 w:1)
	// Storage: Scheduler Agenda (r:1 w:1)
	fn cancel_named(s: u32, ) -> Weight {
		Weight::from_ref_time(20_139_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(595_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(2 as RefTimeWeight))
	}
}
