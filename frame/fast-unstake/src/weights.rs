// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Autogenerated weights for pallet_fast_unstake
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-01-13, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! HOSTNAME: `bm3`, CPU: `Intel(R) Core(TM) i7-7700K CPU @ 4.20GHz`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// /home/benchbot/cargo_target_dir/production/substrate
// benchmark
// pallet
// --steps=50
// --repeat=20
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --json-file=/var/lib/gitlab-runner/builds/zyw4fam_/0/parity/mirrors/substrate/.git/.artifacts/bench.json
// --pallet=pallet_fast_unstake
// --chain=dev
// --header=./HEADER-APACHE2
// --output=./frame/fast-unstake/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_fast_unstake.
pub trait WeightInfo {
	fn on_idle_unstake(b: u32, ) -> Weight;
	fn on_idle_check(x: u32, b: u32, ) -> Weight;
	fn register_fast_unstake() -> Weight;
	fn deregister() -> Weight;
	fn control() -> Weight;
}

/// Weights for pallet_fast_unstake using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: FastUnstake ErasToCheckPerBlock (r:1 w:0)
	// Storage: Staking ValidatorCount (r:1 w:0)
	// Storage: FastUnstake Head (r:1 w:1)
	// Storage: FastUnstake CounterForQueue (r:1 w:0)
	// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:0)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking SlashingSpans (r:1 w:0)
	// Storage: Staking Bonded (r:1 w:1)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:0)
	// Storage: System Account (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Staking Ledger (r:0 w:1)
	// Storage: Staking Payee (r:0 w:1)
	/// The range of component `b` is `[1, 32]`.
	fn on_idle_unstake(b: u32, ) -> Weight {
		// Minimum execution time: 103_719 nanoseconds.
		Weight::from_ref_time(75_165_988)
			// Standard Error: 46_999
			.saturating_add(Weight::from_ref_time(37_374_141).saturating_mul(b.into()))
			.saturating_add(T::DbWeight::get().reads(6))
			.saturating_add(T::DbWeight::get().reads((6_u64).saturating_mul(b.into())))
			.saturating_add(T::DbWeight::get().writes(1))
			.saturating_add(T::DbWeight::get().writes((5_u64).saturating_mul(b.into())))
	}
	// Storage: FastUnstake ErasToCheckPerBlock (r:1 w:0)
	// Storage: Staking ValidatorCount (r:1 w:0)
	// Storage: FastUnstake Head (r:1 w:1)
	// Storage: FastUnstake CounterForQueue (r:1 w:0)
	// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:0)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking ErasStakers (r:17 w:0)
	/// The range of component `u` is `[1, 16]`.
	/// The range of component `v` is `[1, 16]`.
	/// The range of component `b` is `[1, 32]`.
	fn on_idle_check(u: u32, v: u32, b: u32, ) -> Weight {
		// Minimum execution time: 2_397_640 nanoseconds.
		Weight::from_ref_time(2_429_325_000)
			// Standard Error: 56_578_790
			.saturating_add(Weight::from_ref_time(829_150_656).saturating_mul(u.into()))
			// Standard Error: 56_578_790
			.saturating_add(Weight::from_ref_time(670_255_176).saturating_mul(v.into()))
			// Standard Error: 28_171_558
			.saturating_add(Weight::from_ref_time(398_637_537).saturating_mul(b.into()))
			.saturating_add(T::DbWeight::get().reads(23))
			.saturating_add(T::DbWeight::get().reads((10_u64).saturating_mul(u.into())))
			.saturating_add(T::DbWeight::get().reads((9_u64).saturating_mul(v.into())))
			.saturating_add(T::DbWeight::get().writes(1))
	}
	// Storage: FastUnstake ErasToCheckPerBlock (r:1 w:0)
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: FastUnstake Queue (r:1 w:1)
	// Storage: FastUnstake Head (r:1 w:0)
	// Storage: Staking Bonded (r:1 w:0)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking CounterForNominators (r:1 w:1)
	// Storage: VoterList ListNodes (r:2 w:2)
	// Storage: VoterList ListBags (r:1 w:1)
	// Storage: VoterList CounterForListNodes (r:1 w:1)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: FastUnstake CounterForQueue (r:1 w:1)
	fn register_fast_unstake() -> Weight {
		// Minimum execution time: 148_327 nanoseconds.
		Weight::from_ref_time(149_655_000)
			.saturating_add(T::DbWeight::get().reads(15))
			.saturating_add(T::DbWeight::get().writes(10))
	}
	// Storage: FastUnstake ErasToCheckPerBlock (r:1 w:0)
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: FastUnstake Queue (r:1 w:1)
	// Storage: FastUnstake Head (r:1 w:0)
	// Storage: FastUnstake CounterForQueue (r:1 w:1)
	fn deregister() -> Weight {
		// Minimum execution time: 68_305 nanoseconds.
		Weight::from_ref_time(69_343_000)
			.saturating_add(T::DbWeight::get().reads(5))
			.saturating_add(T::DbWeight::get().writes(2))
	}
	// Storage: FastUnstake ErasToCheckPerBlock (r:0 w:1)
	fn control() -> Weight {
		// Minimum execution time: 4_732 nanoseconds.
		Weight::from_ref_time(4_971_000)
			.saturating_add(T::DbWeight::get().writes(1))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: FastUnstake ErasToCheckPerBlock (r:1 w:0)
	// Storage: Staking ValidatorCount (r:1 w:0)
	// Storage: FastUnstake Head (r:1 w:1)
	// Storage: FastUnstake CounterForQueue (r:1 w:0)
	// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:0)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking SlashingSpans (r:1 w:0)
	// Storage: Staking Bonded (r:1 w:1)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:0)
	// Storage: System Account (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Staking Ledger (r:0 w:1)
	// Storage: Staking Payee (r:0 w:1)
	/// The range of component `b` is `[1, 32]`.
	fn on_idle_unstake(b: u32, ) -> Weight {
		// Minimum execution time: 103_719 nanoseconds.
		Weight::from_ref_time(75_165_988)
			// Standard Error: 46_999
			.saturating_add(Weight::from_ref_time(37_374_141).saturating_mul(b.into()))
			.saturating_add(RocksDbWeight::get().reads(6))
			.saturating_add(RocksDbWeight::get().reads((6_u64).saturating_mul(b.into())))
			.saturating_add(RocksDbWeight::get().writes(1))
			.saturating_add(RocksDbWeight::get().writes((5_u64).saturating_mul(b.into())))
	}
	// Storage: FastUnstake ErasToCheckPerBlock (r:1 w:0)
	// Storage: Staking ValidatorCount (r:1 w:0)
	// Storage: FastUnstake Head (r:1 w:1)
	// Storage: FastUnstake CounterForQueue (r:1 w:0)
	// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:0)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking ErasStakers (r:17 w:0)
	/// The range of component `u` is `[1, 16]`.
	/// The range of component `v` is `[1, 16]`.
	/// The range of component `b` is `[1, 32]`.
	fn on_idle_check(u: u32, v: u32, b: u32, ) -> Weight {
		// Minimum execution time: 2_397_640 nanoseconds.
		Weight::from_ref_time(2_429_325_000)
			// Standard Error: 56_578_790
			.saturating_add(Weight::from_ref_time(829_150_656).saturating_mul(u.into()))
			// Standard Error: 56_578_790
			.saturating_add(Weight::from_ref_time(670_255_176).saturating_mul(v.into()))
			// Standard Error: 28_171_558
			.saturating_add(Weight::from_ref_time(398_637_537).saturating_mul(b.into()))
			.saturating_add(RocksDbWeight::get().reads(23))
			.saturating_add(RocksDbWeight::get().reads((10_u64).saturating_mul(u.into())))
			.saturating_add(RocksDbWeight::get().reads((9_u64).saturating_mul(v.into())))
			.saturating_add(RocksDbWeight::get().writes(1))
	}
	// Storage: FastUnstake ErasToCheckPerBlock (r:1 w:0)
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: FastUnstake Queue (r:1 w:1)
	// Storage: FastUnstake Head (r:1 w:0)
	// Storage: Staking Bonded (r:1 w:0)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking CounterForNominators (r:1 w:1)
	// Storage: VoterList ListNodes (r:2 w:2)
	// Storage: VoterList ListBags (r:1 w:1)
	// Storage: VoterList CounterForListNodes (r:1 w:1)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: FastUnstake CounterForQueue (r:1 w:1)
	fn register_fast_unstake() -> Weight {
		// Minimum execution time: 148_327 nanoseconds.
		Weight::from_ref_time(149_655_000)
			.saturating_add(RocksDbWeight::get().reads(15))
			.saturating_add(RocksDbWeight::get().writes(10))
	}
	// Storage: FastUnstake ErasToCheckPerBlock (r:1 w:0)
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: FastUnstake Queue (r:1 w:1)
	// Storage: FastUnstake Head (r:1 w:0)
	// Storage: FastUnstake CounterForQueue (r:1 w:1)
	fn deregister() -> Weight {
		// Minimum execution time: 68_305 nanoseconds.
		Weight::from_ref_time(69_343_000)
			.saturating_add(RocksDbWeight::get().reads(5))
			.saturating_add(RocksDbWeight::get().writes(2))
	}
	// Storage: FastUnstake ErasToCheckPerBlock (r:0 w:1)
	fn control() -> Weight {
		// Minimum execution time: 4_732 nanoseconds.
		Weight::from_ref_time(4_971_000)
			.saturating_add(RocksDbWeight::get().writes(1))
	}
}
