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

//! Autogenerated weights for pallet_election_provider_multi_phase
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-03-16, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
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
// --pallet=pallet_election_provider_multi_phase
// --no-storage-info
// --no-median-slopes
// --no-min-squares
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/election-provider-multi-phase/src/weights.rs
// --header=./HEADER-APACHE2
// --template=./.maintain/frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_election_provider_multi_phase.
pub trait WeightInfo {
	fn on_initialize_nothing() -> Weight;
	fn on_initialize_open_signed() -> Weight;
	fn on_initialize_open_unsigned() -> Weight;
	fn finalize_signed_phase_accept_solution() -> Weight;
	fn finalize_signed_phase_reject_solution() -> Weight;
	fn create_snapshot_internal(v: u32, t: u32, ) -> Weight;
	fn elect_queued(a: u32, d: u32, ) -> Weight;
	fn submit() -> Weight;
	fn submit_unsigned(v: u32, t: u32, a: u32, d: u32, ) -> Weight;
	fn force_rotate_round() -> Weight;
	fn force_rotate_round_from_signed() -> Weight;
	fn feasibility_check(v: u32, t: u32, a: u32, d: u32, ) -> Weight;
}

/// Weights for pallet_election_provider_multi_phase using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: Staking CurrentEra (r:1 w:0)
	/// Proof: Staking CurrentEra (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Staking CurrentPlannedSession (r:1 w:0)
	/// Proof: Staking CurrentPlannedSession (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Staking ErasStartSessionIndex (r:1 w:0)
	/// Proof: Staking ErasStartSessionIndex (max_values: None, max_size: Some(16), added: 2491, mode: MaxEncodedLen)
	/// Storage: Babe EpochIndex (r:1 w:0)
	/// Proof: Babe EpochIndex (max_values: Some(1), max_size: Some(8), added: 503, mode: MaxEncodedLen)
	/// Storage: Babe GenesisSlot (r:1 w:0)
	/// Proof: Babe GenesisSlot (max_values: Some(1), max_size: Some(8), added: 503, mode: MaxEncodedLen)
	/// Storage: Babe CurrentSlot (r:1 w:0)
	/// Proof: Babe CurrentSlot (max_values: Some(1), max_size: Some(8), added: 503, mode: MaxEncodedLen)
	/// Storage: Staking ForceEra (r:1 w:0)
	/// Proof: Staking ForceEra (max_values: Some(1), max_size: Some(1), added: 496, mode: MaxEncodedLen)
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	fn on_initialize_nothing() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `994`
		//  Estimated: `14903`
		// Minimum execution time: 21_538_000 picoseconds.
		Weight::from_parts(22_045_000, 14903)
			.saturating_add(T::DbWeight::get().reads(8_u64))
	}
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	fn on_initialize_open_signed() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `114`
		//  Estimated: `3198`
		// Minimum execution time: 12_696_000 picoseconds.
		Weight::from_parts(12_950_000, 3198)
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	fn on_initialize_open_unsigned() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `114`
		//  Estimated: `3198`
		// Minimum execution time: 14_029_000 picoseconds.
		Weight::from_parts(14_288_000, 3198)
			.saturating_add(T::DbWeight::get().reads(2_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: ElectionProviderMultiPhase QueuedSolution (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase QueuedSolution (max_values: Some(1), max_size: None, mode: Measured)
	fn finalize_signed_phase_accept_solution() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `174`
		//  Estimated: `3767`
		// Minimum execution time: 26_468_000 picoseconds.
		Weight::from_parts(26_790_000, 3767)
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(2_u64))
	}
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	fn finalize_signed_phase_reject_solution() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `174`
		//  Estimated: `3593`
		// Minimum execution time: 18_401_000 picoseconds.
		Weight::from_parts(18_686_000, 3593)
			.saturating_add(T::DbWeight::get().reads(1_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: ElectionProviderMultiPhase SnapshotMetadata (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SnapshotMetadata (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase DesiredTargets (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase DesiredTargets (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Snapshot (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Snapshot (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `v` is `[1000, 2000]`.
	/// The range of component `t` is `[500, 1000]`.
	fn create_snapshot_internal(v: u32, _t: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 266_901_000 picoseconds.
		Weight::from_parts(270_251_000, 0)
			// Standard Error: 1_758
			.saturating_add(Weight::from_parts(167_310, 0).saturating_mul(v.into()))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: ElectionProviderMultiPhase SignedSubmissionIndices (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionIndices (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionNextIndex (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionNextIndex (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SnapshotMetadata (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SnapshotMetadata (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionsMap (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionsMap (max_values: None, max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase QueuedSolution (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase QueuedSolution (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase DesiredTargets (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase DesiredTargets (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Snapshot (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Snapshot (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `a` is `[500, 800]`.
	/// The range of component `d` is `[200, 400]`.
	fn elect_queued(a: u32, d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `337 + a * (768 ±0) + d * (48 ±0)`
		//  Estimated: `16191 + a * (6912 ±0) + d * (441 ±0)`
		// Minimum execution time: 286_523_000 picoseconds.
		Weight::from_parts(19_101_753, 16191)
			// Standard Error: 4_194
			.saturating_add(Weight::from_parts(398_102, 0).saturating_mul(a.into()))
			// Standard Error: 6_287
			.saturating_add(Weight::from_parts(188_928, 0).saturating_mul(d.into()))
			.saturating_add(T::DbWeight::get().reads(7_u64))
			.saturating_add(T::DbWeight::get().writes(8_u64))
			.saturating_add(Weight::from_parts(0, 6912).saturating_mul(a.into()))
			.saturating_add(Weight::from_parts(0, 441).saturating_mul(d.into()))
	}
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SnapshotMetadata (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase SnapshotMetadata (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: TransactionPayment NextFeeMultiplier (r:1 w:0)
	/// Proof: TransactionPayment NextFeeMultiplier (max_values: Some(1), max_size: Some(16), added: 511, mode: MaxEncodedLen)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionIndices (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionIndices (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionNextIndex (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionNextIndex (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionsMap (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionsMap (max_values: None, max_size: None, mode: Measured)
	fn submit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `893`
		//  Estimated: `11906`
		// Minimum execution time: 47_876_000 picoseconds.
		Weight::from_parts(48_464_000, 11906)
			.saturating_add(T::DbWeight::get().reads(5_u64))
			.saturating_add(T::DbWeight::get().writes(3_u64))
	}
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase DesiredTargets (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase DesiredTargets (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase QueuedSolution (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase QueuedSolution (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SnapshotMetadata (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase SnapshotMetadata (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Snapshot (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase Snapshot (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase MinimumUntrustedScore (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase MinimumUntrustedScore (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `v` is `[1000, 2000]`.
	/// The range of component `t` is `[500, 1000]`.
	/// The range of component `a` is `[500, 800]`.
	/// The range of component `d` is `[200, 400]`.
	fn submit_unsigned(v: u32, t: u32, a: u32, _d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `219 + v * (553 ±0) + t * (32 ±0)`
		//  Estimated: `11928 + v * (3871 ±0) + t * (224 ±0)`
		// Minimum execution time: 4_702_825_000 picoseconds.
		Weight::from_parts(4_752_015_000, 11928)
			// Standard Error: 14_906
			.saturating_add(Weight::from_parts(131_585, 0).saturating_mul(v.into()))
			// Standard Error: 44_174
			.saturating_add(Weight::from_parts(4_167_676, 0).saturating_mul(a.into()))
			.saturating_add(T::DbWeight::get().reads(7_u64))
			.saturating_add(T::DbWeight::get().writes(1_u64))
			.saturating_add(Weight::from_parts(0, 3871).saturating_mul(v.into()))
			.saturating_add(Weight::from_parts(0, 224).saturating_mul(t.into()))
	}
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SnapshotMetadata (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SnapshotMetadata (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase QueuedSolution (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase QueuedSolution (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase DesiredTargets (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase DesiredTargets (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Snapshot (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Snapshot (max_values: Some(1), max_size: None, mode: Measured)
	fn force_rotate_round() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `114`
		//  Estimated: `1674`
		// Minimum execution time: 17_000 nanoseconds.
		Weight::from_parts(18_000_000, 1674)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionIndices (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionIndices (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionNextIndex (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionNextIndex (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SnapshotMetadata (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SnapshotMetadata (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionsMap (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionsMap (max_values: None, max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase QueuedSolution (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase QueuedSolution (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase DesiredTargets (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase DesiredTargets (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Snapshot (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Snapshot (max_values: Some(1), max_size: None, mode: Measured)
	fn force_rotate_round_from_signed() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `138`
		//  Estimated: `6192`
		// Minimum execution time: 27_000 nanoseconds.
		Weight::from_parts(28_000_000, 6192)
			.saturating_add(RocksDbWeight::get().reads(6_u64))
			.saturating_add(RocksDbWeight::get().writes(8_u64))
	}
	/// Storage: ElectionProviderMultiPhase DesiredTargets (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase DesiredTargets (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Snapshot (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase Snapshot (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase MinimumUntrustedScore (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase MinimumUntrustedScore (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `v` is `[1000, 2000]`.
	/// The range of component `t` is `[500, 1000]`.
	/// The range of component `a` is `[500, 800]`.
	/// The range of component `d` is `[200, 400]`.
	fn feasibility_check(v: u32, t: u32, a: u32, _d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `194 + v * (553 ±0) + t * (32 ±0)`
		//  Estimated: `6716 + v * (2212 ±0) + t * (128 ±0)`
		// Minimum execution time: 4_069_075_000 picoseconds.
		Weight::from_parts(4_105_635_000, 6716)
			// Standard Error: 12_539
			.saturating_add(Weight::from_parts(163_040, 0).saturating_mul(v.into()))
			// Standard Error: 37_160
			.saturating_add(Weight::from_parts(3_343_858, 0).saturating_mul(a.into()))
			.saturating_add(T::DbWeight::get().reads(4_u64))
			.saturating_add(Weight::from_parts(0, 2212).saturating_mul(v.into()))
			.saturating_add(Weight::from_parts(0, 128).saturating_mul(t.into()))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// Storage: Staking CurrentEra (r:1 w:0)
	/// Proof: Staking CurrentEra (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Staking CurrentPlannedSession (r:1 w:0)
	/// Proof: Staking CurrentPlannedSession (max_values: Some(1), max_size: Some(4), added: 499, mode: MaxEncodedLen)
	/// Storage: Staking ErasStartSessionIndex (r:1 w:0)
	/// Proof: Staking ErasStartSessionIndex (max_values: None, max_size: Some(16), added: 2491, mode: MaxEncodedLen)
	/// Storage: Babe EpochIndex (r:1 w:0)
	/// Proof: Babe EpochIndex (max_values: Some(1), max_size: Some(8), added: 503, mode: MaxEncodedLen)
	/// Storage: Babe GenesisSlot (r:1 w:0)
	/// Proof: Babe GenesisSlot (max_values: Some(1), max_size: Some(8), added: 503, mode: MaxEncodedLen)
	/// Storage: Babe CurrentSlot (r:1 w:0)
	/// Proof: Babe CurrentSlot (max_values: Some(1), max_size: Some(8), added: 503, mode: MaxEncodedLen)
	/// Storage: Staking ForceEra (r:1 w:0)
	/// Proof: Staking ForceEra (max_values: Some(1), max_size: Some(1), added: 496, mode: MaxEncodedLen)
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	fn on_initialize_nothing() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `994`
		//  Estimated: `14903`
		// Minimum execution time: 21_538_000 picoseconds.
		Weight::from_parts(22_045_000, 14903)
			.saturating_add(RocksDbWeight::get().reads(8_u64))
	}
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	fn on_initialize_open_signed() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `114`
		//  Estimated: `3198`
		// Minimum execution time: 12_696_000 picoseconds.
		Weight::from_parts(12_950_000, 3198)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	fn on_initialize_open_unsigned() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `114`
		//  Estimated: `3198`
		// Minimum execution time: 14_029_000 picoseconds.
		Weight::from_parts(14_288_000, 3198)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	/// Storage: ElectionProviderMultiPhase QueuedSolution (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase QueuedSolution (max_values: Some(1), max_size: None, mode: Measured)
	fn finalize_signed_phase_accept_solution() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `174`
		//  Estimated: `3767`
		// Minimum execution time: 26_468_000 picoseconds.
		Weight::from_parts(26_790_000, 3767)
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(2_u64))
	}
	/// Storage: System Account (r:1 w:1)
	/// Proof: System Account (max_values: None, max_size: Some(128), added: 2603, mode: MaxEncodedLen)
	fn finalize_signed_phase_reject_solution() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `174`
		//  Estimated: `3593`
		// Minimum execution time: 18_401_000 picoseconds.
		Weight::from_parts(18_686_000, 3593)
			.saturating_add(RocksDbWeight::get().reads(1_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: ElectionProviderMultiPhase SnapshotMetadata (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SnapshotMetadata (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase DesiredTargets (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase DesiredTargets (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Snapshot (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Snapshot (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `v` is `[1000, 2000]`.
	/// The range of component `t` is `[500, 1000]`.
	fn create_snapshot_internal(v: u32, _t: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 266_901_000 picoseconds.
		Weight::from_parts(270_251_000, 0)
			// Standard Error: 1_758
			.saturating_add(Weight::from_parts(167_310, 0).saturating_mul(v.into()))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: ElectionProviderMultiPhase SignedSubmissionIndices (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionIndices (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionNextIndex (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionNextIndex (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SnapshotMetadata (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SnapshotMetadata (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionsMap (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionsMap (max_values: None, max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase QueuedSolution (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase QueuedSolution (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase DesiredTargets (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase DesiredTargets (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Snapshot (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Snapshot (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `a` is `[500, 800]`.
	/// The range of component `d` is `[200, 400]`.
	fn elect_queued(a: u32, d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `337 + a * (768 ±0) + d * (48 ±0)`
		//  Estimated: `16191 + a * (6912 ±0) + d * (441 ±0)`
		// Minimum execution time: 286_523_000 picoseconds.
		Weight::from_parts(19_101_753, 16191)
			// Standard Error: 4_194
			.saturating_add(Weight::from_parts(398_102, 0).saturating_mul(a.into()))
			// Standard Error: 6_287
			.saturating_add(Weight::from_parts(188_928, 0).saturating_mul(d.into()))
			.saturating_add(RocksDbWeight::get().reads(7_u64))
			.saturating_add(RocksDbWeight::get().writes(8_u64))
			.saturating_add(Weight::from_parts(0, 6912).saturating_mul(a.into()))
			.saturating_add(Weight::from_parts(0, 441).saturating_mul(d.into()))
	}
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SnapshotMetadata (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase SnapshotMetadata (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: TransactionPayment NextFeeMultiplier (r:1 w:0)
	/// Proof: TransactionPayment NextFeeMultiplier (max_values: Some(1), max_size: Some(16), added: 511, mode: MaxEncodedLen)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionIndices (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionIndices (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionNextIndex (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionNextIndex (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionsMap (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionsMap (max_values: None, max_size: None, mode: Measured)
	fn submit() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `893`
		//  Estimated: `11906`
		// Minimum execution time: 47_876_000 picoseconds.
		Weight::from_parts(48_464_000, 11906)
			.saturating_add(RocksDbWeight::get().reads(5_u64))
			.saturating_add(RocksDbWeight::get().writes(3_u64))
	}
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase DesiredTargets (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase DesiredTargets (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase QueuedSolution (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase QueuedSolution (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SnapshotMetadata (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase SnapshotMetadata (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Snapshot (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase Snapshot (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase MinimumUntrustedScore (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase MinimumUntrustedScore (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `v` is `[1000, 2000]`.
	/// The range of component `t` is `[500, 1000]`.
	/// The range of component `a` is `[500, 800]`.
	/// The range of component `d` is `[200, 400]`.
	fn submit_unsigned(v: u32, t: u32, a: u32, _d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `219 + v * (553 ±0) + t * (32 ±0)`
		//  Estimated: `11928 + v * (3871 ±0) + t * (224 ±0)`
		// Minimum execution time: 4_702_825_000 picoseconds.
		Weight::from_parts(4_752_015_000, 11928)
			// Standard Error: 14_906
			.saturating_add(Weight::from_parts(131_585, 0).saturating_mul(v.into()))
			// Standard Error: 44_174
			.saturating_add(Weight::from_parts(4_167_676, 0).saturating_mul(a.into()))
			.saturating_add(RocksDbWeight::get().reads(7_u64))
			.saturating_add(RocksDbWeight::get().writes(1_u64))
			.saturating_add(Weight::from_parts(0, 3871).saturating_mul(v.into()))
			.saturating_add(Weight::from_parts(0, 224).saturating_mul(t.into()))
	}
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SnapshotMetadata (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SnapshotMetadata (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase QueuedSolution (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase QueuedSolution (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase DesiredTargets (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase DesiredTargets (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Snapshot (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Snapshot (max_values: Some(1), max_size: None, mode: Measured)
	fn force_rotate_round() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `114`
		//  Estimated: `1674`
		// Minimum execution time: 17_000 nanoseconds.
		Weight::from_parts(18_000_000, 1674)
			.saturating_add(RocksDbWeight::get().reads(2_u64))
			.saturating_add(RocksDbWeight::get().writes(6_u64))
	}
	/// Storage: ElectionProviderMultiPhase CurrentPhase (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase CurrentPhase (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionIndices (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionIndices (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionNextIndex (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionNextIndex (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SnapshotMetadata (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase SnapshotMetadata (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase SignedSubmissionsMap (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase SignedSubmissionsMap (max_values: None, max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase QueuedSolution (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase QueuedSolution (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase DesiredTargets (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase DesiredTargets (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Snapshot (r:0 w:1)
	/// Proof Skipped: ElectionProviderMultiPhase Snapshot (max_values: Some(1), max_size: None, mode: Measured)
	fn force_rotate_round_from_signed() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `138`
		//  Estimated: `6192`
		// Minimum execution time: 27_000 nanoseconds.
		Weight::from_parts(28_000_000, 6192)
			.saturating_add(RocksDbWeight::get().reads(6_u64))
			.saturating_add(RocksDbWeight::get().writes(8_u64))
	}
	/// Storage: ElectionProviderMultiPhase DesiredTargets (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase DesiredTargets (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Snapshot (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase Snapshot (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase Round (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase Round (max_values: Some(1), max_size: None, mode: Measured)
	/// Storage: ElectionProviderMultiPhase MinimumUntrustedScore (r:1 w:0)
	/// Proof Skipped: ElectionProviderMultiPhase MinimumUntrustedScore (max_values: Some(1), max_size: None, mode: Measured)
	/// The range of component `v` is `[1000, 2000]`.
	/// The range of component `t` is `[500, 1000]`.
	/// The range of component `a` is `[500, 800]`.
	/// The range of component `d` is `[200, 400]`.
	fn feasibility_check(v: u32, t: u32, a: u32, _d: u32, ) -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `194 + v * (553 ±0) + t * (32 ±0)`
		//  Estimated: `6716 + v * (2212 ±0) + t * (128 ±0)`
		// Minimum execution time: 4_069_075_000 picoseconds.
		Weight::from_parts(4_105_635_000, 6716)
			// Standard Error: 12_539
			.saturating_add(Weight::from_parts(163_040, 0).saturating_mul(v.into()))
			// Standard Error: 37_160
			.saturating_add(Weight::from_parts(3_343_858, 0).saturating_mul(a.into()))
			.saturating_add(RocksDbWeight::get().reads(4_u64))
			.saturating_add(Weight::from_parts(0, 2212).saturating_mul(v.into()))
			.saturating_add(Weight::from_parts(0, 128).saturating_mul(t.into()))
	}
}
