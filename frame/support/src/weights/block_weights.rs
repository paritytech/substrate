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

//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-10-11 (Y/M/D)
//! HOSTNAME: `bm2`, CPU: `Intel(R) Core(TM) i7-7700K CPU @ 4.20GHz`
//!
//! SHORT-NAME: `block`, LONG-NAME: `BlockExecution`, RUNTIME: `Development`
//! WARMUPS: `10`, REPEAT: `100`
//! WEIGHT-PATH: `./frame/support/src/weights/`
//! WEIGHT-METRIC: `Average`, WEIGHT-MUL: `1.0`, WEIGHT-ADD: `0`

// Executed Command:
//   ./target/production/substrate
//   benchmark
//   overhead
//   --chain=dev
//   --execution=wasm
//   --wasm-execution=compiled
//   --weight-path=./frame/support/src/weights/
//   --warmup=10
//   --repeat=100
//   --header=HEADER-APACHE2

use sp_core::parameter_types;
use sp_weights::{constants::WEIGHT_PER_NANOS, Weight};

parameter_types! {
	/// Time to execute an empty block.
	/// Calculated by multiplying the *Average* with `1.0` and adding `0`.
	///
	/// Statistics in nanoseconds:
	///   Min, Max: 337_266, 439_477
	///   Average:  342_097
	///   Median:   339_137
	///   Std-Dev:  11478.95
	///
	/// Percentiles in nanoseconds:
	///   99th: 367_555
	///   95th: 355_170
	///   75th: 340_276
	pub const BlockExecutionRefTime: u64 = WEIGHT_PER_NANOS.ref_time().saturating_mul(342_097);

	/// Storage proof size to prove the execution of an empty block.
	///
	/// THIS IS NOT THE POV SIZE. The PoV size additionally includes the block size.
	///
	/// Compaction would result in `3_473` byte.
	/// Compaction and compression would result in `3_163` byte.
	pub const EmptyBlockProofSize: u64 = 4_857;

	/// Storage proof size to prove the execution of a block with at least one extrinsic.
	///
	/// THIS IS NOT THE POV SIZE. The PoV size additionally includes the block size.
	///
	/// Compaction would result in `3_879` byte.
	/// Compaction and compression would result in `3_365` byte.
	pub const NonEmptyBlockProofSize: u64 = 5_422;

	/// Weight to execute an empty block.
	///
	/// We do not distinguish between the weight of empty or non-empty blocks and
	/// therefore use the assumed larger one, being non-empty.
	pub const BlockExecutionWeight: Weight = Weight::from_components(
			BlockExecutionRefTime::get(),
			NonEmptyBlockProofSize::get(),
		);
}

#[cfg(test)]
mod test_weights {
	use sp_weights::constants::{WEIGHT_PER_MICROS, WEIGHT_PER_MILLIS};

	/// Checks that the weight constants exists and are sane.
	// NOTE: If this test fails but you are sure that the generated values are fine,
	// you can delete it.
	#[test]
	fn sane() {
		let w = super::BlockExecutionWeight::get();

		assert!(
			w.ref_time() >= 100u64 * WEIGHT_PER_MICROS.ref_time(),
			"Ref time of executing an empty block should be at least 100 µs."
		);
		assert!(
			w.ref_time() <= 50u64 * WEIGHT_PER_MILLIS.ref_time(),
			"Ref time of executing an empty block should be at most 50 ms."
		);
		assert!(EmptyBlockProofSize::get() > 0, "The proof size of an empty block cannot be zero");
		assert!(
			NonEmptyBlockProofSize::get() > 0,
			"The proof size of a non-empty block cannot be zero"
		);
		assert!(
			EmptyBlockProofSize::get() <= 1024 * 1024,
			"The proof size of an empty block should be smaller than 1 MiB"
		);
		assert!(
			NonEmptyBlockProofSize::get() <= 2 * 1024 * 1024,
			"The proof size of a non-empty block should be smaller than 2 MiB"
		);
		assert!(
			EmptyBlockProofSize::get() >= NonEmptyBlockProofSize::get(),
			"The proof size of a non-empty block should be at least that of an empty block"
		);
		assert!(
			BlockExecutionWeight::get().proof_size ==
				EmptyBlockProofSize::get().max(NonEmptyBlockProofSize::get()),
			"Block weight is has wrong proof size"
		);
	}
}
