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
//! DATE: 2022-10-13 (Y/M/D)
//! HOSTNAME: `bm2`, CPU: `Intel(R) Core(TM) i7-7700K CPU @ 4.20GHz`
//!
//! SHORT-NAME: `extrinsic`, LONG-NAME: `ExtrinsicBase`, RUNTIME: `Development`
//! WARMUPS: `10`, REPEAT: `100`
//! WEIGHT-PATH: `./frame/support/src/weights/`
//! WEIGHT-METRIC: `Average`, WEIGHT-MUL: `1.0`, WEIGHT-ADD: `0`

// Executed Command:
//   target/production/substrate
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
	/// Time to execute a NO-OP extrinsic. For example `System::remark`.
	/// Calculated by multiplying the *Average* with `1.0` and adding `0`.
	///
	/// Statistics in nanoseconds:
	///   Min, Max: 98_040, 99_044
	///   Average:  98_302
	///   Median:   98_283
	///   Std-Dev:  155.86
	///
	/// Percentiles in nanoseconds:
	///   99th: 98_692
	///   95th: 98_553
	///   75th: 98_387
	pub const ExtrinsicBaseRefTime: u64 = WEIGHT_PER_NANOS.ref_time().saturating_mul(98_302);

	/// Weight to execute a NO-OP extrinsic. For example `System::remark`.
	pub const ExtrinsicBaseWeight: Weight = Weight::from_parts(
			ExtrinsicBaseRefTime::get(),
			// There is no proof size consumed by a NO-OP extrinsic.
			0,
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
		use super::*;

		assert!(
			ExtrinsicBaseRefTime::get() >= 10u64 * WEIGHT_PER_MICROS.ref_time(),
			"Ref time of executing a NO-OP extrinsic should be at least 10 µs."
		);
		assert!(
			ExtrinsicBaseRefTime::get() <= WEIGHT_PER_MILLIS.ref_time(),
			"Ref time of executing a NO-OP extrinsic should be at least 1 ms."
		);
	}
}
