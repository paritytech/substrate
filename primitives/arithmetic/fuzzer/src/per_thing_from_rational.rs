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

//! # Running
//! Running this fuzzer can be done with `cargo hfuzz run per_thing_from_rational`. `honggfuzz` CLI
//! options can be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug per_thing_from_rational hfuzz_workspace/per_thing_from_rational/*.fuzz`.

use fraction::prelude::BigFraction as Fraction;
use honggfuzz::fuzz;
use sp_arithmetic::{traits::SaturatedConversion, PerThing, Perbill, Percent, Perquintill, *};

/// Tries to demonstrate that `from_rational` is incorrect.
///
/// NOTE: This `Fraction` library is really slow. Using f128/f256 does not work for the large
/// numbers. But an optimization could be done do use either floats or Fraction depending on the
/// size of the inputs.
fn main() {
	loop {
		fuzz!(|data: (u128, u128)| {
			let (n, d) = (data.0.min(data.1), data.0.max(data.1).max(1));

			check::<PerU16>(n, d);
			check::<Percent>(n, d);
			check::<Perbill>(n, d);
			check::<Perquintill>(n, d);
		})
	}
}

/// Assert that the parts of `from_rational` are correct.
fn check<Per: PerThing>(a: u128, b: u128)
where
	Per::Inner: Into<u128>,
{
	let approx_ratio = Per::from_rational(a, b); // This rounds down.
	let approx_parts = Fraction::from(approx_ratio.deconstruct().saturated_into::<u128>());

	let perfect_ratio = if a == 0 && b == 0 {
		Fraction::from(1)
	} else {
		Fraction::from(a) / Fraction::from(b.max(1))
	};
	let perfect_parts = (perfect_ratio * Fraction::from(Per::ACCURACY.into())).floor();

	assert_eq!(
		approx_parts, perfect_parts,
		"approx_parts: {}, perfect_parts: {}, a: {}, b: {}",
		approx_parts, perfect_parts, a, b
	);
}
