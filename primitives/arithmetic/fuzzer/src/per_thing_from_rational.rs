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
use sp_arithmetic::{
	traits::SaturatedConversion, PerThing, Perbill, Percent, Perquintill, Rounding::*, *,
};

/// Tries to demonstrate that `from_rational` is incorrect for any rounding modes.
///
/// NOTE: This `Fraction` library is really slow. Using f128/f256 does not work for the large
/// numbers. But an optimization could be done do use either floats or Fraction depending on the
/// size of the inputs.
fn main() {
	loop {
		fuzz!(|data: (u128, u128, ArbitraryRounding)| {
			let (n, d, r) = (data.0.min(data.1), data.0.max(data.1).max(1), data.2);

			check::<PerU16>(n, d, r.0);
			check::<Percent>(n, d, r.0);
			check::<Permill>(n, d, r.0);
			check::<Perbill>(n, d, r.0);
			check::<Perquintill>(n, d, r.0);
		})
	}
}

/// Assert that the parts of `from_rational` are correct for the given rounding mode.
fn check<Per: PerThing>(a: u128, b: u128, r: Rounding)
where
	Per::Inner: Into<u128>,
{
	let approx_ratio = Per::from_rational_with_rounding(a, b, r).unwrap();
	let approx_parts = Fraction::from(approx_ratio.deconstruct().saturated_into::<u128>());

	let perfect_ratio = if a == 0 && b == 0 {
		Fraction::from(1)
	} else {
		Fraction::from(a) / Fraction::from(b.max(1))
	};
	let perfect_parts = round(perfect_ratio * Fraction::from(Per::ACCURACY.into()), r);

	assert_eq!(
		approx_parts, perfect_parts,
		"approx_parts: {}, perfect_parts: {}, a: {}, b: {}",
		approx_parts, perfect_parts, a, b
	);
}

/// Round a `Fraction` according to the given mode.
fn round(f: Fraction, r: Rounding) -> Fraction {
	match r {
		Up => f.ceil(),
		NearestPrefUp =>
			if f.fract() < Fraction::from(0.5) {
				f.floor()
			} else {
				f.ceil()
			},
		Down => f.floor(),
		NearestPrefDown =>
			if f.fract() > Fraction::from(0.5) {
				f.ceil()
			} else {
				f.floor()
			},
	}
}

/// An [`arbitrary::Arbitrary`] [`Rounding`] mode.
struct ArbitraryRounding(Rounding);
impl arbitrary::Arbitrary<'_> for ArbitraryRounding {
	fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
		Ok(Self(match u.int_in_range(0..=3).unwrap() {
			0 => Up,
			1 => NearestPrefUp,
			2 => Down,
			3 => NearestPrefDown,
			_ => unreachable!(),
		}))
	}
}
