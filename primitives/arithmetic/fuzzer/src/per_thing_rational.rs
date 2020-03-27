// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # Running
//! Running this fuzzer can be done with `cargo hfuzz run per_thing_rational`. `honggfuzz` CLI options can
//! be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug per_thing_rational hfuzz_workspace/per_thing_rational/*.fuzz`.

use honggfuzz::fuzz;
use sp_arithmetic::{
	PerThing, PerU16, Percent, Perbill, Perquintill, traits::SaturatedConversion,
};

fn main() {
	loop {
		fuzz!(|
			data: ((u16, u16), (u32, u32), (u64, u64))
		| {

			let (u16_pair, u32_pair, u64_pair) = data;

			// peru16
			let (smaller, bigger) = (u16_pair.0.min(u16_pair.1), u16_pair.0.max(u16_pair.1));
			let ratio = PerU16::from_rational_approximation(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				PerU16::from_fraction(smaller as f64 / bigger.max(1) as f64),
				1,
			);
			let (smaller, bigger) = (u32_pair.0.min(u32_pair.1), u32_pair.0.max(u32_pair.1));
			let ratio = PerU16::from_rational_approximation(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				PerU16::from_fraction(smaller as f64 / bigger.max(1) as f64),
				1,
			);
			let (smaller, bigger) = (u64_pair.0.min(u64_pair.1), u64_pair.0.max(u64_pair.1));
			let ratio = PerU16::from_rational_approximation(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				PerU16::from_fraction(smaller as f64 / bigger.max(1) as f64),
				1,
			);

			// percent
			let (smaller, bigger) = (u16_pair.0.min(u16_pair.1), u16_pair.0.max(u16_pair.1));
			let ratio = Percent::from_rational_approximation(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				Percent::from_fraction(smaller as f64 / bigger.max(1) as f64),
				1,
			);

			let (smaller, bigger) = (u32_pair.0.min(u32_pair.1), u32_pair.0.max(u32_pair.1));
			let ratio = Percent::from_rational_approximation(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				Percent::from_fraction(smaller as f64 / bigger.max(1) as f64),
				1,
			);

			let (smaller, bigger) = (u64_pair.0.min(u64_pair.1), u64_pair.0.max(u64_pair.1));
			let ratio = Percent::from_rational_approximation(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				Percent::from_fraction(smaller as f64 / bigger.max(1) as f64),
				1,
			);

			// perbill
			let (smaller, bigger) = (u32_pair.0.min(u32_pair.1), u32_pair.0.max(u32_pair.1));
			let ratio = Perbill::from_rational_approximation(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				Perbill::from_fraction(smaller as f64 / bigger.max(1) as f64),
				100,
			);

			let (smaller, bigger) = (u64_pair.0.min(u64_pair.1), u64_pair.0.max(u64_pair.1));
			let ratio = Perbill::from_rational_approximation(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				Perbill::from_fraction(smaller as f64 / bigger.max(1) as f64),
				100,
			);

			// perquintillion
			let (smaller, bigger) = (u64_pair.0.min(u64_pair.1), u64_pair.0.max(u64_pair.1));
			let ratio = Perquintill::from_rational_approximation(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				Perquintill::from_fraction(smaller as f64 / bigger.max(1) as f64),
				1000,
			);

		})
	}
}

fn assert_per_thing_equal_error<T: PerThing>(a: T, b: T, err: u128) {
	let a_abs = a.deconstruct().saturated_into::<u128>();
	let b_abs = b.deconstruct().saturated_into::<u128>();
	let diff = a_abs.max(b_abs) - a_abs.min(b_abs);
	dbg!(&diff);
	assert!(diff <= err, "{:?} !~ {:?}", a, b);
}
