// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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
//! Running this fuzzer can be done with `cargo hfuzz run per_thing_rational`. `honggfuzz` CLI
//! options can be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug per_thing_rational hfuzz_workspace/per_thing_rational/*.fuzz`.

use honggfuzz::fuzz;
use sp_arithmetic::{traits::SaturatedConversion, PerThing, PerU16, Perbill, Percent, Perquintill};

fn main() {
	loop {
		fuzz!(|data: ((u16, u16), (u32, u32), (u64, u64))| {
			let (u16_pair, u32_pair, u64_pair) = data;

			// peru16
			let (smaller, bigger) = (u16_pair.0.min(u16_pair.1), u16_pair.0.max(u16_pair.1));
			let ratio = PerU16::from_rational(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				PerU16::from_float(smaller as f64 / bigger.max(1) as f64),
				1,
			);
			let (smaller, bigger) = (u32_pair.0.min(u32_pair.1), u32_pair.0.max(u32_pair.1));
			let ratio = PerU16::from_rational(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				PerU16::from_float(smaller as f64 / bigger.max(1) as f64),
				1,
			);
			let (smaller, bigger) = (u64_pair.0.min(u64_pair.1), u64_pair.0.max(u64_pair.1));
			let ratio = PerU16::from_rational(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				PerU16::from_float(smaller as f64 / bigger.max(1) as f64),
				1,
			);

			// percent
			let (smaller, bigger) = (u16_pair.0.min(u16_pair.1), u16_pair.0.max(u16_pair.1));
			let ratio = Percent::from_rational(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				Percent::from_float(smaller as f64 / bigger.max(1) as f64),
				1,
			);

			let (smaller, bigger) = (u32_pair.0.min(u32_pair.1), u32_pair.0.max(u32_pair.1));
			let ratio = Percent::from_rational(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				Percent::from_float(smaller as f64 / bigger.max(1) as f64),
				1,
			);

			let (smaller, bigger) = (u64_pair.0.min(u64_pair.1), u64_pair.0.max(u64_pair.1));
			let ratio = Percent::from_rational(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				Percent::from_float(smaller as f64 / bigger.max(1) as f64),
				1,
			);

			// perbill
			let (smaller, bigger) = (u32_pair.0.min(u32_pair.1), u32_pair.0.max(u32_pair.1));
			let ratio = Perbill::from_rational(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				Perbill::from_float(smaller as f64 / bigger.max(1) as f64),
				100,
			);

			let (smaller, bigger) = (u64_pair.0.min(u64_pair.1), u64_pair.0.max(u64_pair.1));
			let ratio = Perbill::from_rational(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				Perbill::from_float(smaller as f64 / bigger.max(1) as f64),
				100,
			);

			// perquintillion
			let (smaller, bigger) = (u64_pair.0.min(u64_pair.1), u64_pair.0.max(u64_pair.1));
			let ratio = Perquintill::from_rational(smaller, bigger);
			assert_per_thing_equal_error(
				ratio,
				Perquintill::from_float(smaller as f64 / bigger.max(1) as f64),
				1000,
			);
		})
	}
}

fn assert_per_thing_equal_error<P: PerThing>(a: P, b: P, err: u128) {
	let a_abs = a.deconstruct().saturated_into::<u128>();
	let b_abs = b.deconstruct().saturated_into::<u128>();
	let diff = a_abs.max(b_abs) - a_abs.min(b_abs);
	assert!(diff <= err, "{:?} !~ {:?}", a, b);
}
