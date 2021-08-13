// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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
//! Running this fuzzer can be done with `cargo hfuzz run multiply_by_rational`. `honggfuzz` CLI
//! options can be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug multiply_by_rational hfuzz_workspace/multiply_by_rational/*.fuzz`.
//!
//! # More information
//! More information about `honggfuzz` can be found
//! [here](https://docs.rs/honggfuzz/).

use honggfuzz::fuzz;
use sp_arithmetic::{helpers_128bit::multiply_by_rational, traits::Zero};

fn main() {
	loop {
		fuzz!(|data: ([u8; 16], [u8; 16], [u8; 16])| {
			let (a_bytes, b_bytes, c_bytes) = data;
			let (a, b, c) = (
				u128::from_be_bytes(a_bytes),
				u128::from_be_bytes(b_bytes),
				u128::from_be_bytes(c_bytes),
			);

			println!("++ Equation: {} * {} / {}", a, b, c);

			// The point of this fuzzing is to make sure that `multiply_by_rational` is 100%
			// accurate as long as the value fits in a u128.
			if let Ok(result) = multiply_by_rational(a, b, c) {
				let truth = mul_div(a, b, c);

				if result != truth && result != truth + 1 {
					println!("++ Expected {}", truth);
					println!("+++++++ Got {}", result);
					panic!();
				}
			}
		})
	}
}

fn mul_div(a: u128, b: u128, c: u128) -> u128 {
	use primitive_types::U256;
	if a.is_zero() {
		return Zero::zero()
	}
	let c = c.max(1);

	// e for extended
	let ae: U256 = a.into();
	let be: U256 = b.into();
	let ce: U256 = c.into();

	let r = ae * be / ce;
	if r > u128::MAX.into() {
		a
	} else {
		r.as_u128()
	}
}
