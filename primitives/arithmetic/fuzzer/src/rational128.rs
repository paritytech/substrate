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
//! Running this fuzzer can be done with `cargo hfuzz run rational128`. `honggfuzz` CLI options can
//! be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug rational128 hfuzz_workspace/rational128/*.fuzz`.
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
		return Zero::zero();
	}
	let c = c.max(1);

	// e for extended
	let ae: U256 = a.into();
	let be: U256 = b.into();
	let ce: U256 = c.into();

	let r = ae * be / ce;
	if r > u128::max_value().into() {
		a
	} else {
		r.as_u128()
	}
}
