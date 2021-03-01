// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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
//! Running this fuzzer can be done with `cargo hfuzz run fixed_point`. `honggfuzz` CLI options can
//! be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug fixed_point hfuzz_workspace/fixed_point/*.fuzz`.
//!
//! # More information
//! More information about `honggfuzz` can be found
//! [here](https://docs.rs/honggfuzz/).

use honggfuzz::fuzz;
use sp_arithmetic::{FixedPointNumber, FixedI64, traits::Saturating};

fn main() {
	loop {
		fuzz!(|data: (i32, i32)| {
			let x: i128 = data.0.into();
			let y: i128 = data.1.into();

			// Check `from_rational` and division are consistent.
			if y != 0 {
				let f1 = FixedI64::saturating_from_integer(x) / FixedI64::saturating_from_integer(y);
				let f2 = FixedI64::saturating_from_rational(x, y);
				assert_eq!(f1.into_inner(), f2.into_inner());
			}

			// Check `saturating_mul`.
			let a = FixedI64::saturating_from_rational(2, 5);
			let b = a.saturating_mul(FixedI64::saturating_from_integer(x));
			let n = b.into_inner() as i128;
			let m = 2i128 * x * FixedI64::accuracy() as i128 / 5i128;
			assert_eq!(n, m);

			// Check `saturating_mul` and division are inverse.
			if x != 0 {
				assert_eq!(a, b / FixedI64::saturating_from_integer(x));
			}

			// Check `reciprocal`.
			let r = a.reciprocal().unwrap().reciprocal().unwrap();
			assert_eq!(a, r);

			// Check addition.
			let a = FixedI64::saturating_from_integer(x);
			let b = FixedI64::saturating_from_integer(y);
			let c = FixedI64::saturating_from_integer(x.saturating_add(y));
			assert_eq!(a.saturating_add(b), c);

			// Check substraction.
			let a = FixedI64::saturating_from_integer(x);
			let b = FixedI64::saturating_from_integer(y);
			let c = FixedI64::saturating_from_integer(x.saturating_sub(y));
			assert_eq!(a.saturating_sub(b), c);

			// Check `saturating_mul_acc_int`.
			let a = FixedI64::saturating_from_rational(2, 5);
			let b = a.saturating_mul_acc_int(x);
			let xx = FixedI64::saturating_from_integer(x);
			let d = a.saturating_mul(xx).saturating_add(xx).into_inner() as i128 / FixedI64::accuracy() as i128;
			assert_eq!(b, d);
		});
	}
}
