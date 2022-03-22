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
//! Running this fuzzer can be done with `cargo hfuzz run biguint`. `honggfuzz` CLI options can
//! be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug biguint hfuzz_workspace/biguint/*.fuzz`.
//!
//! # More information
//! More information about `honggfuzz` can be found
//! [here](https://docs.rs/honggfuzz/).

use honggfuzz::fuzz;
use sp_arithmetic::biguint::{BigUint, Single};
use std::convert::TryFrom;

fn main() {
	loop {
		fuzz!(|data: (Vec<Single>, Vec<Single>, bool)| {
			let (mut digits_u, mut digits_v, return_remainder) = data;

			let mut u = BigUint::from_limbs(&digits_u);
			let mut v = BigUint::from_limbs(&digits_v);

			u.lstrip();
			v.lstrip();

			let ue = u128::try_from(u.clone());
			let ve = u128::try_from(v.clone());

			digits_u.reverse();
			digits_v.reverse();

			let num_u = num_bigint::BigUint::new(digits_u);
			let num_v = num_bigint::BigUint::new(digits_v);

			if check_digit_lengths(&u, &v, 4) {
				assert_eq!(u.cmp(&v), ue.cmp(&ve));
				assert_eq!(u.eq(&v), ue.eq(&ve));
			}

			if check_digit_lengths(&u, &v, 3) {
				let expected = ue.unwrap() + ve.unwrap();
				let t = u.clone().add(&v);
				assert_eq!(
					u128::try_from(t.clone()).unwrap(),
					expected,
					"{:?} + {:?} ===> {:?} != {:?}",
					u,
					v,
					t,
					expected,
				);
			}

			if check_digit_lengths(&u, &v, 4) {
				let expected = ue.unwrap().checked_sub(ve.unwrap());
				let t = u.clone().sub(&v);
				if expected.is_none() {
					assert!(t.is_err())
				} else {
					let t = t.unwrap();
					let expected = expected.unwrap();
					assert_eq!(
						u128::try_from(t.clone()).unwrap(),
						expected,
						"{:?} - {:?} ===> {:?} != {:?}",
						u,
						v,
						t,
						expected,
					);
				}
			}

			if check_digit_lengths(&u, &v, 2) {
				let expected = ue.unwrap() * ve.unwrap();
				let t = u.clone().mul(&v);
				assert_eq!(
					u128::try_from(t.clone()).unwrap(),
					expected,
					"{:?} * {:?} ===> {:?} != {:?}",
					u,
					v,
					t,
					expected,
				);
			}

			if check_digit_lengths(&u, &v, 4) {
				let (ue, ve) = (ue.unwrap(), ve.unwrap());
				if ve == 0 {
					return
				}
				let (q, r) = (ue / ve, ue % ve);
				if let Some((qq, rr)) = u.clone().div(&v, true) {
					assert_eq!(
						u128::try_from(qq.clone()).unwrap(),
						q,
						"{:?} / {:?} ===> {:?} != {:?}",
						u,
						v,
						qq,
						q,
					);
					assert_eq!(
						u128::try_from(rr.clone()).unwrap(),
						r,
						"{:?} % {:?} ===> {:?} != {:?}",
						u,
						v,
						rr,
						r,
					);
				} else if v.len() == 1 {
					let qq = u.clone().div_unit(ve as Single);
					assert_eq!(
						u128::try_from(qq.clone()).unwrap(),
						q,
						"[single] {:?} / {:?} ===> {:?} != {:?}",
						u,
						v,
						qq,
						q,
					);
				} else if v.msb() != 0 && u.msb() != 0 && u.len() > v.len() {
					panic!("div returned none for an unexpected reason");
				}
			}

			// Test against num_bigint

			// Equality

			assert_eq!(u.cmp(&v), num_u.cmp(&num_v));

			// Addition

			let w = u.clone().add(&v);
			let num_w = num_u.clone() + &num_v;

			assert_biguints_eq(&w, &num_w);

			// Subtraction

			if let Ok(w) = u.clone().sub(&v) {
				let num_w = num_u.clone() - &num_v;

				assert_biguints_eq(&w, &num_w);
			}

			// Multiplication

			let w = u.clone().mul(&v);
			let num_w = num_u.clone() * &num_v;

			assert_biguints_eq(&w, &num_w);

			// Division

			if v.len() == 1 && v.get(0) != 0 {
				let w = u.div_unit(v.get(0));
				let num_w = num_u / &num_v;
				assert_biguints_eq(&w, &num_w);
			} else if u.len() > v.len() && v.len() > 1 {
				let num_remainder = num_u.clone() % num_v.clone();

				let (w, remainder) = u.div(&v, return_remainder).unwrap();
				let num_w = num_u / &num_v;

				assert_biguints_eq(&w, &num_w);

				if return_remainder {
					assert_biguints_eq(&remainder, &num_remainder);
				}
			}
		});
	}
}

fn check_digit_lengths(u: &BigUint, v: &BigUint, max_limbs: usize) -> bool {
	1 <= u.len() && u.len() <= max_limbs && 1 <= v.len() && v.len() <= max_limbs
}

fn assert_biguints_eq(a: &BigUint, b: &num_bigint::BigUint) {
	let mut a = a.clone();
	a.lstrip();

	// `num_bigint::BigUint` doesn't expose it's internals, so we need to convert into that to
	// compare.
	let limbs = (0..a.len()).map(|i| a.get(i)).collect();
	let num_a = num_bigint::BigUint::new(limbs);

	assert!(&num_a == b, "\narithmetic: {:?}\nnum-bigint: {:?}", a, b);
}
