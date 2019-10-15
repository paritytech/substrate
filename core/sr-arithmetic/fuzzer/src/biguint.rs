// Copyright 2019 Parity Technologies (UK) Ltd.
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
//! Running this fuzzer can be done with `cargo hfuzz run biguint`. `honggfuzz` CLI options can
//! be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug biguint hfuzz_workspace/biguint/*.fuzz`.
//!
//! # More infomation
//! More information about `honggfuzz` can be found
//! [here](https://docs.rs/honggfuzz/0.5.45/honggfuzz/).

use honggfuzz::fuzz;
use sr_arithmetic::biguint::{BigUint, Single};
use std::convert::TryFrom;
use num_traits::ops::checked::CheckedDiv;

type S = u128;

fn main() {
	loop {
		fuzz!(|data: (Vec<Single>, Vec<Single>, bool)| {
			let (mut digits_u, mut digits_v, rem) = data;

			run_with_data_set(4, &digits_u, &digits_v, |u, v| {
				let ue = S::try_from(u.clone()).unwrap();
				let ve = S::try_from(v.clone()).unwrap();
				assert_eq!(u.cmp(&v), ue.cmp(&ve));
				assert_eq!(u.eq(&v), ue.eq(&ve));
			});

			run_with_data_set(3, &digits_u, &digits_v, |u, v| {
				let expected = S::try_from(u.clone()).unwrap() + S::try_from(v.clone()).unwrap();
				let t = u.clone().add(&v);
				assert_eq!(
					S::try_from(t.clone()).unwrap(), expected,
					"{:?} + {:?} ===> {:?} != {:?}", u, v, t, expected,
				);
			});

			run_with_data_set(4, &digits_u, &digits_v, |u, v| {
				let expected = S::try_from(u.clone())
					.unwrap()
					.checked_sub(S::try_from(v.clone()).unwrap());
				let t = u.clone().sub(&v);
				if expected.is_none() {
					assert!(t.is_err())
				} else {
					let t = t.unwrap();
					let expected = expected.unwrap();
					assert_eq!(
						S::try_from(t.clone()).unwrap(), expected,
						"{:?} - {:?} ===> {:?} != {:?}", u, v, t, expected,
					);
				}
			});

			run_with_data_set(2, &digits_u, &digits_v, |u, v| {
				let expected = S::try_from(u.clone()).unwrap() * S::try_from(v.clone()).unwrap();
				let t = u.clone().mul(&v);
				assert_eq!(
					S::try_from(t.clone()).unwrap(), expected,
					"{:?} * {:?} ===> {:?} != {:?}", u, v, t, expected,
				);
			});

			run_with_data_set(4, &digits_u, &digits_v, |u, v| {
				let ue = S::try_from(u.clone()).unwrap();
				let ve = S::try_from(v.clone()).unwrap();
				if ve == 0 {
					return;
				}
				let (q, r) = (ue / ve, ue % ve);
				if let Some((qq, rr)) = u.clone().div(&v, true) {
					assert_eq!(
						S::try_from(qq.clone()).unwrap(), q,
						"{:?} / {:?} ===> {:?} != {:?}", u, v, qq, q,
					);
					assert_eq!(
						S::try_from(rr.clone()).unwrap(), r,
						"{:?} % {:?} ===> {:?} != {:?}", u, v, rr, r,
					);
				} else if v.len() == 1 {
					let qq = u.clone().div_unit(ve as Single);
					assert_eq!(
						S::try_from(qq.clone()).unwrap(), q,
						"[single] {:?} / {:?} ===> {:?} != {:?}", u, v, qq, q,
					);
				} else if v.msb() != 0 && u.msb() != 0 && u.len() > v.len() {
					panic!("div returned none for an unexpected reason");
				}
			});

			// Test against num_bigint

			let u = BigUint::from_limbs(&digits_u);
			let v = BigUint::from_limbs(&digits_v);

			digits_u.reverse();
			digits_v.reverse();

			let num_u = num_bigint::BigUint::new(digits_u.clone());
			let num_v = num_bigint::BigUint::new(digits_v.clone());

			// Equality

			assert_biguints_eq(&u, &num_u);
			assert_biguints_eq(&v, &num_v);

			if digits_u == digits_v {
				assert_eq!(u, v);
				assert_eq!(num_u, num_v);
			}

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
				let w = u.clone().div_unit(v.get(0));
				let num_w = num_u.clone() / &num_v;
				assert_biguints_eq(&w, &num_w);
			} else if u.len() > v.len() {
				let w = u.clone().div(&v, rem).map(|(w, _)| w);
				let num_w = num_u.clone().checked_div(&num_v);

				// assert that the division was checked equally:
				// assert_eq!(w.is_some(), num_w.is_some());

				if let Some(w) = w {
					assert_biguints_eq(&w, &num_w.unwrap());
				}
			}
		});
	}
}

fn run_with_data_set<F>(
	max_limbs: usize,
	digits_u: &[Single], digits_v: &[Single],
	assertion: F,
)
	where
		F: Fn(BigUint, BigUint) -> (),
{
	// Ensure that `1 <= num_digits < max_limbs`.
	let valid = value_between(digits_u.len(), 1, max_limbs) &&
		value_between(digits_v.len(), 1, max_limbs);
	if !valid {
		return;
	}

	let u = BigUint::from_limbs(digits_u);
	let v = BigUint::from_limbs(digits_v);
	// this is easier than using lldb
	// println!("u: {:?}, v: {:?}", u, v);

	assertion(u, v)
}

fn value_between(value: usize, min: usize, max: usize) -> bool {
	min <= value && value <= max
}

fn assert_biguints_eq(a: &BigUint, b: &num_bigint::BigUint) {
	// `BigUint` doesn't check the input in `from_limbs` so we skip any leading 0s.
	let a_iter = a.as_slice().iter().skip_while(|&&i| i == 0);
	// the `num-bigint` `BigUint` is little endian whereas our `BigUint` is big endian.
	let b_iter = b.as_slice().iter().rev();

	assert!(a_iter.eq(b_iter), "arithmetic: {:?}\nnum-bigint: {:?}", a, b);
}
