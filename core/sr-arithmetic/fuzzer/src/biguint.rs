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

			let num_u = num_bigint::BigUint::new(digits_u);
			let num_v = num_bigint::BigUint::new(digits_v);

			// Equality

			assert_biguints_eq(&u, &num_u);
			assert_biguints_eq(&v, &num_v);

			// Addition

			let mut w = u.clone().add(&v);
			let mut num_w = num_u.clone() + &num_v;

			assert_biguints_eq(&w, &num_w);

			// Subtraction

			if let Ok(w) = u.clone().sub(&v) {
				num_w = num_u.clone() - &num_v;

				assert_biguints_eq(&w, &num_w);
			}

			// Multiplication

			w = u.clone().mul(&v);
			num_w = num_u.clone() * &num_v;

			assert_biguints_eq(&w, &num_w);

			// Division

			if v.len() == 1 && v.get(0) != 0 {
				w = u.clone().div_unit(v.get(0));
				num_w = num_u.clone() / &num_v;
				assert_biguints_eq(&w, &num_w);
			} else {
				let w = u.clone().div(&v, rem).map(|(w, _)| w);
				let num_w = num_u.clone().checked_div(&num_v);

				// assert that the division was checked equally:
				// assert_eq!(w.is_some(), num_w.is_some());

				if let Some(w) = w {
					if let Some(num_w) = num_w {
						assert_biguints_eq(&w, &num_w);
					}
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
	println!("arithmetic: {:?}", a);
	println!("num-bigint: {:?}", b);

	let mut a = a.as_slice();

	while !a.is_empty() && a[0] == 0 {
		a = &a[1..];
	}

	let mut a = a.to_vec();

	a.reverse();

	assert_eq!(&(*a), b.as_slice());
}