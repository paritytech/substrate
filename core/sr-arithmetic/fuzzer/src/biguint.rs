use honggfuzz::fuzz;
use sr_arithmetic::biguint::{BigUint, Single};
use std::convert::TryFrom;

mod util;

use util::value_between;

type S = u128;

fn main() {
	loop {
		fuzz!(|data: (Vec<Single>, Vec<Single>)| {
			let (digits_u, digits_v) = data;

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
		});
	}
}

fn run_with_data_set<F>(
	max_limbs: usize,
	digits_u: &[Single], digits_v: &[Single],
	assertion: F,
) -> Option<()>
	where
		F: Fn(BigUint, BigUint) -> (),
{
	// Ensure that `1 <= num_digits < max_limbs`.
	value_between(digits_u.len(), 1, max_limbs)?;
	value_between(digits_v.len(), 1, max_limbs)?;

	let u = BigUint::from_limbs(digits_u);
	let v = BigUint::from_limbs(digits_v);
	// this is easier than using lldb
	println!("u: {:?}, v: {:?}", u, v);
	assertion(u, v);
	Some(())
}
