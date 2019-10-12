use honggfuzz::fuzz;
use sr_arithmetic::biguint::{BigUint, Single};
use std::convert::TryFrom;

mod util;

use util::value_between;

type S = u128;

fn main() {
	loop {
		fuzz!(|data: (usize, usize, Vec<Single>, Vec<Single>)| {
			let data = Data {
				random_limb_len_1: data.0,
				random_limb_len_2: data.1,
				digits_1: data.2,
				digits_2: data.3,
			};

			run_with_data_set(4, 4, false, &data, |u, v| {
				let ue = S::try_from(u.clone()).unwrap();
				let ve = S::try_from(v.clone()).unwrap();
				assert_eq!(u.cmp(&v), ue.cmp(&ve));
				assert_eq!(u.eq(&v), ue.eq(&ve));
			});

			run_with_data_set(3, 3, false, &data, |u, v| {
				let expected = S::try_from(u.clone()).unwrap() + S::try_from(v.clone()).unwrap();
				let t = u.clone().add(&v);
				assert_eq!(
					S::try_from(t.clone()).unwrap(), expected,
					"{:?} + {:?} ===> {:?} != {:?}", u, v, t, expected,
				);
			});

			run_with_data_set(4, 4, false, &data, |u, v| {
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

			run_with_data_set(2, 2, false, &data, |u, v| {
				let expected = S::try_from(u.clone()).unwrap() * S::try_from(v.clone()).unwrap();
				let t = u.clone().mul(&v);
				assert_eq!(
					S::try_from(t.clone()).unwrap(), expected,
					"{:?} * {:?} ===> {:?} != {:?}", u, v, t, expected,
				);
			});

			run_with_data_set(4, 4, false, &data, |u, v| {
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

struct Data {
	random_limb_len_1: usize,
	random_limb_len_2: usize,
	digits_1: Vec<Single>,
	digits_2: Vec<Single>,
}

fn run_with_data_set<F>(
	limbs_ub_1: usize,
	limbs_ub_2: usize,
	exact: bool,
	data: &Data,
	assertion: F,
) -> Option<()>
	where
		F: Fn(BigUint, BigUint) -> (),
{
	let digits_len_1 = if exact {
		limbs_ub_1
	} else {
		value_between(data.random_limb_len_1, 1, limbs_ub_1)?
	};

	let digits_len_2 = if exact {
		limbs_ub_2
	} else {
		value_between(data.random_limb_len_2, 1, limbs_ub_2)?
	};

	let u = big_uint_of_size(digits_len_1, &data.digits_1)?;
	let v = big_uint_of_size(digits_len_2, &data.digits_2)?;
	// this is easier than using lldb
	println!("u: {:?}, v: {:?}", u, v);
	assertion(u, v);
	Some(())
}

fn big_uint_of_size(size: usize, digits: &[Single]) -> Option<BigUint> {
	if digits.len() != size {
		None
	} else {
		Some(BigUint::from_limbs(digits))
	}
}
