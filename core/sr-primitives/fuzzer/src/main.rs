use honggfuzz::fuzz;

use sr_primitives::sr_arithmetic::biguint::{Single, BigUint};
use std::convert::TryFrom;

fn main() {
    // Here you can parse `std::env::args and
    // setup / initialize your project

    // You have full control over the loop but
    // you're supposed to call `fuzz` ad vitam aeternam
    loop {
        // The fuzz macro gives an arbitrary object (see `arbitrary crate`)
        // to a closure-like block of code.
        // For performance reasons, it is recommended that you use the native type
        // `&[u8]` when possible.
        // Here, this slice will contain a "random" quantity of "random" data.
        fuzz!(|data: (usize, usize, Vec<Single>, Vec<Single>)| {
            let data = Data {
                random_limb_len_1: data.0,
                random_limb_len_2: data.1,
                digits_1: data.2,
                digits_2: data.3
            };

            type S = u128;
            run_with_data_set(4, 4, false, &data, |u, v| {
                let ue = S::try_from(u.clone()).unwrap();
                let ve = S::try_from(v.clone()).unwrap();
                assert_eq!(u.cmp(&v), ue.cmp(&ve));
                assert_eq!(u.eq(&v), ue.eq(&ve));
            });
        });
    }
}

struct Data {
    random_limb_len_1: usize,
    random_limb_len_2: usize,
    digits_1: Vec<Single>,
    digits_2: Vec<Single>
}

fn run_with_data_set<F>(
    limbs_ub_1: usize,
    limbs_ub_2: usize,
    exact: bool,
    data: &Data,
    assertion: F,
) -> Option<()>
    where
        F: Fn(BigUint, BigUint) -> ()
{
    let digits_len_1 = if exact {
        limbs_ub_1
    } else {
        check_between(data.random_limb_len_1, 1, limbs_ub_1)?
    };

    let digits_len_2 = if exact {
        limbs_ub_2
    } else {
        check_between(data.random_limb_len_2, 1, limbs_ub_2)?
    };

    let u = random_big_uint(digits_len_1, &data.digits_1)?;
    let v = random_big_uint(digits_len_2, &data.digits_2)?;
    assertion(u, v);
    Some(())
}

fn check_between(value: usize, min: usize, max: usize) -> Option<usize> {
    if value >= min && value < max {
        Some(value)
    } else {
        None
    }
}

pub fn random_big_uint(size: usize, digits: &[Single]) -> Option<BigUint> {
    if digits.len() != size {
        return None;
    } else {
        Some(BigUint::from_limbs(digits))
    }
}