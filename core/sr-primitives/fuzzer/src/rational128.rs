use honggfuzz::fuzz;
use sr_primitives::{
	helpers_128bit::multiply_by_rational,
	traits::Zero
};

mod util;

use util::value_between;

fn main() {
	loop {
		fuzz!(|data: ([u8; 16], [u8; 16], [u8; 16])| {
			let data = Data {
				a: u128::from_be_bytes(data.0),
				b: u128::from_be_bytes(data.1),
				c: u128::from_be_bytes(data.2)
			};

			do_fuzz_multiply_by_rational(32, true, &data);
			do_fuzz_multiply_by_rational(32, false, &data);

			do_fuzz_multiply_by_rational(64, true, &data);
			do_fuzz_multiply_by_rational(64, false, &data);

			do_fuzz_multiply_by_rational(96, true, &data);
			do_fuzz_multiply_by_rational(96, false, &data);
			
			do_fuzz_multiply_by_rational(128, true, &data);
			do_fuzz_multiply_by_rational(128, false, &data);
		})
	}
}

struct Data {
	a: u128,
	b: u128,
	c: u128
}

fn do_fuzz_multiply_by_rational(
	bits: u32,
	bounded: bool,
	data: &Data,
) -> Option<()> {
	let upper_bound = 2u128.pow(bits);

	let a = value_between(data.a, 0u128, upper_bound)?;
	let c = value_between(data.c, 0u128, upper_bound)?;
	let b = value_between(
		data.b,
		0u128,
		if bounded { c } else { upper_bound }
	)?;

	let truth = mul_div(a, b, c);
	let result = mul_fn(a, b, c);

	if truth != result {
		println!("++ Computed with more loss than expected: {} * {} / {}", a, b, c);
		println!("++ Expected {}", truth);
		println!("+++++++ Got {}", result);
		panic!();
	}

	Some(())
}

fn mul_div(a: u128, b: u128, c: u128) -> u128 {
	use primitive_types::U256;
	if a.is_zero() { return Zero::zero(); }
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

// if Err just return the truth value. We don't care about such cases. The point of this
// fuzzing is to make sure: if `multiply_by_rational` returns `Ok`, it must be 100% accurate
// returning `Err` is fine.
fn mul_fn(a: u128, b: u128, c: u128) -> u128 {
	multiply_by_rational(a, b, c).unwrap_or(mul_div(a, b, c))
}