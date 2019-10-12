use honggfuzz::fuzz;
use sr_arithmetic::{helpers_128bit::multiply_by_rational, traits::Zero};

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

			let truth = mul_div(a, b, c);
			// if Err just use the truth value. We don't care about such cases. The point of this
			// fuzzing is to make sure: if `multiply_by_rational` returns `Ok`, it must be 100% accurate
			// returning `Err` is fine.
			let result = multiply_by_rational(a, b, c).unwrap_or(truth);

			if truth != result {
				println!("++ Expected {}", truth);
				println!("+++++++ Got {}", result);
				panic!();
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
