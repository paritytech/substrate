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

			fuzz_multiply_by_rational_32(&data);
			fuzz_multiply_by_rational_64(&data);
			fuzz_multiply_by_rational_96(&data);
			fuzz_multiply_by_rational_128(&data);
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
	maximum_error: u128,
	do_print: bool,
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

	let a: u128 = a.into();
	let b: u128 = b.into();
	let c: u128 = c.into();

	let truth = mul_div(a, b, c);
	let result = mul_fn(a, b, c);
	let diff = truth.max(result) - truth.min(result);

	if do_print && diff > maximum_error {
		println!("++ Computed with more loss than expected: {} * {} / {}", a, b, c);
		println!("++ Expected {}", truth);
		println!("+++++++ Got {}", result);
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

fn fuzz_multiply_by_rational_32(data: &Data) {
	println!("\nInvariant: b < c");
	do_fuzz_multiply_by_rational(32, 0, false, true, data);
	println!("every possibility");
	do_fuzz_multiply_by_rational(32, 0, false, false, data);
}

fn fuzz_multiply_by_rational_64(data: &Data) {
	println!("\nInvariant: b < c");
	do_fuzz_multiply_by_rational( 64, 0, false, true, data);
	println!("every possibility");
	do_fuzz_multiply_by_rational( 64, 0, false, false, data);
}

fn fuzz_multiply_by_rational_96(data: &Data) {
	println!("\nInvariant: b < c");
	do_fuzz_multiply_by_rational( 96, 0, false, true, data);
	println!("every possibility");
	do_fuzz_multiply_by_rational( 96, 0, false, false, data);
}

fn fuzz_multiply_by_rational_128(data: &Data) {
	println!("\nInvariant: b < c");
	do_fuzz_multiply_by_rational( 127, 0, false, true, data);
	println!("every possibility");
	do_fuzz_multiply_by_rational( 127, 0, false, false, data);
}