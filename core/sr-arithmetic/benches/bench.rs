use criterion::{Criterion, criterion_group, criterion_main};
use sr_arithmetic::biguint::{BigUint, Single};

fn random_big_uint(size: usize) -> BigUint {
	use rand::Rng;
	let mut rng = rand::thread_rng();
	let digits: Vec<_> = (0..size).map(|_| rng.gen_range(0, Single::max_value())).collect();
	BigUint::from_limbs(&digits)
}

fn bench_addition_2_digit(c: &mut Criterion) {
	let a = random_big_uint(2);
	let b = random_big_uint(2);
	c.bench_function("addition 2 digit", |bencher| bencher.iter(|| {
		let _ = a.clone().add(&b);
	}));
}

fn bench_addition_4_digit(c: &mut Criterion) {
	let a = random_big_uint(4);
	let b = random_big_uint(4);
	c.bench_function("addition 4 digit", |bencher| bencher.iter(|| {
		let _ = a.clone().add(&b);
	}));
}

fn bench_subtraction_2_digit(c: &mut Criterion) {
	let a = random_big_uint(2);
	let b = random_big_uint(2);
	c.bench_function("subtraction 2 digit", |bencher| bencher.iter(|| {
		let _ = a.clone().sub(&b);
	}));
}

fn bench_subtraction_4_digit(c: &mut Criterion) {
	let a = random_big_uint(4);
	let b = random_big_uint(4);
	c.bench_function("subtraction 4 digit", |bencher| bencher.iter(|| {
		let _ = a.clone().sub(&b);
	}));
}

fn bench_multiplication_2_digit(c: &mut Criterion) {
	let a = random_big_uint(2);
	let b = random_big_uint(2);
	c.bench_function("multiplication 2 digit", |bencher| bencher.iter(|| {
		let _ = a.clone().mul(&b);
	}));
}

fn bench_multiplication_4_digit(c: &mut Criterion) {
	let a = random_big_uint(4);
	let b = random_big_uint(4);
	c.bench_function("multiplication 4 digit", |bencher| bencher.iter(|| {
		let _ = a.clone().mul(&b);
	}));
}

fn bench_division_4_digit(c: &mut Criterion) {
	let a = random_big_uint(4);
	let b = random_big_uint(2);
	c.bench_function("division 4 digit", |bencher| bencher.iter(|| {
		let _ = a.clone().div(&b, true);
	}));
}

criterion_group!{
    name = benches;
    config = Criterion::default();
    targets =
        bench_addition_2_digit, bench_addition_4_digit,
        bench_subtraction_2_digit, bench_subtraction_4_digit,
        bench_multiplication_2_digit, bench_multiplication_4_digit,
        bench_division_4_digit
}
criterion_main!(benches);