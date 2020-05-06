use std::convert::TryInto;

/// Return Per-million value.
pub fn log2(p: u32, q: u32) -> u32 {
	assert!(p >= q);
	assert!(p <= u32::max_value()/2);

	// This restriction should not be mandatory. But function is only tested and used for this.
	assert!(p <= 1_000_000);
	assert!(q <= 1_000_000);

	if p == q {
		return 0
	}

	let mut n = 0u32;
	while !(p >= (1u32 << n)*q) || !(p < (1u32 << (n+1))*q) {
		n += 1;
	}
	assert!(p < (1u32 << (n+1)) * q);

	let y_num: u32 = (p - (1u32 << n) * q).try_into().unwrap();
	let y_den: u32 = (p + (1u32 << n) * q).try_into().unwrap();

	let _2_div_ln_2 = 2_885_390u32;

	let taylor_term = |k: u32| -> u32 {
		if k == 0 {
			(_2_div_ln_2 as u128 * (y_num as u128).pow(1) / (y_den as u128).pow(1))
				.try_into().unwrap()
		} else {
			let mut res = _2_div_ln_2 as u128 * (y_num as u128).pow(3) / (y_den as u128).pow(3);
			for _ in 1..k {
				res = res * (y_num as u128).pow(2) / (y_den as u128).pow(2);
			}
			res /= 2 * k as u128 + 1;

			res.try_into().unwrap()
		}
	};

	let mut res = n * 1_000_000u32;
	let mut k = 0;
	loop {
		let term = taylor_term(k);
		if term == 0 {
			break
		}

		res += term;
		k += 1;
	}

	res
}

#[test]
fn test_log() {
	let div = 1_000;
	for p in 0..=div {
		for q in 1..=p {
			let p: u32 = (1_000_000 as u64 * p as u64 / div as u64).try_into().unwrap();
			let q: u32 = (1_000_000 as u64 * q as u64 / div as u64).try_into().unwrap();

			let res = - (log2(p, q) as i64);
			let expected = ((q as f64 / p as f64).log(2.0) * 1_000_000 as f64).round() as i64;
			assert!((res - expected).abs() <= 6);
		}
	}
}
