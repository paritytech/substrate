/// Return Per-million value.
pub fn log2(p: u32, q: u32) -> u32 {
	assert!(p >= q);
	assert!(p <= u32::max_value()/2);
	let mut n = 0;
	while !(p >= 2u32.pow(n)*q) || !(p < 2u32.pow(n+1)*q) {
		n += 1;
	}
	assert!(p < 2u32.pow(n+1) * q);

	let y_num = (p - 2u32.pow(n) * q) as u32;
	let y_den = (p + 2u32.pow(n) * q) as u32;

	let _2_div_ln_2 = 2_885_390u32;

	let taylor_term = |k: u32| {
		if k == 0 {
			(_2_div_ln_2 as u128 * (y_num as u128).pow(1) / (y_den as u128).pow(1)) as u32
	 	} else {
			let mut res = _2_div_ln_2 as u128 * (y_num as u128).pow(3) / (y_den as u128).pow(3);
			for _ in 1..k {
				res = res * (y_num as u128).pow(2) / (y_den as u128).pow(2);
			}
			res /= 2 * k as u128 + 1;

			res as u32
		}
	};

	let mut res = n as u32 * 1_000_000u32;
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
	let mil = 1_000_000;
	let test = |a: u32| {
		let i = log2(mil, a);
		let f = (mil as f64 / a as f64).log(2.0) * mil as f64;
		assert!((i as i64 - f.floor() as i64).abs() < 6);
	};

	for i in 1..1_000_000 {
		test(i as u32)
	}
}

// TODO TODO: test a bit more
