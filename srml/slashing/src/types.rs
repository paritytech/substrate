use primitives::traits::{SimpleArithmetic, Zero};

/// Type to keep a fraction represented as integers `until the result is computed`
/// The use case might be to calculate `0.05 * min( 3(k-1) / n, 1)`
///
/// Because `3 / 10 = 0` then keep it as a fraction instead
///
/// 1 / 25 * 3(k-1) / n
///
/// -> denominator = 1 * 3(k-1)
/// -> numerator = 25 * n
///
/// then in the end: (balance / numerator) * denominator
// remove later or make generic
#[derive(Debug, Copy, Clone)]
pub struct Fraction<N> {
	/// remove later or make generic
	denominator: N,
	/// remove later or make generic
	numerator: N,
}


impl<N: SimpleArithmetic + Copy> Fraction<N> {

	/// Create a new `Fraction` which uses `gcd` to create as numerator as possible
	/// Because of `integer semantics` i.e, a large denominator will likely be zero
	pub fn new(denominator: N, numerator: N) -> Self {
		let gcd = gcd(denominator, numerator);

		Self { denominator: denominator / gcd, numerator: numerator / gcd }
	}

	/// Get denominator
	pub fn denominator(&self) -> N {
		self.denominator
	}

	/// Get numerator
	pub fn numerator(&self) -> N {
		self.numerator
	}
}

/// temp naive gcd algorithm
fn gcd<N: SimpleArithmetic + Copy>(mut x: N, mut y: N) -> N {
    while y != Zero::zero() {
        let tmp = x;
        x = y;
        y = tmp % y;
    }

    x
}
