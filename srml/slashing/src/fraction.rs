use rstd::ops::{Add, Mul};
use primitives::traits::{SimpleArithmetic, Zero};

/// Type to keep a fraction represented as integers `until the result is computed`
/// The use case might be to calculate `0.05 * min(3(k-1) / n, 1)`
///
/// Because `3 / 10 = 0` then keep it as a fraction instead
///
/// 1 / 25 * 3(k-1) / n
///
/// -> denominator = 1 * 3(k-1)
/// -> numerator = 25 * n
///
/// then in the end: (balance / numerator) * denominator
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Fraction<N> {
	denominator: N,
	numerator: N,
}

impl<N: SimpleArithmetic + Copy> Mul for Fraction<N> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let numerator = self.numerator * rhs.numerator;
        let denominator = self.denominator * rhs.denominator;
        Self::new(denominator, numerator)
    }
}

impl<N: SimpleArithmetic + Copy> Add for Fraction<N> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
		match (self.is_zero(), rhs.is_zero()) {
			(true, true) => self,
			(false, true) => self,
			(true, false) => rhs,
			(false, false) => {
				let lcm = lcm(self.numerator, rhs.numerator);

				let factor1 = lcm / self.numerator;
				let factor2 = lcm / rhs.numerator;

				let common_numerator = self.numerator * factor1;
				let denominator = (self.denominator * factor1) + (rhs.denominator * factor2);

				Self::new(denominator, common_numerator)
			}
		}
    }
}

impl<N: SimpleArithmetic + Copy> Fraction<N> {

	/// Create a new `Fraction` which uses `gcd` to create as small denominator and numerator as possible.
	pub fn new(denominator: N, numerator: N) -> Self {
		if denominator.is_zero() || numerator.is_zero() {
			Self { denominator, numerator }
		} else {
			let gcd = naive_gcd(denominator, numerator);
			Self { denominator: denominator / gcd, numerator: numerator / gcd }
		}
	}

	/// Create a `Zero` fraction
	pub fn zero() -> Self {
		Self::new(Zero::zero(), Zero::zero())
	}

	/// Check if the `Fraction` is zero
	pub fn is_zero(&self) -> bool {
		self.denominator.is_zero()
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

// Computes the greatest common divisor of `x` and `y`
// Panics if x or y is zero
// TODO(niklasad1): remove or optimize
fn naive_gcd<N: SimpleArithmetic + Copy>(mut x: N, mut y: N) -> N {
	assert!(!x.is_zero() && !y.is_zero());
	while y != Zero::zero() {
		let tmp = x;
		x = y;
		y = tmp % y;
	}
	x
}

// Computes the lowest common multiple of `x` and `y`
// Panics if x or y is zero
// TODO(niklasad1): remove or optimize
fn lcm<N: SimpleArithmetic + Copy>(x: N, y: N) -> N {
	assert!(!x.is_zero() && !y.is_zero());
	let gcd = naive_gcd(x, y);
	let product = x * y;

	product / gcd
}


#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn zero() {
		assert_eq!(Fraction::new(0_u64, 0_u64).is_zero(), true);
		assert_eq!(Fraction::new(0_u64, 1200120).is_zero(), true);
		assert_eq!(Fraction::new(129291_u64, 0).is_zero(), false);
	}

	#[test]
	fn add() {
		// 0,428571429
		let f1 = Fraction::new(3_u64, 7_u64);
		// 0.25
		let f2 = Fraction::new(1_u64, 4_u64);
		assert_eq!(f1 + f2, Fraction::new(19_u64, 28_u64));

		// 0.0
		let f1 = Fraction::zero();
		// 0.25
		let f2 = Fraction::new(1_u32, 4_u32);
		assert_eq!(f1 + f2, Fraction::new(1_u32, 4_u32));

		// 0.75
		let f1 = Fraction::new(3_u32, 4_u32);
		// 0.25
		let f2 = Fraction::new(1_u32, 4_u32);
		assert_eq!(f1 + f2, Fraction::new(1_u32, 1_u32));
	}


	#[test]
	fn mul() {
		let f1 = Fraction::new(2_u64, 3_u64);
		let f2 = Fraction::new(1_u64, 2_u64);
		assert_eq!(f1 * f2, Fraction::new(2_u64, 6_u64));

		let f1 = Fraction::zero();
		let f2 = Fraction::new(1_u32, 4_u32);
		assert_eq!(f1 * f2, Fraction::zero());
	}
}
