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
		self.numerator == Zero::zero() && self.denominator == Zero::zero()
	}

	/// Get denominator
	pub fn denominator(&self) -> N {
		self.denominator
	}

	/// Get numerator
	pub fn numerator(&self) -> N {
		self.numerator
	}

	/// Convert fraction into severity level
	// TODO: extract into default trait impl
	pub fn as_misconduct_level(&self) -> u8 {
		if self.denominator.saturating_mul(10_u32.into()) > self.numerator {
			4
		} else if self.denominator.saturating_mul(100_u32.into()) > self.numerator {
			3
		} else if self.denominator.saturating_mul(1000_u32.into()) > self.numerator {
			2
		} else {
			1
		}
	}
}


/// Temp naive gcd algorithm
// TODO(niklasad1): move this or use `num-integer::Integer::gcd`
fn naive_gcd<N: SimpleArithmetic + Copy>(mut x: N, mut y: N) -> N {
    while y != Zero::zero() {
        let tmp = x;
        x = y;
        y = tmp % y;
    }
	x
}

/// lowest common multiple
fn lcm<N: SimpleArithmetic + Copy>(x: N, y: N) -> N {
	let gcd = naive_gcd(x, y);
    let product = x * y;

    product / gcd
}


#[cfg(test)]
mod tests {
	use super::*;

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

	#[test]
	fn misconduct_level() {
		assert_eq!(4, Fraction::new(10_u32, 10_u32).as_misconduct_level(), "100% should be severity level 4");
		assert_eq!(4, Fraction::new(2_u32, 10_u32).as_misconduct_level(), "20% should be severity level 4");
		assert_eq!(3, Fraction::new(5_u32, 100_u32).as_misconduct_level(), "5% should be severity level 3");
		assert_eq!(3, Fraction::new(2_u32, 100_u32).as_misconduct_level(), "2% should be severity level 3");
		assert_eq!(2, Fraction::new(1_u32, 100_u32).as_misconduct_level(), "1% should be severity level 2");
		assert_eq!(2, Fraction::new(2_u32, 1000_u32).as_misconduct_level(), "0.2% should be severity level 2");
		assert_eq!(1, Fraction::new(1_u32, 1000_u32).as_misconduct_level(), "0.1% should be severity level 1");
	}
}
