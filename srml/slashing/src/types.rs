use primitives::traits::{SimpleArithmetic, Zero, One};

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
// remove later or make generic
#[derive(Debug, Copy, Clone)]
pub struct Fraction<N> {
	denominator: N,
	numerator: N,
}


impl<N: SimpleArithmetic + Copy> Default for Fraction<N> {
	fn default() -> Self {
		Self { denominator: Zero::zero(), numerator: One::one() }
	}
}

impl<N: SimpleArithmetic + Copy> Fraction<N> {

	/// Create a new `Fraction` which uses `gcd` to create as small denominator and numerator as possible.
	pub fn new(denominator: N, numerator: N) -> Self {
		Self { denominator, numerator }
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

#[cfg(test)]
mod tests {
	use super::*;

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
