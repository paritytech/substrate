use crate::{Fraction, Misconduct, EraMisconduct};

/// An actor taking too long to respond
/// Slash after each era, 0.05 * min(3(k-1) / n, 1)
pub struct Unresponsive;

impl Misconduct for Unresponsive {
	type Severity = u64;

	fn as_misconduct_level(&self, severity: Fraction<Self::Severity>) -> u8 {
		if severity.denominator().saturating_mul(100_u32.into()) > severity.numerator() {
			3
		} else {
			1
		}
	}
}

impl EraMisconduct for Unresponsive {
	fn severity(&self, num_misbehaved: u64, num_validators: u64) -> Fraction<Self::Severity> {
		let numerator = num_validators;
		let denominator = 3 * num_misbehaved - 3;

		if denominator / numerator >= 1 {
			Fraction::new(1, 20)
		} else {
			Fraction::new(denominator, numerator) * Fraction::new(1, 20)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn unresponsiveness() {
		// 0.12 * 0.05 = 0.006
		let s = EraMisconduct::severity(&Unresponsive, 5, 100);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.006);

		// min(27, 1) * 0.05 = 0.05
		let s = EraMisconduct::severity(&Unresponsive, 10, 10);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.05);

		// 0.99 * 0.05 = 0.0495
		let s = EraMisconduct::severity(&Unresponsive, 34, 100);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.0495);
	}
}
