use crate::{CheckpointMisconduct, Misconduct, Fraction};

/// An actor taking too long to respond
/// Slash after each era, 0.05 * min(3(k-1) / n, 1)
#[derive(Copy, Clone)]
pub struct Unresponsive;

impl Misconduct for Unresponsive {
	type Severity = u64;
}

impl CheckpointMisconduct for Unresponsive {
	fn severity(&self, k: u64, n: u64) -> Fraction<Self::Severity> {
		let numerator = 20 * n;
		let denominator = 3*k - 3;

		if denominator / n > 1 {
			Fraction::new(1, 1)
		} else {
			Fraction::new(denominator, numerator)
		}
	}
}


#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn unresponsiveness() {
		let s = CheckpointMisconduct::severity(&Unresponsive, 5, 100);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.006);
	}
}
