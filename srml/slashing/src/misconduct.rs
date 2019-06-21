use crate::{CheckpointMisconduct, Misconduct, Fraction};

/// An actor taking too long to respond
/// Slash after each era, 0.05 * min(3(k-1) / n, 1)
pub struct Unresponsive;

impl Misconduct for Unresponsive {
	type Severity = u64;
}

impl CheckpointMisconduct for Unresponsive {
	fn severity(&self, k: u64, n: u64) -> Fraction<Self::Severity> {
		let numerator = 20 * n;
		let denominator = 3*k - 3;

		if denominator / n >= 1 {
			Fraction::new(1, 20)
		} else {
			Fraction::new(denominator, numerator)
		}
	}
}

/// Grandpa misconducts
pub mod grandpa {
	use crate::{CheckpointMisconduct, Misconduct, Fraction};

	/// Unjustified vote(s) from only one validator in the same era then slash 10%
	// assumption: this is called in the end of the era otherwise it would be impossible to know
	// that only one validator had performed a culprit in the era.
	pub struct UnjustifiedVote;

	impl Misconduct for UnjustifiedVote {
		type Severity = u64;
	}

	impl CheckpointMisconduct for UnjustifiedVote {
		fn severity(&self, _k: u64, _n: u64) -> Fraction<Self::Severity> {
			Fraction::new(1, 10)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn unresponsiveness() {
		// 0.12 * 0.05 = 0.006
		let s = CheckpointMisconduct::severity(&Unresponsive, 5, 100);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.006);

		// min(27, 1) * 0.05 = 0.05
		let s = CheckpointMisconduct::severity(&Unresponsive, 10, 10);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.05);

		// 0.99 * 0.05 = 0.0495
		let s = CheckpointMisconduct::severity(&Unresponsive, 34, 100);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.0495);
	}

	#[test]
	fn grandpa_unjustified_vote() {
		let s = CheckpointMisconduct::severity(&grandpa::UnjustifiedVote, 0, 0);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.10);
	}
}
