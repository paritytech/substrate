use crate::{Fraction, Misconduct, EraMisconduct};

/// Unjustified vote from only one validator in the same era then slash 10%
// assumption: this is called in the end of the era otherwise it would be impossible to know
// that only one validator had performed a culprit in the era.
pub struct UnjustifiedVote;

impl Misconduct for UnjustifiedVote {
	type Severity = u32;

	fn as_misconduct_level(&self, _: Fraction<Self::Severity>) -> u8 {
		3
	}
}

impl EraMisconduct for UnjustifiedVote {
	fn severity(&self, _k: u64, _n: u64) -> Fraction<Self::Severity> {
		Fraction::new(1, 10)
	}
}

#[cfg(test)]
mod tests {
	#[test]
	fn unjustified_vote() {
		let s = EraMisconduct::severity(&grandpa::UnjustifiedVote, 0, 0);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.10);
	}
}
