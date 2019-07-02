use crate::{Fraction, Misconduct, RollingMisconduct, EraMisconduct};


//TODO(niklasad1): Rejecting set of votes is needs to be implemented!!


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

/// An equivocation is defined as a validator signing two or more votes
/// in the same round, for the same vote type
///
/// Slash `min((3k/n)^2, 1)`
pub struct Equivocation;

impl Misconduct for Equivocation {
	type Severity = u64;

	fn as_misconduct_level(&self, severity: Fraction<Self::Severity>) -> u8 {
		if severity.denominator().saturating_mul(100) / severity.numerator() > 1 {
			3
		} else {
			2
		}
	}
}

impl EraMisconduct for Equivocation {
	fn severity(&self, num_misbehaved: u64, num_validators: u64) -> Fraction<Self::Severity> {
		let denominator = (3 * num_misbehaved) * (3 * num_misbehaved);
		let numerator = num_validators * num_validators;

		if denominator / numerator >= 1 {
			Fraction::new(1, 1)
		} else {
			Fraction::new(denominator, numerator)
		}
	}
}

/// An invalid vote for a chain that contains a non-validated block,
/// i.e. a block which contains a reference to a parachain blob that is not fully validated.
pub struct InvalidVote;

impl Misconduct for InvalidVote {
	type Severity = u64;

	fn as_misconduct_level(&self, _severity: Fraction<Self::Severity>) -> u8 {
		1
	}
}

impl RollingMisconduct<u64> for InvalidVote {
	const WINDOW_LENGTH: u32 = 0;

	fn severity(&mut self, _who: &u64, _num_validators: u64, _session_idx: u64) -> Fraction<Self::Severity> {
		Fraction::zero()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn unjustified_vote() {
		let seve = EraMisconduct::severity(&UnjustifiedVote, 0, 0);
		assert_eq!(seve.denominator() as f64 / seve.numerator() as f64, 0.1);
		assert_eq!(Misconduct::as_misconduct_level(&UnjustifiedVote, seve), 3);
	}

	#[test]
	fn equivocation() {
		let eq = Equivocation;

		// min(1, (3*2 / 80)^2)) = 0.0056
		let seve = EraMisconduct::severity(&eq, 2, 80);
		assert_eq!(seve.denominator() as f64 / seve.numerator() as f64, 0.005625);
		assert_eq!(Misconduct::as_misconduct_level(&eq, seve), 2);

		// min(1, (3*3 / 10)^2)) = 0.81
		let seve = EraMisconduct::severity(&eq, 3, 10);
		assert_eq!(seve.denominator() as f64 / seve.numerator() as f64, 0.81);
		assert_eq!(Misconduct::as_misconduct_level(&eq, seve), 3);

		// min(1, (4*3 / 10)^2)) = 1
		let seve = EraMisconduct::severity(&eq, 4, 10);
		assert_eq!(seve.denominator() as f64 / seve.numerator() as f64, 1.00);
		assert_eq!(Misconduct::as_misconduct_level(&eq, seve), 3);
	}


	#[test]
	fn invalid_vote_no_punishment() {
		let mut invalid_vote = InvalidVote;
		let who = 0;
		let num_validators = 100;
		let session = 0;
		let seve = RollingMisconduct::severity(&mut invalid_vote, &who, num_validators, session);
		assert!(seve.is_zero());
		assert_eq!(Misconduct::as_misconduct_level(&invalid_vote, seve), 1);
	}
}
