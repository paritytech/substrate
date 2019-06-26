use crate::{Fraction, Misconduct};

/// An actor taking too long to respond
/// Slash after each era, 0.05 * min(3(k-1) / n, 1)
pub struct Unresponsive;

impl Misconduct for Unresponsive {
	type Severity = u64;

	fn severity(&self, num_misbehaved: u64, num_validators: u64, _era_len: u64) -> Fraction<Self::Severity> {
		let numerator = 20 * num_validators;
		let denominator = 3*num_misbehaved - 3;

		if denominator / num_validators >= 1 {
			Fraction::new(1, 20)
		} else {
			Fraction::new(denominator, numerator)
		}
	}

	fn on_misconduct(&mut self) {}

	fn on_signal(&mut self) {}
}

/// Grandpa misconducts
// TODO(niklasad1): move these to the grandpa module or remove?!
pub mod grandpa {
	use crate::{Misconduct, Fraction, impl_misconduct_static_severity};

	/// Unjustified vote from only one validator in the same era then slash 10%
	// assumption: this is called in the end of the era otherwise it would be impossible to know
	// that only one validator had performed a culprit in the era.
	pub struct UnjustifiedVote;
	impl_misconduct_static_severity!(UnjustifiedVote, u64 => Fraction::new(1, 10));

	/// An equivocation is defined as a validator signing two or more votes
	/// in the same round, for the same vote type
	pub struct Equivocation;

	impl Misconduct for Equivocation {
		type Severity = u64;

		fn severity(&self, num_misbehaved: u64, num_validators: u64, _era_len: u64) -> Fraction<Self::Severity> {
			let denominator = (3*num_misbehaved) * (3*num_misbehaved);
			let numerator = num_validators * num_validators;

			if denominator / numerator >= 1 {
				Fraction::new(1, 1)
			} else {
				Fraction::new(denominator, numerator)
			}
		}

		fn on_misconduct(&mut self) {}

		fn on_signal(&mut self) {}
	}

	/// Collusion of > 1/3 of validators which may lead to finalizing blocks in different chains
	/// Slash 100%
	pub struct CollusionSetVotes;
	impl_misconduct_static_severity!(CollusionSetVotes, u64 => Fraction::new(1, 1));

	/// Invalid vote, no slashing
	/// Voter A ignores any votes from its own point-of-view which contains `non-validated` blocks
	// TODO(niklasad1): this could be removed and replaced with the `unit type impl`
	pub struct InvalidVote;
	impl_misconduct_static_severity!(InvalidVote, u64 => Fraction::default());

}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn unresponsiveness() {
		// 0.12 * 0.05 = 0.006
		let s = Misconduct::severity(&Unresponsive, 5, 100, 0);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.006);

		// min(27, 1) * 0.05 = 0.05
		let s = Misconduct::severity(&Unresponsive, 10, 10, 0);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.05);

		// 0.99 * 0.05 = 0.0495
		let s = Misconduct::severity(&Unresponsive, 34, 100, 0);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.0495);
	}

	#[test]
	fn grandpa_unjustified_vote() {
		let s = Misconduct::severity(&grandpa::UnjustifiedVote, 0, 0, 0);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.10);
	}

	#[test]
	fn grandpa_equivocation() {
		// min(1, (3*1 / 10)^2)) = 0.09
		let s = Misconduct::severity(&grandpa::Equivocation, 1, 10, 0);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.09);

		// min(1, (3*3 / 10)^2)) = 0.81
		let s = Misconduct::severity(&grandpa::Equivocation, 3, 10, 0);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.81);

		// min(1, (4*3 / 10)^2)) = 1
		let s = Misconduct::severity(&grandpa::Equivocation, 4, 10, 0);
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 1.00);
	}

	#[test]
	fn reject_set_votes_colluding_to_circumvent_super_majority() {
		let s = Misconduct::severity(&grandpa::CollusionSetVotes, 1, 1000, 0);
		assert_eq!(1, s.denominator());
		assert_eq!(1, s.numerator());

		let s = Misconduct::severity(&grandpa::CollusionSetVotes, 0, 0, 0);
		assert_eq!(1, s.denominator());
		assert_eq!(1, s.numerator());
	}

	#[test]
	fn grandpa_invalid_vote_no_slash() {
		let s = Misconduct::severity(&grandpa::InvalidVote, 0, 0, 0);
		assert_eq!(0, s.denominator() / s.numerator());
	}
}
