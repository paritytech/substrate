use crate::{Fraction, Misconduct};

/// An actor taking too long to respond
/// Slash after each era, 0.05 * min(3(k-1) / n, 1)
#[derive(Default)]
pub struct Unresponsive(rstd::vec::Vec<(u64, Fraction<u64>)>);

impl Misconduct for Unresponsive {
	type Severity = u64;
	const WINDOW_SIZE: u32 = 6;

	fn on_misconduct(&mut self, num_misbehaved: u64, num_validators: u64, session_index: u64) {
		self.0.retain(|&(s, _)| s > session_index);

		let numerator = 20 * num_validators;
		let denominator = 3 * num_misbehaved - 3;

		let severity = if denominator / num_validators >= 1 {
			Fraction::new(1, 20)
		} else {
			Fraction::new(denominator, numerator)
		};

		self.0.push((session_index + Self::WINDOW_SIZE as u64, severity));
	}

	fn severity(&self) -> Fraction<Self::Severity> {
		let mut sum = Fraction::zero();
		for &(_, seve) in &self.0 {
			sum = sum + seve;
		}
		sum * Fraction::new(1_u64, self.0.len() as u64)
	}
}

/// Grandpa misconducts
// TODO(niklasad1): move these to the grandpa module or remove?!
pub mod grandpa {
	use crate::{Misconduct, Fraction, impl_static_misconduct};

	/// Unjustified vote from only one validator in the same era then slash 10%
	// assumption: this is called in the end of the era otherwise it would be impossible to know
	// that only one validator had performed a culprit in the era.
	#[derive(Default)]
	pub struct UnjustifiedVote;
	impl_static_misconduct!(UnjustifiedVote, u64 => Fraction::new(1, 10));

	/// An equivocation is defined as a validator signing two or more votes
	/// in the same round, for the same vote type
	#[derive(Default)]
	pub struct Equivocation(rstd::vec::Vec<(u64, Fraction<u64>)>);

	impl Misconduct for Equivocation {
		type Severity = u64;
		// just for fun remove this
		const WINDOW_SIZE: u32 = 99;

		fn on_misconduct(&mut self, num_misbehaved: u64, num_validators: u64, session_index: u64) {
			self.0.retain(|&(s, _)| s > session_index);

			let denominator = (3*num_misbehaved) * (3*num_misbehaved);
			let numerator = num_validators * num_validators;

			let severity = if denominator / numerator >= 1 {
				Fraction::new(1, 1)
			} else {
				Fraction::new(denominator, numerator)
			};

			self.0.push((session_index + Self::WINDOW_SIZE as u64, severity));
		}

		fn severity(&self) -> Fraction<Self::Severity> {
			let mut sum = Fraction::zero();
			for &(_, seve) in &self.0 {
				sum = sum + seve;
			}
			sum * Fraction::new(1_u64, 2_u64)
		}
	}

	/// Collusion of > 1/3 of validators which may lead to finalizing blocks in different chains
	/// Slash 100%
	#[derive(Default)]
	pub struct CollusionSetVotes;
	impl_static_misconduct!(CollusionSetVotes, u64 => Fraction::new(1, 1));

	/// Invalid vote, no slashing
	/// Voter A ignores any votes from its own point-of-view which contains `non-validated` blocks
	// TODO(niklasad1): this could be removed and replaced with the `unit type impl`
	#[derive(Default)]
	pub struct InvalidVote;
	impl_static_misconduct!(InvalidVote, u64 => Fraction::zero());

}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	#[ignore]
	fn unresponsiveness() {
		let mut ur = Unresponsive::default();
		// 0.12 * 0.05 = 0.006
		ur.on_misconduct(5, 100, 0);
		let s = ur.severity();
		let rate = s.denominator() as f64 / s.numerator() as f64;
		assert_eq!(rate, 0.006);

		// // min(27, 1) * 0.05 = 0.05
		// let s = Misconduct::severity(&Unresponsive, 10, 10, 0);
		// let rate = s.denominator() as f64 / s.numerator() as f64;
		// assert_eq!(rate, 0.05);
        //
		// // 0.99 * 0.05 = 0.0495
		// let s = Misconduct::severity(&Unresponsive, 34, 100, 0);
		// let rate = s.denominator() as f64 / s.numerator() as f64;
		// assert_eq!(rate, 0.0495);
	}

	// #[test]
	// #[ignore]
	// fn grandpa_unjustified_vote() {
	//     let s = Misconduct::severity(&grandpa::UnjustifiedVote, 0, 0, 0);
	//     let rate = s.denominator() as f64 / s.numerator() as f64;
	//     assert_eq!(rate, 0.10);
	// }
    //
	// #[test]
	// #[ignore]
	// fn grandpa_equivocation() {
	//     // min(1, (3*1 / 10)^2)) = 0.09
	//     let s = Misconduct::severity(&grandpa::Equivocation, 1, 10, 0);
	//     let rate = s.denominator() as f64 / s.numerator() as f64;
	//     assert_eq!(rate, 0.09);
    //
	//     // min(1, (3*3 / 10)^2)) = 0.81
	//     let s = Misconduct::severity(&grandpa::Equivocation, 3, 10, 0);
	//     let rate = s.denominator() as f64 / s.numerator() as f64;
	//     assert_eq!(rate, 0.81);
    //
	//     // min(1, (4*3 / 10)^2)) = 1
	//     let s = Misconduct::severity(&grandpa::Equivocation, 4, 10, 0);
	//     let rate = s.denominator() as f64 / s.numerator() as f64;
	//     assert_eq!(rate, 1.00);
	// }
    //
	// #[test]
	// #[ignore]
	// fn reject_set_votes_colluding_to_circumvent_super_majority() {
	//     let s = Misconduct::severity(&grandpa::CollusionSetVotes, 1, 1000, 0);
	//     assert_eq!(1, s.denominator());
	//     assert_eq!(1, s.numerator());
    //
	//     let s = Misconduct::severity(&grandpa::CollusionSetVotes, 0, 0, 0);
	//     assert_eq!(1, s.denominator());
	//     assert_eq!(1, s.numerator());
	// }

	#[test]
	#[ignore]
	fn grandpa_invalid_vote_no_slash() {
		let mut invalid_vote = grandpa::InvalidVote::default();
		invalid_vote.on_misconduct(0, 0, 0);
		let s = invalid_vote.severity();
		assert_eq!(0, s.denominator() / s.numerator());
	}
}
