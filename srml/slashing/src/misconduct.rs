use crate::{Fraction, EraMisconduct, Misconduct, RollingMisconduct};

/// An actor taking too long to respond
/// Slash after each era, 0.05 * min(3(k-1) / n, 1)
pub struct Unresponsive;

impl Misconduct for Unresponsive {
	type Severity = u64;
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


#[derive(Default)]
struct MisconductEntry<T: Default> {
	who: T,
	num_validators: T,
	session_index: T,
}

#[derive(Default)]
// very inefficient
struct Rolling(rstd::vec::Vec<MisconductEntry<u64>>);

impl Misconduct for Rolling {
	type Severity = u64;
}

impl RollingMisconduct<u64> for Rolling {
	const WINDOW_LENGTH: u32 = 5;

	fn severity(&mut self, who: &u64, num_validators: u64, session_index: u64) -> Fraction<Self::Severity> {
		self.0.retain(|m| m.session_index > session_index);

		self.0.push(MisconductEntry {
			who: *who,
			num_validators,
			session_index: session_index + Self::WINDOW_LENGTH as u64
		});

		let misbehaved: u64 = self.0.iter().map(|m| m.who).fold(0_u64, |acc, i| acc.saturating_add(i));
		// calculate average number of validators because it may change between sessions
		let validators = {
			let sum: u64 = self.0
				.iter()
				.map(|m| m.num_validators)
				.fold(0_u64, |acc, i| acc.saturating_add(i));
			sum / self.0.len() as u64
		};

		// min(1, (k / n)^2)

		let denominator = misbehaved.saturating_mul(misbehaved);
		let numerator = validators.saturating_mul(validators);

		if denominator > numerator {
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

	#[test]
	fn rolling_it_works() {

		let mut rolling = Rolling::default();
		let validator_len = 50;

		for _ in 0..19 {
			RollingMisconduct::severity(&mut rolling, &1, validator_len, 0);
		}

		// (20^2 / 50^2) = 0.16
		let seve = RollingMisconduct::severity(&mut rolling, &1, validator_len, 0);

		assert_eq!(seve.denominator() as f64 / seve.numerator() as f64, 0.16);

		for _ in 0..9 {
			RollingMisconduct::severity(&mut rolling, &1, validator_len, 4);
		}


		// (10^2 / 50^2) = 0.04
		// misconducts in session 0 should be disregarded now
		// only the misconducts in session 4 should be taken into account
		let seve = RollingMisconduct::severity(&mut rolling, &1, validator_len, 5);
		assert_eq!(seve.denominator() as f64 / seve.numerator() as f64, 0.04);
	}
}
