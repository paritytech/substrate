use crate::{Fraction, Misconduct, RollingMisconduct};

#[derive(Default)]
struct MisconductEntry<T: Default> {
	who: T,
	num_validators: T,
	session_index: T,
}

#[derive(Default)]
// inefficient, either sort it by session_index or use btreemap
struct Rolling(rstd::vec::Vec<MisconductEntry<u64>>);

impl Misconduct for Rolling {
	type Severity = u64;

	fn as_misconduct_level(&self, _severity: Fraction<Self::Severity>) -> u8 {
		unimplemented!()
	}
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

		let denominator = misbehaved.saturating_mul(misbehaved);
		let numerator = validators.saturating_mul(validators);

		// min(1, (k / n)^2)
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
