use crate::*;
use crate::mock::*;

/// An actor taking too long to respond
/// Slash after each era, 0.05 * min(3(k-1) / n, 1)
pub struct Unresponsive<T: srml_staking::Trait> {
	_t: T,
	reports: Vec<(T::AccountId, Exposure)>,
}

impl<T: srml_staking::Trait> Unresponsive<T> {
	pub fn new(t: T) -> Self {
		Self {
			_t: t,
			reports: Vec::new(),
		}
	}
}

impl<T: srml_staking::Trait> MisconductReporter<T::AccountId, Exposure> for Unresponsive<T> {
	fn on_misconduct(&mut self, misbehaved: Vec<(T::AccountId, Exposure)>) {
		for (who, exposure) in misbehaved {

			// already have exposure just replace it
			if let Some(idx) = self.reports.iter().map(|(w, _,)| w).position(|w| w == &who) {
				self.reports[idx] = (who, exposure);
			} else {
				self.reports.push((who, exposure));
			}
		}
	}
}

impl<T: srml_staking::Trait> Misconduct<T::AccountId, Exposure> for Unresponsive<T> {
	type Severity = u64;

	fn severity(&self) -> Fraction<Self::Severity> {
		let k = self.reports.len() as u64;

		if k == 0 {
			Fraction::zero()
		} else {
			// validator set is supposed to be fixed under the era
			let n: u64 = Staking::validator_count().into();

			// min(1, 3(k - 1) / n) * 0.05

			let d = 3 * k - 3;

			let five_percent = Fraction::new(1_u64, 20_u64);

			if d >= n {
				five_percent
			} else {
				let f = Fraction::new(d, n);
				five_percent * f
			}
		}
	}

	fn as_misconduct_level(&self, severity: Fraction<Self::Severity>) -> u8 {
		if severity.denominator().saturating_mul(100_u32.into()) > severity.numerator() {
			3
		} else {
			1
		}
	}

	fn misbehaved(&self) -> Vec<(T::AccountId, Exposure)> {
		self.reports.clone()
	}

	fn end_of_era(&mut self) {
		self.reports.clear();
	}
}
