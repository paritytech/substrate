use crate::Misconduct;

/// Unresposiveness misconduct which is slashed 0.00001% for isolated cases and grows exponentially on
/// concurrent culprits
//
// Assumption: `no floating point` available rely on that all arithmetics are constrained to integers
// then use `division` to calculate percentage instead
//
// Thus, 1 / 100_000 ~= 0.00001
pub struct Unresponsive {
	severity: u64,
}

impl Default for Unresponsive {
	fn default() -> Self {
		Self { severity: 100_000 }
	}
}

impl Misconduct for Unresponsive {
	type Severity = u64;

	fn on_misconduct(&mut self) {
		self.severity = std::cmp::max(1, self.severity / 2);
	}

	fn on_signal(&mut self) {
		self.severity = std::cmp::min(100_000, self.severity * 2);
	}

	fn severity(&self) -> Self::Severity {
		self.severity
	}
}
