use crate::Misconduct;
use rstd::cmp;

const ONE_PERCENT: u64 = 100;
const FOUR_PERCENT: u64 = 25;
const TEN_PERCENT: u64 = 10;
const HUNDRED_PERCENT: u64 = 1;
const TEN_PPM: u64 = 100_000;

/// An actor taking too long to respond
/// Isolated case: 0.00001% slashing, growing exponentially for concurrent cases
#[derive(Copy, Clone)]
pub struct Unresponsive {
	severity: u64,
}

impl Default for Unresponsive {
	fn default() -> Self {
		Self { severity: TEN_PPM }
	}
}

impl Misconduct for Unresponsive {
	type Severity = u64;

	fn on_misconduct(&mut self) {
		self.severity = cmp::max(HUNDRED_PERCENT, self.severity / 2);
	}

	fn on_signal(&mut self) {
		self.severity = cmp::min(TEN_PPM, self.severity * 2);
	}

	fn severity(&self) -> Self::Severity {
		self.severity
	}
}

/// A block producer produces more than one block in same timeslot or an invalid block
/// Slash 1%
#[derive(Copy, Clone, Default)]
pub struct BlockProduction;

impl Misconduct for BlockProduction {
	type Severity = u64;

	fn on_misconduct(&mut self) {}

	fn on_signal(&mut self) {}

	fn severity(&self) -> Self::Severity {
		ONE_PERCENT
	}
}

/// A `Grandpa` validator signed more than one vote in the same timeslot
/// Isolated case, slash 4% of stake.
/// If there are k concurrent cases, slash 4k% from each culprit.
#[derive(Copy, Clone)]
pub struct GrandpaEquivocation {
	severity: u64
}

impl Default for GrandpaEquivocation {
	fn default() -> Self {
		Self { severity: FOUR_PERCENT }
	}
}

impl Misconduct for GrandpaEquivocation {
	type Severity = u64;

	fn on_misconduct(&mut self) {
		self.severity = cmp::max(HUNDRED_PERCENT, self.severity / 2);
	}

	fn on_signal(&mut self) {
		self.severity = cmp::min(FOUR_PERCENT, self.severity * 2);
	}

	fn severity(&self) -> Self::Severity {
		self.severity
	}
}

/// Vote for a chain that doesn't contain a block that could have been finalized
/// Slash between 10% and 100%, depending on the number of culprits.
// TODO(niklasad1): not specified how growth shall be estimated just between 10% - 100%
#[derive(Copy, Clone)]
pub struct GrandpaUnjustifiedVote {
	severity: u64
}

impl Default for GrandpaUnjustifiedVote {
	fn default() -> Self {
		Self { severity: TEN_PERCENT }
	}
}

impl Misconduct for GrandpaUnjustifiedVote {
	type Severity = u64;

	fn on_misconduct(&mut self) {
		self.severity = cmp::min(HUNDRED_PERCENT, self.severity / 2);
	}

	fn on_signal(&mut self) {
		self.severity = cmp::max(TEN_PERCENT, self.severity * 2);
	}

	fn severity(&self) -> Self::Severity {
		self.severity
	}
}

/// Finalization of 2 competing forks.
/// Slash between 10% and 100%, depending on the number of culprits.
// TODO(niklasad1): not specified how growth shall be estimated just between 10% - 100%
#[derive(Copy, Clone)]
pub struct GrandpaSafetyFault {
	severity: u64
}

impl Default for GrandpaSafetyFault {
	fn default() -> Self {
		Self { severity: TEN_PERCENT }
	}
}

impl Misconduct for GrandpaSafetyFault {
	type Severity = u64;

	fn on_misconduct(&mut self) {
		self.severity = cmp::min(HUNDRED_PERCENT, self.severity / 2);
	}

	fn on_signal(&mut self) {
		self.severity = cmp::max(TEN_PERCENT, self.severity * 2);
	}

	fn severity(&self) -> Self::Severity {
		self.severity
	}
}
