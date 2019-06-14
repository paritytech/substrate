// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

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



/// ...
pub struct GrandpaEquivocation {
	severity: u64,
}

impl Default for GrandpaEquivocation {
	fn default() -> Self {
		Self { severity: 25 }
	}
}

impl Misconduct for GrandpaEquivocation {
	type Severity = u64;

	fn on_misconduct(&mut self) {
		self.severity = std::cmp::max(1, self.severity / 2);
	}

	fn on_signal(&mut self) {
		self.severity = std::cmp::min(25, self.severity * 2);
	}

	fn severity(&self) -> Self::Severity {
		self.severity
	}
}
