// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Tracks offline validators.

use polkadot_primitives::AccountId;

use std::collections::HashMap;
use std::time::{Instant, Duration};

// time before we report a validator.
const REPORT_TIME: Duration = Duration::from_secs(60 * 5);

struct Observed {
	last_round_end: Instant,
	offline_since: Instant,
}

impl Observed {
	fn new() -> Observed {
		let now = Instant::now();
		Observed {
			last_round_end: now,
			offline_since: now,
		}
	}

	fn note_round_end(&mut self, was_online: bool) {
		let now = Instant::now();

		self.last_round_end = now;
		if was_online {
			self.offline_since = now;
		}
	}

	fn is_active(&self) -> bool {
		// can happen if clocks are not monotonic
		if self.offline_since > self.last_round_end { return true }
		self.last_round_end.duration_since(self.offline_since) < REPORT_TIME
	}
}

/// Tracks offline validators and can issue a report for those offline.
pub struct OfflineTracker {
	observed: HashMap<AccountId, Observed>,
}

impl OfflineTracker {
	/// Create a new tracker.
	pub fn new() -> Self {
		OfflineTracker { observed: HashMap::new() }
	}

	/// Note new consensus is starting with the given set of validators.
	pub fn note_new_block(&mut self, validators: &[AccountId]) {
		use std::collections::HashSet;

		let set: HashSet<_> = validators.iter().cloned().collect();
		self.observed.retain(|k, _| set.contains(k));
	}

	/// Note that a round has ended.
	pub fn note_round_end(&mut self, validator: AccountId, was_online: bool) {
		self.observed.entry(validator)
			.or_insert_with(Observed::new)
			.note_round_end(was_online);
	}

	/// Generate a vector of reports for the given account IDs.
	/// The length of the vector will be the same as the length of the validator
	/// list.
	/// `None` is "not enough data", `true` is "online", and `false` is "offline".
	pub fn reports(&self, validators: &[AccountId]) -> Vec<Option<bool>> {
		validators.iter()
			.map(|v| self.observed.get(v).map(Observed::is_active))
			.collect()
	}
}
