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

struct Observed {
	last_round_end: Instant,
	offline_since: Instant,
}

#[derive(Eq, PartialEq)]
enum Activity {
	Offline,
	StillOffline(Duration),
	Online,
}

impl Observed {
	fn new() -> Observed {
		let now = Instant::now();
		Observed {
			last_round_end: now,
			offline_since: now,
		}
	}

	fn note_round_end(&mut self, now: Instant, was_online: Option<bool>) {
		self.last_round_end = now;
		if let Some(false) = was_online {
			self.offline_since = now;
		}
	}

	/// Returns what we have observed about the online/offline state of the validator.
	fn activity(&self) -> Activity {
		// can happen if clocks are not monotonic
		if self.offline_since > self.last_round_end { return Activity::Online }
		if self.offline_since == self.last_round_end { return Activity::Offline }
		Activity::StillOffline(self.last_round_end.duration_since(self.offline_since))
	}
}

/// Tracks offline validators and can issue a report for those offline.
pub struct OfflineTracker {
	observed: HashMap<AccountId, Observed>,
	block_instant: Instant,
}

impl OfflineTracker {
	/// Create a new tracker.
	pub fn new() -> Self {
		OfflineTracker { observed: HashMap::new(), block_instant: Instant::now() }
	}

	/// Note new consensus is starting with the given set of validators.
	pub fn note_new_block(&mut self, validators: &[AccountId]) {
		use std::collections::HashSet;

		let set: HashSet<_> = validators.iter().cloned().collect();
		self.observed.retain(|k, _| set.contains(k));

		self.block_instant = Instant::now();
	}

	/// Note that a round has ended.
	pub fn note_round_end(&mut self, validator: AccountId, was_online: bool) {
		self.observed.entry(validator).or_insert_with(Observed::new);
		for (val, obs) in self.observed.iter_mut() {
			obs.note_round_end(
				self.block_instant,
				if val == &validator {
					Some(was_online)
				} else {
					None
				}
			)
		}
	}

	/// Generate a vector of indices for offline account IDs.
	pub fn reports(&self, validators: &[AccountId]) -> Vec<u32> {
		validators.iter()
			.enumerate()
			.filter_map(|(i, v)| if self.is_known_offline_now(v) {
				Some(i as u32)
			} else {
				None
			})
			.collect()
	}

	/// Whether reports on a validator set are consistent with our view of things.
	pub fn check_consistency(&self, validators: &[AccountId], reports: &[u32]) -> bool {
		reports.iter().cloned().all(|r| {
			let v = match validators.get(r as usize) {
				Some(v) => v,
				None => return false,
			};

			// we must think all validators reported externally are offline.
			self.is_known_offline_now(v)
		})
	}

	/// Rwturns true only if we have seen the validator miss the last round. For further
	/// rounds where we can't say for sure that they're still offline, we give them the
	/// benefit of the doubt.
	fn is_known_offline_now(&self, v: &AccountId) -> bool {
		self.observed.get(v).map(|o| o.activity() == Activity::Offline).unwrap_or(false)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn validator_offline() {
		let mut tracker = OfflineTracker::new();
		let v = [0; 32].into();
		let v2 = [1; 32].into();
		let v3 = [2; 32].into();
		tracker.note_new_block(&[v, v2, v3]);
		tracker.note_round_end(v, true);
		tracker.note_round_end(v2, true);
		tracker.note_round_end(v3, true);
		assert_eq!(tracker.reports(&[v, v2, v3]), vec![0u32; 0]);

		tracker.note_new_block(&[v, v2, v3]);
		tracker.note_round_end(v, true);
		tracker.note_round_end(v2, false);
		tracker.note_round_end(v3, true);
		assert_eq!(tracker.reports(&[v, v2, v3]), vec![1]);

		tracker.note_new_block(&[v, v2, v3]);
		tracker.note_round_end(v, false);
		assert_eq!(tracker.reports(&[v, v2, v3]), vec![0]);

		tracker.note_new_block(&[v, v2, v3]);
		tracker.note_round_end(v, false);
		tracker.note_round_end(v2, true);
		tracker.note_round_end(v3, false);
		assert_eq!(tracker.reports(&[v, v2, v3]), vec![0, 2]);

		tracker.note_new_block(&[v, v2]);
		tracker.note_round_end(v, false);
		assert_eq!(tracker.reports(&[v, v2, v3]), vec![0]);
	}
}
