// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Tracks offline validators.

use std::collections::HashMap;
use std::time::Duration;
use wasm_timer::Instant;

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
pub struct OfflineTracker<AuthorityId> {
	observed: HashMap<AuthorityId, Observed>,
}

impl<AuthorityId: Eq + Clone + std::hash::Hash> OfflineTracker<AuthorityId> {
	/// Create a new tracker.
	pub fn new() -> Self {
		OfflineTracker { observed: HashMap::new() }
	}

	/// Note new consensus is starting with the given set of validators.
	pub fn note_new_block(&mut self, validators: &[AuthorityId]) {
		use std::collections::HashSet;

		let set: HashSet<_> = validators.iter().cloned().collect();
		self.observed.retain(|k, _| set.contains(k));
	}

	/// Note that a round has ended.
	pub fn note_round_end(&mut self, validator: AuthorityId, was_online: bool) {
		self.observed.entry(validator)
			.or_insert_with(Observed::new)
			.note_round_end(was_online);
	}

	/// Generate a vector of indices for offline account IDs.
	pub fn reports(&self, validators: &[AuthorityId]) -> Vec<u32> {
		validators.iter()
			.enumerate()
			.filter_map(|(i, v)| if self.is_online(v) {
				None
			} else {
				Some(i as u32)
			})
			.collect()
	}

	/// Whether reports on a validator set are consistent with our view of things.
	pub fn check_consistency(&self, validators: &[AuthorityId], reports: &[u32]) -> bool {
		reports.iter().cloned().all(|r| {
			let v = match validators.get(r as usize) {
				Some(v) => v,
				None => return false,
			};

			// we must think all validators reported externally are offline.
			let thinks_online = self.is_online(v);
			!thinks_online
		})
	}

	fn is_online(&self, v: &AuthorityId) -> bool {
		self.observed.get(v).map(Observed::is_active).unwrap_or(true)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn validator_offline() {
		let mut tracker = OfflineTracker::<u64>::new();
		let v1 = 1;
		let v2 = 2;
		let v3 = 3;
		tracker.note_round_end(v1, true);
		tracker.note_round_end(v2, true);
		tracker.note_round_end(v3, true);

		let slash_time = REPORT_TIME + Duration::from_secs(5);
		tracker.observed.get_mut(&v1).unwrap().offline_since -= slash_time;
		tracker.observed.get_mut(&v2).unwrap().offline_since -= slash_time;

		assert_eq!(tracker.reports(&[v1, v2, v3]), vec![0, 1]);

		tracker.note_new_block(&[v1, v3]);
		assert_eq!(tracker.reports(&[v1, v2, v3]), vec![0]);
	}
}
