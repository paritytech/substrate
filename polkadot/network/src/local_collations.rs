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

//! Local collations to be circulated to validators.
//!
//! Collations are attempted to be repropagated when a new validator connects,
//! a validator changes his session key, or when they are generated.

use polkadot_primitives::{Hash, SessionKey};

use collator_pool::Role;

use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

const LIVE_FOR: Duration = Duration::from_secs(60 * 5);

struct LocalCollation<C> {
	targets: HashSet<SessionKey>,
	collation: C,
	live_since: Instant,
}

/// Tracker for locally collated values and which validators to send them to.
pub struct LocalCollations<C> {
	primary_for: HashSet<SessionKey>,
	local_collations: HashMap<Hash, LocalCollation<C>>,
}

impl<C: Clone> LocalCollations<C> {
	/// Create a new `LocalCollations` tracker.
	pub fn new() -> Self {
		LocalCollations {
			primary_for: HashSet::new(),
			local_collations: HashMap::new(),
		}
	}

	/// Validator gave us a new role. If the new role is "primary", this function might return
	/// a set of collations to send to that validator.
	pub fn note_validator_role(&mut self, key: SessionKey, role: Role) -> Vec<(Hash, C)> {
		match role {
			Role::Backup => {
				self.primary_for.remove(&key);
				Vec::new()
			}
			Role::Primary => {
				let new_primary = self.primary_for.insert(key);
				if new_primary {
					self.collations_targeting(&key)
				} else {
					Vec::new()
				}
			}
		}
	}

	/// Fresh session key from a validator. Returns a vector of collations to send
	/// to the validator.
	pub fn fresh_key(&mut self, old_key: &SessionKey, new_key: &SessionKey) -> Vec<(Hash, C)> {
		if self.primary_for.remove(old_key) {
			self.primary_for.insert(*new_key);

			self.collations_targeting(new_key)
		} else {
			Vec::new()
		}
	}

	/// Validator disconnected.
	pub fn on_disconnect(&mut self, key: &SessionKey) {
		self.primary_for.remove(key);
	}

	/// Mark collations relevant to the given parent hash as obsolete.
	pub fn collect_garbage(&mut self, relay_parent: Option<&Hash>) {
		if let Some(relay_parent) = relay_parent {
			self.local_collations.remove(relay_parent);
		}

		let now = Instant::now();
		self.local_collations.retain(|_, v| v.live_since + LIVE_FOR > now);
	}

	/// Add a collation. Returns an iterator of session keys to send to and lazy copies of the collation.
	pub fn add_collation<'a>(
		&'a mut self,
		relay_parent: Hash,
		targets: HashSet<SessionKey>,
		collation: C
	)
		-> impl Iterator<Item=(SessionKey, C)> + 'a
	{
		self.local_collations.insert(relay_parent, LocalCollation {
			targets,
			collation,
			live_since: Instant::now(),
		});

		let local = self.local_collations.get(&relay_parent)
			.expect("just inserted to this key; qed");

		let borrowed_collation = &local.collation;
		local.targets
			.intersection(&self.primary_for)
			.map(move |k| (*k, borrowed_collation.clone()))
	}

	fn collations_targeting(&self, key: &SessionKey) -> Vec<(Hash, C)> {
		self.local_collations.iter()
			.filter(|&(_, ref v)| v.targets.contains(key))
			.map(|(h, v)| (*h, v.collation.clone()))
			.collect()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn add_validator_with_ready_collation() {
		let key = [1; 32].into();
		let relay_parent = [2; 32].into();
		let targets = {
			let mut set = HashSet::new();
			set.insert(key);
			set
		};

		let mut tracker = LocalCollations::new();
		assert!(tracker.add_collation(relay_parent, targets, 5).next().is_none());
		assert_eq!(tracker.note_validator_role(key, Role::Primary), vec![(relay_parent, 5)]);
	}

	#[test]
	fn rename_with_ready() {
		let orig_key = [1; 32].into();
		let new_key  = [2; 32].into();
		let relay_parent = [255; 32].into();
		let targets = {
			let mut set = HashSet::new();
			set.insert(new_key);
			set
		};

		let mut tracker: LocalCollations<u8> = LocalCollations::new();
		assert!(tracker.add_collation(relay_parent, targets, 5).next().is_none());
		assert!(tracker.note_validator_role(orig_key, Role::Primary).is_empty());
		assert_eq!(tracker.fresh_key(&orig_key, &new_key), vec![(relay_parent, 5u8)]);
	}

	#[test]
	fn collecting_garbage() {
		let relay_parent_a = [255; 32].into();
		let relay_parent_b = [222; 32].into();

		let mut tracker: LocalCollations<u8> = LocalCollations::new();
		assert!(tracker.add_collation(relay_parent_a, HashSet::new(), 5).next().is_none());
		assert!(tracker.add_collation(relay_parent_b, HashSet::new(), 69).next().is_none());

		let live_since = Instant::now() - LIVE_FOR - Duration::from_secs(10);
		tracker.local_collations.get_mut(&relay_parent_b).unwrap().live_since = live_since;

		tracker.collect_garbage(Some(&relay_parent_a));

		// first one pruned because of relay parent, other because of time.
		assert!(tracker.local_collations.is_empty());
	}

	#[test]
	fn add_collation_with_connected_target() {
		let key = [1; 32].into();
		let relay_parent = [2; 32].into();
		let targets = {
			let mut set = HashSet::new();
			set.insert(key);
			set
		};

		let mut tracker = LocalCollations::new();
		assert!(tracker.note_validator_role(key, Role::Primary).is_empty());
		assert_eq!(tracker.add_collation(relay_parent, targets, 5).next(), Some((key, 5)));

	}
}
