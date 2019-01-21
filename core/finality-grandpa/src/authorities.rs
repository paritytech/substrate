// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Utilities for dealing with authorities, authority sets, and handoffs.

use parking_lot::RwLock;
use substrate_primitives::Ed25519AuthorityId;

use std::cmp::Ord;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::Add;
use std::sync::Arc;

/// A shared authority set.
pub(crate) struct SharedAuthoritySet<H, N> {
	inner: Arc<RwLock<AuthoritySet<H, N>>>,
}

impl<H, N> Clone for SharedAuthoritySet<H, N> {
	fn clone(&self) -> Self {
		SharedAuthoritySet { inner: self.inner.clone() }
	}
}

impl<H, N> SharedAuthoritySet<H, N> {
	/// The genesis authority set.
	pub(crate) fn genesis(initial: Vec<(Ed25519AuthorityId, u64)>) -> Self {
		SharedAuthoritySet {
			inner: Arc::new(RwLock::new(AuthoritySet::genesis(initial)))
		}
	}

	/// Acquire a reference to the inner read-write lock.
	pub(crate) fn inner(&self) -> &RwLock<AuthoritySet<H, N>> {
		&*self.inner
	}
}

impl<H: Eq, N> SharedAuthoritySet<H, N>
where
	N: Add<Output=N> + Ord + Clone + Debug,
	H: Debug
{
	/// Get the earliest limit-block number, if any.
	pub(crate) fn current_limit(&self) -> Option<N> {
		self.inner.read().current_limit()
	}

	/// Get the current set ID. This is incremented every time the set changes.
	pub(crate) fn set_id(&self) -> u64 {
		self.inner.read().set_id
	}

	/// Get the current authorities and their weights (for the current set ID).
	pub(crate) fn current_authorities(&self) -> HashMap<Ed25519AuthorityId, u64> {
		self.inner.read().current_authorities.iter().cloned().collect()
	}
}

impl<H, N> From<AuthoritySet<H, N>> for SharedAuthoritySet<H, N> {
	fn from(set: AuthoritySet<H, N>) -> Self {
		SharedAuthoritySet { inner: Arc::new(RwLock::new(set)) }
	}
}

/// Status of the set after changes were applied.
pub(crate) struct Status<H, N> {
	/// Whether internal changes were made.
	pub(crate) changed: bool,
	/// `Some` when underlying authority set has changed, containing the
	/// block where that set changed.
	pub(crate) new_set_block: Option<(H, N)>,
}

/// A set of authorities.
#[derive(Debug, Clone, Encode, Decode)]
pub(crate) struct AuthoritySet<H, N> {
	current_authorities: Vec<(Ed25519AuthorityId, u64)>,
	set_id: u64,
	pending_changes: Vec<PendingChange<H, N>>,
}

impl<H, N> AuthoritySet<H, N> {
	/// Get a genesis set with given authorities.
	pub(crate) fn genesis(initial: Vec<(Ed25519AuthorityId, u64)>) -> Self {
		AuthoritySet {
			current_authorities: initial,
			set_id: 0,
			pending_changes: Vec::new(),
		}
	}

	/// Get the current set id and a reference to the current authority set.
	pub(crate) fn current(&self) -> (u64, &[(Ed25519AuthorityId, u64)]) {
		(self.set_id, &self.current_authorities[..])
	}
}

impl<H: Eq, N> AuthoritySet<H, N>
where
	N: Add<Output=N> + Ord + Clone + Debug,
	H: Debug
{
	/// Note an upcoming pending transition. This makes sure that there isn't
	/// already any pending change for the same chain. Multiple pending changes
	/// are allowed but they must be signalled in different forks. The closure
	/// should return an error if the pending change block is equal to or a
	/// descendent of the given block.
	pub(crate) fn add_pending_change<F, E: Debug>(
		&mut self,
		pending: PendingChange<H, N>,
		is_equal_or_descendent_of: F,
	) -> Result<(), E> where
		F: Fn(&H) -> Result<(), E>,
	{
		for change in self.pending_changes.iter() {
			is_equal_or_descendent_of(&change.canon_hash)?;
		}

		// ordered first by effective number and then by signal-block number.
		let key = (pending.effective_number(), pending.canon_height.clone());
		let idx = self.pending_changes
			.binary_search_by_key(&key, |change| (
				change.effective_number(),
				change.canon_height.clone(),
			))
			.unwrap_or_else(|i| i);

		self.pending_changes.insert(idx, pending);

		Ok(())
	}

	/// Inspect pending changes.
	pub(crate) fn pending_changes(&self) -> &[PendingChange<H, N>] {
		&self.pending_changes
	}

	/// Get the earliest limit-block number, if any.
	pub(crate) fn current_limit(&self) -> Option<N> {
		self.pending_changes.get(0).map(|change| change.effective_number().clone())
	}

	/// Apply or prune any pending transitions. Provide a closure that can be used to check for the
	/// finalized block with given number.
	///
	/// When the set has changed, the return value will be `Ok(Some((H, N)))` which is the canonical
	/// block where the set last changed.
	pub(crate) fn apply_changes<F, E>(&mut self, just_finalized: N, mut canonical: F)
		-> Result<Status<H, N>, E>
		where F: FnMut(N) -> Result<Option<H>, E>
	{
		let mut status = Status {
			changed: false,
			new_set_block: None,
		};
		loop {
			let remove_up_to = match self.pending_changes.first() {
				None => break,
				Some(change) => {
					let effective_number = change.effective_number();
					if effective_number > just_finalized { break }

					// check if the block that signalled the change is canonical in
					// our chain.
					let canonical_hash = canonical(change.canon_height.clone())?;
					let effective_hash = canonical(effective_number.clone())?;

					debug!(target: "afg", "Evaluating potential set change at block {:?}. Our canonical hash is {:?}",
						(&change.canon_height, &change.canon_hash), canonical_hash);

					match (canonical_hash, effective_hash) {
						(Some(canonical_hash), Some(effective_hash)) => {
							if canonical_hash == change.canon_hash {
								// apply this change: make the set canonical
								info!(target: "finality", "Applying authority set change scheduled at block #{:?}",
									  change.canon_height);

								self.current_authorities = change.next_authorities.clone();
								self.set_id += 1;

								status.new_set_block = Some((
									effective_hash,
									effective_number.clone(),
								));

								// discard all signalled changes since they're
								// necessarily from other forks
								self.pending_changes.len()
							} else {
								1 // prune out this entry; it's no longer relevant.
							}
						},
						_ => 1, // prune out this entry; it's no longer relevant.
					}
				}
			};

			let remove_up_to = ::std::cmp::min(remove_up_to, self.pending_changes.len());
			self.pending_changes.drain(..remove_up_to);
			status.changed = true; // always changed because we strip at least the first change.
		}

		Ok(status)
	}

	/// Check whether the given finalized block number enacts any authority set
	/// change (without triggering it). Provide a closure that can be used to
	/// check for the canonical block with a given number.
	pub fn enacts_change<F, E>(&self, just_finalized: N, mut canonical: F)
		-> Result<bool, E>
		where F: FnMut(N) -> Result<Option<H>, E>
	{
		for change in self.pending_changes.iter() {
			if change.effective_number() > just_finalized { break };

			// check if the block that signalled the change is canonical in
			// our chain.
			match canonical(change.canon_height.clone())? {
				Some(ref canonical_hash) if *canonical_hash == change.canon_hash =>
					return Ok(true),
				_ => (),
			}
		}

		Ok(false)
	}
}

/// A pending change to the authority set.
///
/// This will be applied when the announcing block is at some depth within
/// the finalized chain.
#[derive(Debug, Clone, Encode, Decode, PartialEq)]
pub(crate) struct PendingChange<H, N> {
	/// The new authorities and weights to apply.
	pub(crate) next_authorities: Vec<(Ed25519AuthorityId, u64)>,
	/// How deep in the finalized chain the announcing block must be
	/// before the change is applied.
	pub(crate) finalization_depth: N,
	/// The announcing block's height.
	pub(crate) canon_height: N,
	/// The announcing block's hash.
	pub(crate) canon_hash: H,
}

impl<H, N: Add<Output=N> + Clone> PendingChange<H, N> {
	/// Returns the effective number this change will be applied at.
	pub fn effective_number(&self) -> N {
		self.canon_height.clone() + self.finalization_depth.clone()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn ignore_existing_changes<A>(_a: &A) -> Result<(), ::Error> {
		Ok(())
	}

	#[test]
	fn changes_sorted_in_correct_order() {
		let mut authorities = AuthoritySet {
			current_authorities: Vec::new(),
			set_id: 0,
			pending_changes: Vec::new(),
		};

		let change_a = PendingChange {
			next_authorities: Vec::new(),
			finalization_depth: 10,
			canon_height: 5,
			canon_hash: "hash_a",
		};

		let change_b = PendingChange {
			next_authorities: Vec::new(),
			finalization_depth: 0,
			canon_height: 16,
			canon_hash: "hash_b",
		};

		let change_c = PendingChange {
			next_authorities: Vec::new(),
			finalization_depth: 5,
			canon_height: 10,
			canon_hash: "hash_c",
		};

		authorities.add_pending_change(change_a.clone(), ignore_existing_changes).unwrap();
		authorities.add_pending_change(change_b.clone(), ignore_existing_changes).unwrap();
		authorities.add_pending_change(change_c.clone(), ignore_existing_changes).unwrap();

		assert_eq!(authorities.pending_changes, vec![change_a, change_c, change_b]);
	}

	#[test]
	fn apply_change() {
		let mut authorities = AuthoritySet {
			current_authorities: Vec::new(),
			set_id: 0,
			pending_changes: Vec::new(),
		};

		let set_a = vec![([1; 32].into(), 5)];
		let set_b = vec![([2; 32].into(), 5)];

		let change_a = PendingChange {
			next_authorities: set_a.clone(),
			finalization_depth: 10,
			canon_height: 5,
			canon_hash: "hash_a",
		};

		let change_b = PendingChange {
			next_authorities: set_b.clone(),
			finalization_depth: 10,
			canon_height: 5,
			canon_hash: "hash_b",
		};

		authorities.add_pending_change(change_a.clone(), ignore_existing_changes).unwrap();
		authorities.add_pending_change(change_b.clone(), ignore_existing_changes).unwrap();

		authorities.apply_changes(10, |_| Err(())).unwrap();
		assert!(authorities.current_authorities.is_empty());

		authorities.apply_changes(15, |n| match n {
			5 => Ok(Some("hash_a")),
			15 => Ok(Some("hash_15_canon")),
			_ => Err(()),
		}).unwrap();

		assert_eq!(authorities.current_authorities, set_a);
		assert_eq!(authorities.set_id, 1);
		assert!(authorities.pending_changes.is_empty());
	}

	#[test]
	fn disallow_multiple_changes_on_same_fork() {
		let mut authorities = AuthoritySet {
			current_authorities: Vec::new(),
			set_id: 0,
			pending_changes: Vec::new(),
		};

		let set_a = vec![([1; 32].into(), 5)];
		let set_b = vec![([2; 32].into(), 5)];
		let set_c = vec![([3; 32].into(), 5)];

		let change_a = PendingChange {
			next_authorities: set_a.clone(),
			finalization_depth: 10,
			canon_height: 5,
			canon_hash: "hash_a",
		};

		let change_b = PendingChange {
			next_authorities: set_b.clone(),
			finalization_depth: 10,
			canon_height: 16,
			canon_hash: "hash_b",
		};

		let change_c = PendingChange {
			next_authorities: set_c.clone(),
			finalization_depth: 10,
			canon_height: 16,
			canon_hash: "hash_c",
		};

		let is_equal_or_descendent_of = |base, block| -> Result<(), ()> {
			match (base, block) {
				("hash_a", "hash_b") => return Err(()),
				("hash_a", "hash_c") => return Ok(()),
				("hash_c", "hash_b") => return Ok(()),
				_ => unreachable!(),
			}
		};

		authorities.add_pending_change(
			change_a.clone(),
			|base| is_equal_or_descendent_of(base, change_a.canon_hash),
		).unwrap();

		// change b is on the same chain has the unfinalized change a so it should error
		assert!(
			authorities.add_pending_change(
				change_b.clone(),
				|base| is_equal_or_descendent_of(base, change_b.canon_hash),
			).is_err()
		);

		// change c is accepted because it's on a different fork
		authorities.add_pending_change(
			change_c.clone(),
			|base| is_equal_or_descendent_of(base, change_c.canon_hash)
		).unwrap();

		authorities.apply_changes(15, |n| match n {
			5 => Ok(Some("hash_a")),
			15 => Ok(Some("hash_a15")),
			_ => Err(()),
		}).unwrap();

		assert_eq!(authorities.current_authorities, set_a);

		// pending change c has been removed since it was on a different fork
		// and can no longer be enacted
		assert!(authorities.pending_changes.is_empty());

		// pending change b can now be added
		authorities.add_pending_change(
			change_b.clone(),
			|base| is_equal_or_descendent_of(base, change_b.canon_hash),
		).unwrap();
	}
}
