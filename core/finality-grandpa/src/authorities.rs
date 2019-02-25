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

use fork_tree::ForkTree;
use parking_lot::RwLock;
use substrate_primitives::Ed25519AuthorityId;
use grandpa::VoterSet;
use parity_codec_derive::{Encode, Decode};
use log::{debug, info};

use std::cmp::Ord;
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

impl<H, N> SharedAuthoritySet<H, N>
where H: PartialEq,
	  N: Ord,
{
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
where N: Add<Output=N> + Ord + Clone + Debug,
	  H: Clone + Debug
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
	pub(crate) fn current_authorities(&self) -> VoterSet<Ed25519AuthorityId> {
		self.inner.read().current_authorities.iter().cloned().collect()
	}
}

impl<H, N> From<AuthoritySet<H, N>> for SharedAuthoritySet<H, N> {
	fn from(set: AuthoritySet<H, N>) -> Self {
		SharedAuthoritySet { inner: Arc::new(RwLock::new(set)) }
	}
}

/// Status of the set after changes were applied.
#[derive(Debug)]
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
	pending_changes: ForkTree<H, N, PendingChange<H, N>>,
}

impl<H, N> AuthoritySet<H, N>
where H: PartialEq,
	  N: Ord,
{
	/// Get a genesis set with given authorities.
	pub(crate) fn genesis(initial: Vec<(Ed25519AuthorityId, u64)>) -> Self {
		AuthoritySet {
			current_authorities: initial,
			set_id: 0,
			pending_changes: ForkTree::new(),
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
	H: Clone + Debug
{
	/// Note an upcoming pending transition. Multiple pending changes on the
	/// same branch can be added as long as they don't overlap. This method
	/// assumes that changes on the same branch will be added in-order. The
	/// given function `is_descendent_of` should return `true` if the second
	/// hash (target) is a descendent of the first hash (base).
	pub(crate) fn add_pending_change<F, E>(
		&mut self,
		pending: PendingChange<H, N>,
		is_descendent_of: &F,
	) -> Result<(), fork_tree::Error<E>> where
		F: Fn(&H, &H) -> Result<bool, E>,
		E:  std::error::Error,
	{
		let hash = pending.canon_hash.clone();
		let number = pending.canon_height.clone();

		debug!(target: "afg", "Inserting potential set change signalled at block {:?} \
							   (delayed by {:?} blocks).",
			   (&number, &hash), pending.finalization_depth);

		self.pending_changes.import(
			hash.clone(),
			number.clone(),
			pending,
			is_descendent_of,
		)?;

		debug!(target: "afg", "There are now {} alternatives for the next pending change (roots), \
							   and a total of {} pending changes (across all forks).",
			self.pending_changes.roots().count(),
			self.pending_changes.iter().count(),
		);

		Ok(())
	}

	/// Inspect pending changes. Pending changes in the tree are traversed in pre-order.
	pub(crate) fn pending_changes(&self) -> impl Iterator<Item=&PendingChange<H, N>> {
		self.pending_changes.iter().map(|(_, _, c)| c)
	}

	/// Get the earliest limit-block number, if any. If there are pending
	/// changes across different forks, this method will return the earliest
	/// effective number (across the different branches).
	pub(crate) fn current_limit(&self) -> Option<N> {
		self.pending_changes.roots()
			.min_by_key(|&(_, _, c)| c.effective_number())
			.map(|(_, _, c)| c.effective_number())
	}

	/// Apply or prune any pending transitions. This method ensures that if
	/// there are multiple changes in the same branch, finalizing this block
	/// won't finalize past multiple transitions (i.e. transitions must be
	/// finalized in-order). The given function `is_descendent_of` should return
	/// `true` if the second hash (target) is a descendent of the first hash
	/// (base).
	///
	/// When the set has changed, the return value will be `Ok(Some((H, N)))`
	/// which is the canonical block where the set last changed (i.e. the given
	/// hash and number).
	pub(crate) fn apply_changes<F, E>(
		&mut self,
		finalized_hash: H,
		finalized_number: N,
		is_descendent_of: &F,
	) -> Result<Status<H, N>, fork_tree::Error<E>>
	where F: Fn(&H, &H) -> Result<bool, E>,
		  E: std::error::Error,
	{
		let mut status = Status {
			changed: false,
			new_set_block: None,
		};

		match self.pending_changes.finalize_with_descendent_if(
			&finalized_hash,
			finalized_number.clone(),
			is_descendent_of,
			|change| change.effective_number() <= finalized_number
		)? {
			fork_tree::FinalizationResult::Changed(change) => {
				status.changed = true;

				if let Some(change) = change {
					info!(target: "finality", "Applying authority set change scheduled at block #{:?}",
						  change.canon_height);

					self.current_authorities = change.next_authorities;
					self.set_id += 1;

					status.new_set_block = Some((
						finalized_hash,
						finalized_number,
					));
				}
			},
			fork_tree::FinalizationResult::Unchanged => {},
		}

		Ok(status)
	}

	/// Check whether the given finalized block number enacts any authority set
	/// change (without triggering it), ensuring that if there are multiple
	/// changes in the same branch, finalizing this block won't finalize past
	/// multiple transitions (i.e. transitions must be finalized in-order). The
	/// given function `is_descendent_of` should return `true` if the second
	/// hash (target) is a descendent of the first hash (base).
	pub fn enacts_change<F, E>(
		&self,
		finalized_hash: H,
		finalized_number: N,
		is_descendent_of: &F,
	) -> Result<bool, fork_tree::Error<E>>
	where F: Fn(&H, &H) -> Result<bool, E>,
		  E: std::error::Error,
	{
		self.pending_changes.finalizes_any_with_descendent_if(
			&finalized_hash,
			finalized_number.clone(),
			is_descendent_of,
			|change| change.effective_number() == finalized_number
		)
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

	fn static_is_descendent_of<A>(value: bool)
		-> impl Fn(&A, &A) -> Result<bool, std::io::Error>
	{
		move |_, _| Ok(value)
	}

	fn is_descendent_of<A, F>(f: F) -> impl Fn(&A, &A) -> Result<bool, std::io::Error>
		where F: Fn(&A, &A) -> bool
	{
		move |base, hash| Ok(f(base, hash))
	}

	#[test]
	fn changes_iterated_in_pre_order() {
		let mut authorities = AuthoritySet {
			current_authorities: Vec::new(),
			set_id: 0,
			pending_changes: ForkTree::new(),
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
			canon_height: 5,
			canon_hash: "hash_b",
		};

		let change_c = PendingChange {
			next_authorities: Vec::new(),
			finalization_depth: 5,
			canon_height: 10,
			canon_hash: "hash_c",
		};

		authorities.add_pending_change(change_a.clone(), &static_is_descendent_of(false)).unwrap();
		authorities.add_pending_change(change_b.clone(), &static_is_descendent_of(false)).unwrap();
		authorities.add_pending_change(change_c.clone(), &is_descendent_of(|base, hash| match (*base, *hash) {
			("hash_a", "hash_c") => true,
			("hash_b", "hash_c") => false,
			_ => unreachable!(),
		})).unwrap();

		assert_eq!(
			authorities.pending_changes().collect::<Vec<_>>(),
			vec![&change_b, &change_a, &change_c],
		);
	}

	#[test]
	fn apply_change() {
		let mut authorities = AuthoritySet {
			current_authorities: Vec::new(),
			set_id: 0,
			pending_changes: ForkTree::new(),
		};

		let set_a = vec![([1; 32].into(), 5)];
		let set_b = vec![([2; 32].into(), 5)];

		// two competing changes at the same height on different forks
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

		authorities.add_pending_change(change_a.clone(), &static_is_descendent_of(true)).unwrap();
		authorities.add_pending_change(change_b.clone(), &static_is_descendent_of(true)).unwrap();

		assert_eq!(
			authorities.pending_changes().collect::<Vec<_>>(),
			vec![&change_b, &change_a],
		);

		// finalizing "hash_c" won't enact the change signalled at "hash_a" but it will prune out "hash_b"
		let status = authorities.apply_changes("hash_c", 11, &is_descendent_of(|base, hash| match (*base, *hash) {
			("hash_a", "hash_c") => true,
			("hash_b", "hash_c") => false,
			_ => unreachable!(),
		})).unwrap();

		assert!(status.changed);
		assert_eq!(status.new_set_block, None);
		assert_eq!(
			authorities.pending_changes().collect::<Vec<_>>(),
			vec![&change_a],
		);

		// finalizing "hash_d" will enact the change signalled at "hash_a"
		let status = authorities.apply_changes("hash_d", 15, &is_descendent_of(|base, hash| match (*base, *hash) {
			("hash_a", "hash_d") => true,
			_ => unreachable!(),
		})).unwrap();

		assert!(status.changed);
		assert_eq!(status.new_set_block, Some(("hash_d", 15)));

		assert_eq!(authorities.current_authorities, set_a);
		assert_eq!(authorities.set_id, 1);
		assert_eq!(authorities.pending_changes().count(), 0);
	}

	#[test]
	fn disallow_multiple_changes_being_finalized_at_once() {
		let mut authorities = AuthoritySet {
			current_authorities: Vec::new(),
			set_id: 0,
			pending_changes: ForkTree::new(),
		};

		let set_a = vec![([1; 32].into(), 5)];
		let set_c = vec![([2; 32].into(), 5)];

		// two competing changes at the same height on different forks
		let change_a = PendingChange {
			next_authorities: set_a.clone(),
			finalization_depth: 10,
			canon_height: 5,
			canon_hash: "hash_a",
		};

		let change_c = PendingChange {
			next_authorities: set_c.clone(),
			finalization_depth: 10,
			canon_height: 30,
			canon_hash: "hash_c",
		};

		authorities.add_pending_change(change_a.clone(), &static_is_descendent_of(true)).unwrap();
		authorities.add_pending_change(change_c.clone(), &static_is_descendent_of(true)).unwrap();

		let is_descendent_of = is_descendent_of(|base, hash| match (*base, *hash) {
			("hash_a", "hash_b") => true,
			("hash_a", "hash_c") => true,
			("hash_a", "hash_d") => true,

			("hash_c", "hash_b") => false,
			("hash_c", "hash_d") => true,

			("hash_b", "hash_c") => true,
			_ => unreachable!(),
		});

		// trying to finalize past `change_c` without finalizing `change_a` first
		match authorities.apply_changes("hash_d", 40, &is_descendent_of) {
			Err(fork_tree::Error::UnfinalizedAncestor) => {},
			_ => unreachable!(),
		}

		let status = authorities.apply_changes("hash_b", 15, &is_descendent_of).unwrap();
		assert!(status.changed);
		assert_eq!(status.new_set_block, Some(("hash_b", 15)));

		assert_eq!(authorities.current_authorities, set_a);
		assert_eq!(authorities.set_id, 1);

		// after finalizing `change_a` it should be possible to finalize `change_c`
		let status = authorities.apply_changes("hash_d", 40, &is_descendent_of).unwrap();
		assert!(status.changed);
		assert_eq!(status.new_set_block, Some(("hash_d", 40)));

		assert_eq!(authorities.current_authorities, set_c);
		assert_eq!(authorities.set_id, 2);
	}

	#[test]
	fn enacts_change_works() {
		let mut authorities = AuthoritySet {
			current_authorities: Vec::new(),
			set_id: 0,
			pending_changes: ForkTree::new(),
		};

		let set_a = vec![([1; 32].into(), 5)];

		let change_a = PendingChange {
			next_authorities: set_a.clone(),
			finalization_depth: 10,
			canon_height: 5,
			canon_hash: "hash_a",
		};

		authorities.add_pending_change(change_a.clone(), &static_is_descendent_of(false)).unwrap();

		let is_descendent_of = is_descendent_of(|base, hash| match (*base, *hash) {
			("hash_a", "hash_b") => true,
			("hash_a", "hash_c") => false,
			_ => unreachable!(),
		});

		// "hash_c" won't finalize the existing change since it isn't a descendent
		assert!(!authorities.enacts_change("hash_c", 15, &is_descendent_of).unwrap());

		// "hash_b" at depth 14 won't work either
		assert!(!authorities.enacts_change("hash_b", 14, &is_descendent_of).unwrap());

		// but it should work at depth 15 (change height + depth)
		assert!(authorities.enacts_change("hash_b", 15, &is_descendent_of).unwrap());
	}
}
