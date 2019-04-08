// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
use substrate_primitives::ed25519;
use grandpa::voter_set::VoterSet;
use parity_codec::{Encode, Decode};
use log::{debug, info};
use substrate_telemetry::{telemetry, CONSENSUS_INFO};

use std::cmp::Ord;
use std::fmt::Debug;
use std::ops::Add;
use std::sync::Arc;

use ed25519::Public as AuthorityId;

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
	pub(crate) fn current_authorities(&self) -> VoterSet<AuthorityId> {
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
#[derive(Debug, Clone, Encode, Decode, PartialEq)]
pub(crate) struct AuthoritySet<H, N> {
	pub(crate) current_authorities: Vec<(AuthorityId, u64)>,
	pub(crate) set_id: u64,
	// Tree of pending standard changes across forks. Standard changes are
	// enacted on finality and must be enacted (i.e. finalized) in-order across
	// a given branch
	pub(crate) pending_standard_changes: ForkTree<H, N, PendingChange<H, N>>,
	// Pending forced changes across different forks (at most one per fork).
	// Forced changes are enacted on block depth (not finality), for this reason
	// only one forced change should exist per fork.
	pub(crate) pending_forced_changes: Vec<PendingChange<H, N>>,
}

impl<H, N> AuthoritySet<H, N>
where H: PartialEq,
	  N: Ord,
{
	/// Get a genesis set with given authorities.
	pub(crate) fn genesis(initial: Vec<(AuthorityId, u64)>) -> Self {
		AuthoritySet {
			current_authorities: initial,
			set_id: 0,
			pending_standard_changes: ForkTree::new(),
			pending_forced_changes: Vec::new(),
		}
	}

	/// Get the current set id and a reference to the current authority set.
	pub(crate) fn current(&self) -> (u64, &[(AuthorityId, u64)]) {
		(self.set_id, &self.current_authorities[..])
	}
}

impl<H: Eq, N> AuthoritySet<H, N>
where
	N: Add<Output=N> + Ord + Clone + Debug,
	H: Clone + Debug
{
	fn add_standard_change<F, E>(
		&mut self,
		pending: PendingChange<H, N>,
		is_descendent_of: &F,
	) -> Result<(), fork_tree::Error<E>> where
		F: Fn(&H, &H) -> Result<bool, E>,
		E:  std::error::Error,
	{
		let hash = pending.canon_hash.clone();
		let number = pending.canon_height.clone();

		debug!(target: "afg", "Inserting potential standard set change signaled at block {:?} \
							   (delayed by {:?} blocks).",
			   (&number, &hash), pending.delay);

		self.pending_standard_changes.import(
			hash.clone(),
			number.clone(),
			pending,
			is_descendent_of,
		)?;

		debug!(target: "afg", "There are now {} alternatives for the next pending standard change (roots), \
							   and a total of {} pending standard changes (across all forks).",
			self.pending_standard_changes.roots().count(),
			self.pending_standard_changes.iter().count(),
		);

		Ok(())
	}

	fn add_forced_change<F, E>(
		&mut self,
		pending: PendingChange<H, N>,
		is_descendent_of: &F,
	) -> Result<(), fork_tree::Error<E>> where
		F: Fn(&H, &H) -> Result<bool, E>,
		E:  std::error::Error,
	{
		for change in self.pending_forced_changes.iter() {
			if change.canon_hash == pending.canon_hash ||
				is_descendent_of(&change.canon_hash, &pending.canon_hash)?
			{
				return Err(fork_tree::Error::UnfinalizedAncestor);
			}
		}

		// ordered first by effective number and then by signal-block number.
		let key = (pending.effective_number(), pending.canon_height.clone());
		let idx = self.pending_forced_changes
			.binary_search_by_key(&key, |change| (
				change.effective_number(),
				change.canon_height.clone(),
			))
			.unwrap_or_else(|i| i);

		debug!(target: "afg", "Inserting potential forced set change at block {:?} \
							   (delayed by {:?} blocks).",
			   (&pending.canon_height, &pending.canon_hash), pending.delay);

		self.pending_forced_changes.insert(idx, pending);

		debug!(target: "afg", "There are now {} pending forced changes.", self.pending_forced_changes.len());

		Ok(())
	}

	/// Note an upcoming pending transition. Multiple pending standard changes
	/// on the same branch can be added as long as they don't overlap. Forced
	/// changes are restricted to one per fork. This method assumes that changes
	/// on the same branch will be added in-order. The given function
	/// `is_descendent_of` should return `true` if the second hash (target) is a
	/// descendent of the first hash (base).
	pub(crate) fn add_pending_change<F, E>(
		&mut self,
		pending: PendingChange<H, N>,
		is_descendent_of: &F,
	) -> Result<(), fork_tree::Error<E>> where
		F: Fn(&H, &H) -> Result<bool, E>,
		E:  std::error::Error,
	{
		match pending.delay_kind {
			DelayKind::Best { .. } => {
				self.add_forced_change(pending, is_descendent_of)
			},
			DelayKind::Finalized => {
				self.add_standard_change(pending, is_descendent_of)
			},
		}
	}

	/// Inspect pending changes. Standard pending changes are iterated first,
	/// and the changes in the tree are traversed in pre-order, afterwards all
	/// forced changes are iterated.
	pub(crate) fn pending_changes(&self) -> impl Iterator<Item=&PendingChange<H, N>> {
		self.pending_standard_changes.iter().map(|(_, _, c)| c)
			.chain(self.pending_forced_changes.iter())
	}

	/// Get the earliest limit-block number, if any. If there are pending changes across
	/// different forks, this method will return the earliest effective number (across the
	/// different branches). Only standard changes are taken into account for the current
	/// limit, since any existing forced change should preclude the voter from voting.
	pub(crate) fn current_limit(&self) -> Option<N> {
		self.pending_standard_changes.roots()
			.min_by_key(|&(_, _, c)| c.effective_number())
			.map(|(_, _, c)| c.effective_number())
	}

	/// Apply or prune any pending transitions based on a best-block trigger.
	///
	/// Returns `Ok((median, new_set))` when a forced change has occurred. The
	/// median represents the median last finalized block at the time the change
	/// was signaled, and it should be used as the canon block when starting the
	/// new grandpa voter. Only alters the internal state in this case.
	///
	/// These transitions are always forced and do not lead to justifications
	/// which light clients can follow.
	pub(crate) fn apply_forced_changes<F, E>(
		&self,
		best_hash: H,
		best_number: N,
		is_descendent_of: &F,
	) -> Result<Option<(N, Self)>, E>
		where F: Fn(&H, &H) -> Result<bool, E>,
	{
		let mut new_set = None;

		for change in self.pending_forced_changes.iter()
			.take_while(|c| c.effective_number() <= best_number) // to prevent iterating too far
			.filter(|c| c.effective_number() == best_number)
		{
			// check if the given best block is in the same branch as the block that signaled the change.
			if is_descendent_of(&change.canon_hash, &best_hash)? {
				// apply this change: make the set canonical
				info!(target: "finality", "Applying authority set change forced at block #{:?}",
					  change.canon_height);
				telemetry!(CONSENSUS_INFO; "afg.applying_forced_authority_set_change";
					"block" => ?change.canon_height
				);

				let median_last_finalized = match change.delay_kind {
					DelayKind::Best { ref median_last_finalized } => median_last_finalized.clone(),
					_ => unreachable!("pending_forced_changes only contains forced changes; forced changes have delay kind Best; qed."),
				};

				new_set = Some((median_last_finalized, AuthoritySet {
					current_authorities: change.next_authorities.clone(),
					set_id: self.set_id + 1,
					pending_standard_changes: ForkTree::new(), // new set, new changes.
					pending_forced_changes: Vec::new(),
				}));

				break;
			}

			// we don't wipe forced changes until another change is
			// applied
		}

		Ok(new_set)
	}

	/// Apply or prune any pending transitions based on a finality trigger. This
	/// method ensures that if there are multiple changes in the same branch,
	/// finalizing this block won't finalize past multiple transitions (i.e.
	/// transitions must be finalized in-order). The given function
	/// `is_descendent_of` should return `true` if the second hash (target) is a
	/// descendent of the first hash (base).
	///
	/// When the set has changed, the return value will be `Ok(Some((H, N)))`
	/// which is the canonical block where the set last changed (i.e. the given
	/// hash and number).
	pub(crate) fn apply_standard_changes<F, E>(
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

		match self.pending_standard_changes.finalize_with_descendent_if(
			&finalized_hash,
			finalized_number.clone(),
			is_descendent_of,
			|change| change.effective_number() <= finalized_number
		)? {
			fork_tree::FinalizationResult::Changed(change) => {
				status.changed = true;

				// if we are able to finalize any standard change then we can
				// discard all pending forced changes (on different forks)
				self.pending_forced_changes.clear();

				if let Some(change) = change {
					info!(target: "finality", "Applying authority set change scheduled at block #{:?}",
						  change.canon_height);
					telemetry!(CONSENSUS_INFO; "afg.applying_scheduled_authority_set_change";
						"block" => ?change.canon_height
					);

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

	/// Check whether the given finalized block number enacts any standard
	/// authority set change (without triggering it), ensuring that if there are
	/// multiple changes in the same branch, finalizing this block won't
	/// finalize past multiple transitions (i.e. transitions must be finalized
	/// in-order). Returns `Some(true)` if the block being finalized enacts a
	/// change that can be immediately applied, `Some(false)` if the block being
	/// finalized enacts a change but it cannot be applied yet since there are
	/// other dependent changes, and `None` if no change is enacted. The given
	/// function `is_descendent_of` should return `true` if the second hash
	/// (target) is a descendent of the first hash (base).
	pub fn enacts_standard_change<F, E>(
		&self,
		finalized_hash: H,
		finalized_number: N,
		is_descendent_of: &F,
	) -> Result<Option<bool>, fork_tree::Error<E>>
	where F: Fn(&H, &H) -> Result<bool, E>,
		  E: std::error::Error,
	{
		self.pending_standard_changes.finalizes_any_with_descendent_if(
			&finalized_hash,
			finalized_number.clone(),
			is_descendent_of,
			|change| change.effective_number() == finalized_number
		)
	}
}

/// Kinds of delays for pending changes.
#[derive(Debug, Clone, Encode, Decode, PartialEq)]
pub(crate) enum DelayKind<N> {
	/// Depth in finalized chain.
	Finalized,
	/// Depth in best chain. The median last finalized block is calculated at the time the
	/// change was signaled.
	Best { median_last_finalized: N },
}

/// A pending change to the authority set.
///
/// This will be applied when the announcing block is at some depth within
/// the finalized or unfinalized chain.
#[derive(Debug, Clone, Encode, PartialEq)]
pub(crate) struct PendingChange<H, N> {
	/// The new authorities and weights to apply.
	pub(crate) next_authorities: Vec<(AuthorityId, u64)>,
	/// How deep in the chain the announcing block must be
	/// before the change is applied.
	pub(crate) delay: N,
	/// The announcing block's height.
	pub(crate) canon_height: N,
	/// The announcing block's hash.
	pub(crate) canon_hash: H,
	/// The delay kind.
	pub(crate) delay_kind: DelayKind<N>,
}

impl<H: Decode, N: Decode> Decode for PendingChange<H, N> {
	fn decode<I: parity_codec::Input>(value: &mut I) -> Option<Self> {
		let next_authorities = Decode::decode(value)?;
		let delay = Decode::decode(value)?;
		let canon_height = Decode::decode(value)?;
		let canon_hash = Decode::decode(value)?;

		let delay_kind = DelayKind::decode(value).unwrap_or(DelayKind::Finalized);

		Some(PendingChange {
			next_authorities,
			delay,
			canon_height,
			canon_hash,
			delay_kind,
		})
	}
}

impl<H, N: Add<Output=N> + Clone> PendingChange<H, N> {
	/// Returns the effective number this change will be applied at.
	pub fn effective_number(&self) -> N {
		self.canon_height.clone() + self.delay.clone()
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
			pending_standard_changes: ForkTree::new(),
			pending_forced_changes: Vec::new(),
		};

		let change_a = PendingChange {
			next_authorities: Vec::new(),
			delay: 10,
			canon_height: 5,
			canon_hash: "hash_a",
			delay_kind: DelayKind::Finalized,
		};

		let change_b = PendingChange {
			next_authorities: Vec::new(),
			delay: 0,
			canon_height: 5,
			canon_hash: "hash_b",
			delay_kind: DelayKind::Finalized,
		};

		let change_c = PendingChange {
			next_authorities: Vec::new(),
			delay: 5,
			canon_height: 10,
			canon_hash: "hash_c",
			delay_kind: DelayKind::Finalized,
		};

		authorities.add_pending_change(change_a.clone(), &static_is_descendent_of(false)).unwrap();
		authorities.add_pending_change(change_b.clone(), &static_is_descendent_of(false)).unwrap();
		authorities.add_pending_change(change_c.clone(), &is_descendent_of(|base, hash| match (*base, *hash) {
			("hash_a", "hash_c") => true,
			("hash_b", "hash_c") => false,
			_ => unreachable!(),
		})).unwrap();

		// forced changes are iterated last
		let change_d = PendingChange {
			next_authorities: Vec::new(),
			delay: 2,
			canon_height: 1,
			canon_hash: "hash_d",
			delay_kind: DelayKind::Best { median_last_finalized: 0 },
		};

		let change_e = PendingChange {
			next_authorities: Vec::new(),
			delay: 2,
			canon_height: 0,
			canon_hash: "hash_e",
			delay_kind: DelayKind::Best { median_last_finalized: 0 },
		};

		authorities.add_pending_change(change_d.clone(), &static_is_descendent_of(false)).unwrap();
		authorities.add_pending_change(change_e.clone(), &static_is_descendent_of(false)).unwrap();

		assert_eq!(
			authorities.pending_changes().collect::<Vec<_>>(),
			vec![&change_b, &change_a, &change_c, &change_e, &change_d],
		);
	}

	#[test]
	fn apply_change() {
		let mut authorities = AuthoritySet {
			current_authorities: Vec::new(),
			set_id: 0,
			pending_standard_changes: ForkTree::new(),
			pending_forced_changes: Vec::new(),
		};

		let set_a = vec![(AuthorityId([1; 32]), 5)];
		let set_b = vec![(AuthorityId([2; 32]), 5)];

		// two competing changes at the same height on different forks
		let change_a = PendingChange {
			next_authorities: set_a.clone(),
			delay: 10,
			canon_height: 5,
			canon_hash: "hash_a",
			delay_kind: DelayKind::Finalized,
		};

		let change_b = PendingChange {
			next_authorities: set_b.clone(),
			delay: 10,
			canon_height: 5,
			canon_hash: "hash_b",
			delay_kind: DelayKind::Finalized,
		};

		authorities.add_pending_change(change_a.clone(), &static_is_descendent_of(true)).unwrap();
		authorities.add_pending_change(change_b.clone(), &static_is_descendent_of(true)).unwrap();

		assert_eq!(
			authorities.pending_changes().collect::<Vec<_>>(),
			vec![&change_b, &change_a],
		);

		// finalizing "hash_c" won't enact the change signaled at "hash_a" but it will prune out "hash_b"
		let status = authorities.apply_standard_changes("hash_c", 11, &is_descendent_of(|base, hash| match (*base, *hash) {
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

		// finalizing "hash_d" will enact the change signaled at "hash_a"
		let status = authorities.apply_standard_changes("hash_d", 15, &is_descendent_of(|base, hash| match (*base, *hash) {
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
			pending_standard_changes: ForkTree::new(),
			pending_forced_changes: Vec::new(),
		};

		let set_a = vec![(AuthorityId([1; 32]), 5)];
		let set_c = vec![(AuthorityId([2; 32]), 5)];

		// two competing changes at the same height on different forks
		let change_a = PendingChange {
			next_authorities: set_a.clone(),
			delay: 10,
			canon_height: 5,
			canon_hash: "hash_a",
			delay_kind: DelayKind::Finalized,
		};

		let change_c = PendingChange {
			next_authorities: set_c.clone(),
			delay: 10,
			canon_height: 30,
			canon_hash: "hash_c",
			delay_kind: DelayKind::Finalized,
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
		match authorities.apply_standard_changes("hash_d", 40, &is_descendent_of) {
			Err(fork_tree::Error::UnfinalizedAncestor) => {},
			_ => unreachable!(),
		}

		let status = authorities.apply_standard_changes("hash_b", 15, &is_descendent_of).unwrap();
		assert!(status.changed);
		assert_eq!(status.new_set_block, Some(("hash_b", 15)));

		assert_eq!(authorities.current_authorities, set_a);
		assert_eq!(authorities.set_id, 1);

		// after finalizing `change_a` it should be possible to finalize `change_c`
		let status = authorities.apply_standard_changes("hash_d", 40, &is_descendent_of).unwrap();
		assert!(status.changed);
		assert_eq!(status.new_set_block, Some(("hash_d", 40)));

		assert_eq!(authorities.current_authorities, set_c);
		assert_eq!(authorities.set_id, 2);
	}

	#[test]
	fn enacts_standard_change_works() {
		let mut authorities = AuthoritySet {
			current_authorities: Vec::new(),
			set_id: 0,
			pending_standard_changes: ForkTree::new(),
			pending_forced_changes: Vec::new(),
		};

		let set_a = vec![(AuthorityId([1; 32]), 5)];

		let change_a = PendingChange {
			next_authorities: set_a.clone(),
			delay: 10,
			canon_height: 5,
			canon_hash: "hash_a",
			delay_kind: DelayKind::Finalized,
		};

		let change_b = PendingChange {
			next_authorities: set_a.clone(),
			delay: 10,
			canon_height: 20,
			canon_hash: "hash_b",
			delay_kind: DelayKind::Finalized,
		};

		authorities.add_pending_change(change_a.clone(), &static_is_descendent_of(false)).unwrap();
		authorities.add_pending_change(change_b.clone(), &static_is_descendent_of(true)).unwrap();

		let is_descendent_of = is_descendent_of(|base, hash| match (*base, *hash) {
			("hash_a", "hash_d") => true,
			("hash_a", "hash_e") => true,
			("hash_b", "hash_d") => true,
			("hash_b", "hash_e") => true,
			("hash_a", "hash_c") => false,
			("hash_b", "hash_c") => false,
			_ => unreachable!(),
		});

		// "hash_c" won't finalize the existing change since it isn't a descendent
		assert_eq!(
			authorities.enacts_standard_change("hash_c", 15, &is_descendent_of).unwrap(),
			None,
		);

		// "hash_d" at depth 14 won't work either
		assert_eq!(
			authorities.enacts_standard_change("hash_d", 14, &is_descendent_of).unwrap(),
			None,
		);

		// but it should work at depth 15 (change height + depth)
		assert_eq!(
			authorities.enacts_standard_change("hash_d", 15, &is_descendent_of).unwrap(),
			Some(true),
		);

		// finalizing "hash_e" at depth 20 will trigger change at "hash_b", but
		// it can't be applied yet since "hash_a" must be applied first
		assert_eq!(
			authorities.enacts_standard_change("hash_e", 30, &is_descendent_of).unwrap(),
			Some(false),
		);
	}

	#[test]
	fn forced_changes() {
		let mut authorities = AuthoritySet {
			current_authorities: Vec::new(),
			set_id: 0,
			pending_standard_changes: ForkTree::new(),
			pending_forced_changes: Vec::new(),
		};

		let set_a = vec![(AuthorityId([1; 32]), 5)];
		let set_b = vec![(AuthorityId([2; 32]), 5)];

		let change_a = PendingChange {
			next_authorities: set_a.clone(),
			delay: 10,
			canon_height: 5,
			canon_hash: "hash_a",
			delay_kind: DelayKind::Best { median_last_finalized: 42 },
		};

		let change_b = PendingChange {
			next_authorities: set_b.clone(),
			delay: 10,
			canon_height: 5,
			canon_hash: "hash_b",
			delay_kind: DelayKind::Best { median_last_finalized: 0 },
		};

		authorities.add_pending_change(change_a, &static_is_descendent_of(false)).unwrap();
		authorities.add_pending_change(change_b, &static_is_descendent_of(false)).unwrap();

		// there's an effective change triggered at block 15 but not a standard one.
		// so this should do nothing.
		assert_eq!(
			authorities.enacts_standard_change("hash_c", 15, &static_is_descendent_of(true)).unwrap(),
			None,
		);

		// throw a standard change into the mix to prove that it's discarded
		// for being on the same fork.
		//
		// NOTE: after https://github.com/paritytech/substrate/issues/1861
		// this should still be rejected based on the "span" rule -- it overlaps
		// with another change on the same fork.
		let change_c = PendingChange {
			next_authorities: set_b.clone(),
			delay: 3,
			canon_height: 8,
			canon_hash: "hash_a8",
			delay_kind: DelayKind::Best { median_last_finalized: 0 },
		};

		let is_descendent_of_a = is_descendent_of(|base: &&str, _| {
			base.starts_with("hash_a")
		});

		assert!(authorities.add_pending_change(change_c, &is_descendent_of_a).is_err());

		// too early.
		assert!(authorities.apply_forced_changes("hash_a10", 10, &static_is_descendent_of(true)).unwrap().is_none());

		// too late.
		assert!(authorities.apply_forced_changes("hash_a16", 16, &static_is_descendent_of(true)).unwrap().is_none());

		// on time -- chooses the right change.
		assert_eq!(
			authorities.apply_forced_changes("hash_a15", 15, &is_descendent_of_a).unwrap().unwrap(),
			(42, AuthoritySet {
				current_authorities: set_a,
				set_id: 1,
				pending_standard_changes: ForkTree::new(),
				pending_forced_changes: Vec::new(),
			})
		);
	}
}
