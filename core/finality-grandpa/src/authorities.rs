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
use substrate_primitives::AuthorityId;

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

impl<H, N> SharedAuthoritySet<H, N> {
	/// The genesis authority set.
	pub(crate) fn genesis(initial: Vec<(AuthorityId, u64)>) -> Self {
		SharedAuthoritySet {
			inner: Arc::new(RwLock::new(AuthoritySet {
				current_authorities: initial,
				set_id: 0,
				pending_changes: Vec::new(),
			}))
		}
	}

	/// Execute some work using the inner authority set.
	pub(crate) fn with<F, U>(&self, f: F) -> U
		where F: FnOnce(&AuthoritySet<H, N>) -> U
	{
		f(&*self.inner.read())
	}
}

impl<H: Eq, N> SharedAuthoritySet<H, N>
	where N: Add<Output=N> + Ord + Clone + Debug
{
	/// Note an upcoming pending transition.
	pub(crate) fn add_pending_change(&self, pending: PendingChange<H, N>) {
		// ordered first by effective number and then by signal-block number.
		let mut inner = self.inner.write();
		let key = (pending.effective_number(), pending.canon_height.clone());
		let idx = inner.pending_changes
			.binary_search_by_key(&key, |change| (
				change.effective_number(),
				change.canon_height.clone(),
			))
			.unwrap_or_else(|i| i);

		inner.pending_changes.insert(idx, pending);
	}

	/// Get the earliest limit-block number, if any.
	pub(crate) fn current_limit(&self) -> Option<N> {
		self.inner.read().current_limit()
	}

	/// Get the current set ID. This is incremented every time the set changes.
	pub(crate) fn set_id(&self) -> u64 {
		self.inner.read().set_id
	}

	/// Execute a closure with the inner set mutably.
	pub(crate) fn with_mut<F, U>(&self, f: F) -> U where F: FnOnce(&mut AuthoritySet<H, N>) -> U {
		f(&mut *self.inner.write())
	}
}

impl<H, N> From<AuthoritySet<H, N>> for SharedAuthoritySet<H, N> {
	fn from(set: AuthoritySet<H, N>) -> Self {
		SharedAuthoritySet { inner: Arc::new(RwLock::new(set)) }
	}
}

/// A set of authorities.
#[derive(Debug, Clone, Encode, Decode)]
pub(crate) struct AuthoritySet<H, N> {
	current_authorities: Vec<(AuthorityId, u64)>,
	set_id: u64,
	pending_changes: Vec<PendingChange<H, N>>,
}

impl<H, N> AuthoritySet<H, N> {
	/// Get the set identifier.
	pub(crate) fn set_id(&self) -> u64 {
		self.set_id
	}

	/// Get the current set id and a reference to the current authority set.
	pub(crate) fn current(&self) -> (u64, &[(AuthorityId, u64)]) {
		(self.set_id, &self.current_authorities[..])
	}
}

impl<H: Eq, N> AuthoritySet<H, N>
	where N: Add<Output=N> + Ord + Clone + Debug,
{
	/// Get the earliest limit-block number, if any.
	pub(crate) fn current_limit(&self) -> Option<N> {
		self.pending_changes.get(0).map(|change| change.effective_number().clone())
	}

	/// Apply or prune any pending transitions. Provide a closure that can be used to check for the
	/// finalized block with given number.
	///
	/// Returns true when the set's representation has changed.
	pub(crate) fn apply_changes<F, E>(&mut self, just_finalized: N, mut canonical: F)
		-> Result<bool, E>
		where F: FnMut(N) -> Result<H, E>
	{
		let mut changed = false;
		loop {
			let remove_up_to = match self.pending_changes.first() {
				None => break,
				Some(change) => {
					let effective_number = change.effective_number();
					if effective_number > just_finalized { break }

					// check if the block that signalled the change is canonical in
					// our chain.
					if canonical(change.canon_height.clone())? == change.canon_hash {
						// apply this change: make the set canonical
						info!(target: "finality", "Applying authority set change scheduled at block #{:?}",
							change.canon_height);

						self.current_authorities = change.next_authorities.clone();
						self.set_id += 1;

						// discard any signalled changes
						// that happened before or equal to the effective number of the change.
						self.pending_changes.iter()
							.take_while(|c| c.canon_height <= effective_number)
							.count()
					} else {
						1 // prune out this entry; it's no longer relevant.
					}
				}
			};

			let remove_up_to = ::std::cmp::min(remove_up_to, self.pending_changes.len());
			self.pending_changes.drain(..remove_up_to);
			changed = true; // always changed because we strip at least the first change.
		}

		Ok(changed)
	}
}

/// A pending change to the authority set.
///
/// This will be applied when the announcing block is at some depth within
/// the finalized chain.
#[derive(Debug, Clone, Encode, Decode)]
pub(crate) struct PendingChange<H, N> {
	/// The new authorities and weights to apply.
	pub(crate) next_authorities: Vec<(AuthorityId, u64)>,
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
	fn effective_number(&self) -> N {
		self.canon_height.clone() + self.finalization_depth.clone()
	}
}
