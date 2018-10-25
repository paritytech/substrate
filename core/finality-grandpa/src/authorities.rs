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

impl<H, N: Add<Output=N> + Ord + Clone> SharedAuthoritySet<H, N> {
	/// Note an upcoming pending transition.
	pub(crate) fn add_pending_change(&self, pending: PendingChange<H, N>) {
		let mut inner = self.inner.write();
		let idx = inner.pending_changes
			.binary_search_by_key(&pending.effective_number(), |change| change.effective_number())
			.unwrap_or_else(|i| i);

		inner.pending_changes.insert(idx, pending);
	}

	/// Get the earliest limit-block number, if any.
	pub(crate) fn current_limit(&self) -> Option<N> {
		self.inner.read().pending_changes.get(0).map(|change| change.effective_number().clone())
	}
}

impl<H, N> From<AuthoritySet<H, N>> for SharedAuthoritySet<H, N> {
	fn from(set: AuthoritySet<H, N>) -> Self {
		SharedAuthoritySet { inner: Arc::new(RwLock::new(set)) }
	}
}

/// A set of authorities.
#[derive(Encode, Decode)]
pub(crate) struct AuthoritySet<H, N> {
	current_authorities: Vec<(AuthorityId, u64)>,
	set_id: u64,
	pending_changes: Vec<PendingChange<H, N>>,
}

/// A pending change to the authority set.
///
/// This will be applied when the announcing block is at some depth within
/// the finalized chain.
#[derive(Encode, Decode)]
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
	/// Returns the effective number.
	fn effective_number(&self) -> N {
		self.canon_height.clone() + self.finalization_depth.clone()
	}
}
