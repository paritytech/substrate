// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Conrete externalities implementation.

use std::{error, fmt};
use backend::Backend;
use {Externalities, OverlayedChanges};

/// Errors that can occur when interacting with the externalities.
#[derive(Debug, Copy, Clone)]
pub enum Error<B, E> {
	/// Failure to load state data from the backend.
	#[allow(unused)]
	Backend(B),
	/// Failure to execute a function.
	#[allow(unused)]
	Executor(E),
}

impl<B: fmt::Display, E: fmt::Display> fmt::Display for Error<B, E> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Error::Backend(ref e) => write!(f, "Storage backend error: {}", e),
			Error::Executor(ref e) => write!(f, "Sub-call execution error: {}", e),
		}
	}
}

impl<B: error::Error, E: error::Error> error::Error for Error<B, E> {
	fn description(&self) -> &str {
		match *self {
			Error::Backend(..) => "backend error",
			Error::Executor(..) => "executor error",
		}
	}
}

/// Wraps a read-only backend, call executor, and current overlayed changes.
pub struct Ext<'a, B: 'a + Backend> {
	// The overlayed changes to write to.
	overlay: &'a mut OverlayedChanges,
	// The storage backend to read from.
	backend: &'a B,
	// The transaction necessary to commit to the backend.
	transaction: Option<(B::Transaction, [u8; 32])>,
}

impl<'a, B: 'a + Backend> Ext<'a, B> {
	/// Create a new `Ext` from overlayed changes and read-only backend
	pub fn new(overlay: &'a mut OverlayedChanges, backend: &'a B) -> Self {
		Ext {
			overlay,
			backend,
			transaction: None,
		}
	}

	/// Get the transaction necessary to update the backend.
	pub fn transaction(mut self) -> B::Transaction {
		let _ = self.storage_root();
		self.transaction.expect("transaction always set after calling storage root; qed").0
	}

	/// Invalidates the currently cached storage root and the db transaction.
	///
	/// Called when there are changes that likely will invalidate the storage root.
	fn mark_dirty(&mut self) {
		self.transaction = None;
	}
}

#[cfg(test)]
impl<'a, B: 'a + Backend> Ext<'a, B> {
	pub fn storage_pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		use std::collections::HashMap;

		self.backend.pairs().iter()
			.map(|&(ref k, ref v)| (k.to_vec(), Some(v.to_vec())))
			.chain(self.overlay.committed.clone().into_iter())
			.chain(self.overlay.prospective.clone().into_iter())
			.collect::<HashMap<_, _>>()
			.into_iter()
			.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
			.collect()
	}
}

impl<'a, B: 'a> Externalities for Ext<'a, B>
	where B: Backend
{
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.overlay.storage(key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.backend.storage(key).expect("Externalities not allowed to fail within runtime"))
	}

	fn exists_storage(&self, key: &[u8]) -> bool {
		match self.overlay.storage(key) {
			Some(x) => x.is_some(),
			_ => self.backend.exists_storage(key).expect("Externalities not allowed to fail within runtime"),
		}
	}

	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>) {
		self.mark_dirty();
		self.overlay.set_storage(key, value);
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		self.mark_dirty();
		self.overlay.clear_prefix(prefix);
		self.backend.for_keys_with_prefix(prefix, |key| {
			self.overlay.set_storage(key.to_vec(), None);
		});
	}

	fn chain_id(&self) -> u64 {
		42
	}

	fn storage_root(&mut self) -> [u8; 32] {
		if let Some((_, ref root)) =  self.transaction {
			return root.clone();
		}

		// compute and memoize
		let delta = self.overlay.committed.iter()
			.chain(self.overlay.prospective.iter())
			.map(|(k, v)| (k.clone(), v.clone()));

		let (root, transaction) = self.backend.storage_root(delta);
		self.transaction = Some((transaction, root));
		root
	}
}
