// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Conrete externalities implementation.

use std::{error, fmt};
use triehash::trie_root;
use backend::Backend;
use {Externalities, ExternalitiesError, OverlayedChanges};

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
pub struct Ext<'a, B: 'a> {
	/// The overlayed changes to write to.
	pub overlay: &'a mut OverlayedChanges,
	/// The storage backend to read from.
	pub backend: &'a B,
}

impl<'a, B: 'a> Externalities for Ext<'a, B>
	where B: Backend
{
	fn storage(&self, key: &[u8]) -> Result<&[u8], ExternalitiesError> {
		match self.overlay.storage(key) {
			Some(x) => Ok(x),
			None => self.backend.storage(key).map_err(|_| ExternalitiesError),
		}
	}

	fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
		self.overlay.set_storage(key, value);
	}

	fn chain_id(&self) -> u64 {
		42
	}

	fn storage_root(&self) -> [u8; 32] {
		let mut all_pairs = self.backend.pairs();
		all_pairs.extend(
			self.overlay.committed.storage.iter()
				.chain(self.overlay.prospective.storage.iter())
				.map(|(k, v)| (&k[..], &v[..]))
		);

		trie_root(all_pairs.into_iter().map(|(k, v)| (k.to_vec(), v.to_vec()))).0
	}
}
