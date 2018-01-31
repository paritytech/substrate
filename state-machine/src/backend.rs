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

//! State machine backends. These manage the code and storage of contracts.

use std::{error, fmt};
use primitives::hash::H256;
use triehash::sec_trie_root;

use super::{Update, MemoryState};

/// Output of a commit.
pub struct Committed {
	/// Root of the storage tree after changes committed.
	pub storage_tree_root: H256,
}

/// A state backend is used to read state data and can have changes committed
/// to it.
pub trait Backend {
	/// An error type when fetching data is not possible.
	type Error: super::Error;

	/// Get keyed storage associated with specific address.
	fn storage(&self, key: &[u8]) -> Result<&[u8], Self::Error>;

	/// Commit updates to the backend and get new state.
	fn commit<I>(&mut self, changes: I) -> Committed
		where I: IntoIterator<Item=Update>;

	/// Get all key/value pairs into a Vec.
	fn pairs(&self) -> Vec<(&[u8], &[u8])>;
}

/// Error impossible.
// TODO: use `!` type when stabilized.
#[derive(Debug)]
pub enum Void {}

impl fmt::Display for Void {
	fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
		match *self {}
	}
}

impl error::Error for Void {
	fn description(&self) -> &str { "unreachable error" }
}

/// In-memory backend. Fully recomputes tries on each commit but useful for
/// tests.
#[derive(Default, Clone)]
pub struct InMemory {
	inner: MemoryState, // keeps all the state in memory.
}

#[cfg(test)]
impl InMemory {
	/// Create a new instance from a given storage map.
	pub fn from(storage: ::std::collections::HashMap<Vec<u8>, Vec<u8>>) -> Self {
		InMemory {
			inner: MemoryState {
				storage
			}
		}
	}
}

impl Backend for InMemory {
	type Error = Void;

	fn storage(&self, key: &[u8]) -> Result<&[u8], Self::Error> {
		Ok(self.inner.storage(key).unwrap_or(&[]))
	}

	fn commit<I>(&mut self, changes: I) -> Committed
		where I: IntoIterator<Item=Update>
	{
		self.inner.update(changes);

		// fully recalculate trie roots.
		let storage_tree_root = H256(sec_trie_root(
			self.inner.storage.iter()
				.map(|(k, v)| (k.to_vec(), v.clone()))
				.collect()
			).0);

		Committed {
			storage_tree_root,
		}
	}

	fn pairs(&self) -> Vec<(&[u8], &[u8])> {
		self.inner.storage.iter().map(|(k, v)| (&k[..], &v[..])).collect()
	}
}

// TODO: DB-based backend
