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

use std::fmt;

use primitives::Address;
use primitives::hash::H256;
use triehash::sec_trie_root;

use super::{Update, MemoryState};

/// Output of a commit.
pub struct Committed {
	/// Root of the code tree after changes committed.
	pub code_tree_root: H256,
	/// Root of the storage tree after changes committed.
	pub storage_tree_root: H256,
}

/// A state backend is used to read state data and can have changes committed
/// to it.
pub trait Backend {
	/// An error type when fetching data is not possible.
	type Error: super::Error;

	/// Get code associated with specific address.
	fn code(&self, address: &Address) -> Result<&[u8], Self::Error>;

	/// Get keyed storage associated with specific address.
	fn storage(&self, address: &Address, key: &H256) -> Result<&[u8], Self::Error>;

	/// Commit updates to the backend and get new state.
	fn commit<I>(&mut self, changes: I) -> Committed
		where I: IntoIterator<Item=Update>;
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

/// In-memory backend. Fully recomputes tries on each commit but useful for
/// tests.
#[derive(Default)]
pub struct InMemory {
	inner: MemoryState, // keeps all the state in memory.
}

impl Backend for InMemory {
	type Error = Void;

	fn code(&self, address: &Address) -> Result<&[u8], Void> {
		Ok(self.inner.code(address).unwrap_or(&[]))
	}

	fn storage(&self, address: &Address, key: &H256) -> Result<&[u8], Void> {
		Ok(self.inner.storage(address, key).unwrap_or(&[]))
	}

	fn commit<I>(&mut self, changes: I) -> Committed
		where I: IntoIterator<Item=Update>
	{
		self.inner.update(changes);

		// fully recalculate trie roots.

		let storage_roots = self.inner.storage.iter().map(|(addr, storage)| {
			let flat_trie = storage.iter().map(|(k, v)| (k.to_vec(), v.clone())).collect();
			(addr.to_vec(), sec_trie_root(flat_trie).to_vec())
		}).collect();

		let storage_tree_root = H256(sec_trie_root(storage_roots).0);

		let code_tree_root = sec_trie_root(
			self.inner.code.iter().map(|(k, v)| (k.to_vec(), v.clone())).collect()
		);

		let code_tree_root = H256(code_tree_root.0);

		Committed {
			code_tree_root,
			storage_tree_root,
		}
	}
}

// TODO: DB-based backend
