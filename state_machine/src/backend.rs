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
	/// Get code associated with specific address.
	fn code(&self, address: &Address) -> Option<&[u8]>;

	/// Get keyed storage associated with specific address.
	fn storage(&self, address: &Address, key: &H256) -> Option<&[u8]>;

	/// Commit updates.
	fn commit<I>(&mut self, changes: I) -> Committed
		where I: IntoIterator<Item=Update>;
}

/// In-memory backend. Fully recomputes tries on each commit but useful for
/// tests.
pub struct InMemory {
	inner: super::MemoryState, // keeps all the state in memory.
}

impl Backend for InMemory {
	fn code(&self, address: &Address) -> Option<&[u8]> {
		self.inner.code(address)
	}

	fn storage(&self, address: &Address, key: &H256) -> Option<&[u8]> {
		self.inner.storage(address, key)
	}

	fn commit<I>(&mut self, changes: I) -> Committed
		where I: IntoIterator<Item=Update>
	{
		self.inner.update(changes);

		// TODO: recalculate trie roots.
		unimplemented!()
	}
}
