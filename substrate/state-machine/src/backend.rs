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

//! State machine backends. These manage the code and storage of contracts.

use std::{error, fmt};
use std::collections::HashMap;
use std::sync::Arc;
use trie_backend::{TryIntoTrieBackend, TrieBackend};

/// A state backend is used to read state data and can have changes committed
/// to it.
///
/// The clone operation should be cheap.
pub trait Backend: TryIntoTrieBackend + Clone {
	/// An error type when fetching data is not possible.
	type Error: super::Error;

	/// Changes to be applied if committing
	type Transaction;

	/// Get keyed storage associated with specific address, or None if there is nothing associated.
	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error>;

	/// Calculate the storage root, with given delta over what is already stored in
	/// the backend, and produce a "transaction" that can be used to commit.
	fn storage_root<I>(&self, delta: I) -> ([u8; 32], Self::Transaction)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>;

	/// Get all key/value pairs into a Vec.
	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)>;
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
#[derive(Clone, PartialEq, Eq)]
pub struct InMemory {
	inner: Arc<HashMap<Vec<u8>, Vec<u8>>>,
}

impl Default for InMemory {
	fn default() -> Self {
		InMemory {
			inner: Arc::new(Default::default()),
		}
	}
}

impl InMemory {
	/// Copy the state, with applied updates
	pub fn update(&self, changes: <Self as Backend>::Transaction) -> Self {
		let mut inner: HashMap<_, _> = (&*self.inner).clone();
		for (key, val) in changes {
			match val {
				Some(v) => { inner.insert(key, v); },
				None => { inner.remove(&key); },
			}
		}

		inner.into()
	}
}

impl From<HashMap<Vec<u8>, Vec<u8>>> for InMemory {
	fn from(inner: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		InMemory {
			inner: Arc::new(inner),
		}
	}
}

impl Backend for InMemory {
	type Error = Void;
	type Transaction = Vec<(Vec<u8>, Option<Vec<u8>>)>;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		Ok(self.inner.get(key).map(Clone::clone))
	}

	fn storage_root<I>(&self, delta: I) -> ([u8; 32], Self::Transaction)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		let existing_pairs = self.inner.iter().map(|(k, v)| (k.clone(), Some(v.clone())));

		let transaction: Vec<_> = delta.into_iter().collect();
		let root = ::triehash::trie_root(existing_pairs.chain(transaction.iter().cloned())
			.collect::<HashMap<_, _>>()
			.into_iter()
			.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
		).0;

		(root, transaction)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.inner.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
	}
}

impl TryIntoTrieBackend for InMemory {
	fn try_into_trie_backend(self) -> Option<TrieBackend> {
		use ethereum_types::H256 as TrieH256;
		use memorydb::MemoryDB;
		use patricia_trie::{TrieDBMut, TrieMut};

		let mut root = TrieH256::default();
		let mut mdb = MemoryDB::default();
		{
			let mut trie = TrieDBMut::new(&mut mdb, &mut root);
			for (key, value) in self.inner.iter() {
				if let Err(e) = trie.insert(&key, &value) {
					warn!(target: "trie", "Failed to write to trie: {}", e);
					return None;
				}
			}
		}

		Some(TrieBackend::with_memorydb(mdb, root))
	}
}
