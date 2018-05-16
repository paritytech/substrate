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

/// A state backend is used to read state data and can have changes committed
/// to it.
pub trait Backend {
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

	/// Commit updates to the backend and get new state.
	fn commit(&mut self, tx: Self::Transaction);

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
pub type InMemory = HashMap<Vec<u8>, Vec<u8>>;

impl Backend for InMemory {
	type Error = Void;
	type Transaction = Vec<(Vec<u8>, Option<Vec<u8>>)>;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		Ok(self.get(key).map(Clone::clone))
	}

	fn storage_root<I>(&self, delta: I) -> ([u8; 32], Self::Transaction)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		let existing_pairs = self.iter().map(|(k, v)| (k.clone(), Some(v.clone())));

		let transaction: Vec<_> = delta.into_iter().collect();
		let root = ::triehash::trie_root(existing_pairs.chain(transaction.iter().cloned())
			.collect::<HashMap<_, _>>()
			.into_iter()
			.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
		).0;

		(root, transaction)
	}

	fn commit(&mut self, changes: Self::Transaction) {
		for (key, val) in changes {
			match val {
				Some(v) => { self.insert(key, v); },
				None => { self.remove(&key); },
			}
		}
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
	}
}

