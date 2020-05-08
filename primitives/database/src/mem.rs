// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! In-memory implementation of `Database`

use std::collections::HashMap;
use crate::{Database, Transaction, ColumnId, Change};
use parking_lot::RwLock;

#[derive(Default)]
/// This implements `Database` as an in-memory hash map. `commit` is not atomic.
pub struct MemDb<H: Clone + Send + Sync + Eq + PartialEq + Default + std::hash::Hash>
	(RwLock<(HashMap<ColumnId, HashMap<Vec<u8>, Vec<u8>>>, HashMap<H, Vec<u8>>)>);

impl<H> Database<H> for MemDb<H>
	where H: Clone + Send + Sync + Eq + PartialEq + Default + std::hash::Hash
{
	fn commit(&self, transaction: Transaction<H>) {
		let mut s = self.0.write();
		for change in transaction.0.into_iter() {
			match change {
				Change::Set(col, key, value) => { s.0.entry(col).or_default().insert(key, value); },
				Change::Remove(col, key) => { s.0.entry(col).or_default().remove(&key); },
				Change::Store(hash, preimage) => { s.1.insert(hash, preimage); },
				Change::Release(hash) => { s.1.remove(&hash); },
			}
		}
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		let s = self.0.read();
		s.0.get(&col).and_then(|c| c.get(key).cloned())
	}

	fn lookup(&self, hash: &H) -> Option<Vec<u8>> {
		let s = self.0.read();
		s.1.get(hash).cloned()
	}
}

impl<H> MemDb<H>
	where H: Clone + Send + Sync + Eq + PartialEq + Default + std::hash::Hash
{
	/// Create a new instance
	pub fn new() -> Self {
		MemDb::default()
	}

	/// Count number of values in a column
	pub fn count(&self, col: ColumnId) -> usize {
		let s = self.0.read();
		s.0.get(&col).map(|c| c.len()).unwrap_or(0)
	}
}

