// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! In-memory implementation of `Database`

use std::collections::HashMap;
use crate::{Database, Change, ColumnId, Transaction, error};
use parking_lot::RwLock;

#[derive(Default)]
/// This implements `Database` as an in-memory hash map. `commit` is not atomic.
pub struct MemDb<H: Clone + Send + Sync + Eq + PartialEq + Default + std::hash::Hash>
	(RwLock<(HashMap<ColumnId, HashMap<Vec<u8>, Vec<u8>>>, HashMap<H, Vec<u8>>)>);

impl<H> Database<H> for MemDb<H>
	where H: Clone + Send + Sync + Eq + PartialEq + Default + std::hash::Hash
{
	fn commit(&self, transaction: Transaction<H>) -> error::Result<()> {
		let mut s = self.0.write();
		for change in transaction.0.into_iter() {
			match change {
				Change::Set(col, key, value) => { s.0.entry(col).or_default().insert(key, value); },
				Change::Remove(col, key) => { s.0.entry(col).or_default().remove(&key); },
				Change::Store(hash, preimage) => { s.1.insert(hash, preimage); },
				Change::Release(hash) => { s.1.remove(&hash); },
			}
		}

		Ok(())
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

