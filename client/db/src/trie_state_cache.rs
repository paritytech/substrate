// This file is part of Substrate.

// Copyright (C) 2021-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Cache over trie node collection.
//! This cache is limited to insertion and
//! its usage is only for trie state where
//! deletion is done through journaling.


use parking_lot::RwLock;
use std::sync::Arc;
use std::collections::BTreeSet;
use std::marker::PhantomData;
use sp_database::{Database, ColumnId, Transaction, error, Change};
use crate::storage_cache::LRUMap;

/// Simple lru cache.
#[derive(Clone)]
pub struct DatabaseCache<H: Clone + AsRef<[u8]>, DB: Database<H>> {
	has_lru: BTreeSet<ColumnId>,
	// Note that design really only work for trie node (we do not cache
	// deletion) TODO consider just a single column
	lru: Option<Arc<RwLock<Vec<Option<LRUMap<Vec<u8>, Vec<u8>>>>>>>,
	db: DB,
	_ph: PhantomData<H>,
}

impl<H: Clone + AsRef<[u8]>, DB: Database<H>> DatabaseCache<H, DB> {
	/// New db with unconfigured cache.
	pub fn new(db: DB) -> Self {
		DatabaseCache {
			has_lru: Default::default(),
			lru: None,
			db,
			_ph: PhantomData,
		}
	}

	/// define cache for a given column.
	pub fn configure_cache(&mut self, column: ColumnId, size: Option<usize>) {
		if size.is_some() {
			self.has_lru.insert(column);
		} else {
			self.has_lru.remove(&column);
		}
		let new_cache = size.map(|size| LRUMap::new(size));
		if self.lru.is_none() {
			if new_cache.is_none() {
				return;
			}
			let mut caches = Vec::with_capacity(column as usize + 1);
			while caches.len() < column as usize + 1 {
				caches.push(None);
			}
			caches[column as usize] = new_cache;
			self.lru = Some(Arc::new(RwLock::new(Vec::new())));
		} else {
			self.lru.as_ref().map(|lru| {
				let mut lru = lru.write();
				while lru.len() < column as usize + 1 {
					lru.push(None);
				}
				lru[column as usize] = new_cache;
			});
		}
	}

	fn add_val(&self, col: ColumnId, key: &[u8], value: &Vec<u8>) {
		if let Some(lru) = self.lru.as_ref()  {
			let mut lru = lru.write();
			if let Some(Some(lru)) = lru.get_mut(col as usize) {
				lru.add(key.to_vec(), value.clone());
			}
		}
	}

	fn add_val_slice(&self, col: ColumnId, key: &[u8], value: &[u8]) {
		if let Some(lru) = self.lru.as_ref()  {
			let mut lru = lru.write();
			if let Some(Some(lru)) = lru.get_mut(col as usize) {
				lru.add(key.to_vec(), value.to_vec());
			}
		}
	}
}

impl<H, DB> Database<H> for DatabaseCache<H, DB>
	where H: Clone + AsRef<[u8]>, DB: Database<H>,
{
	fn commit(&self, transaction: Transaction<H>) -> error::Result<()> {
		let cache_update: Vec<_> = if self.lru.is_some() {
			transaction.0.iter().filter_map(|change| {
				if let Change::Set(col, key, value) = change {
					self.has_lru.contains(col).then(|| (*col, key.clone(), value.clone()))
				} else {
					None
				}
			}).collect()
		} else {
			Vec::new()
		};
		self.db.commit(transaction)?;

		if let Some(lru) = self.lru.as_ref()  {
			let mut lru = lru.write();
			for (col, key, value) in cache_update {
				if let Some(Some(lru)) = lru.get_mut(col as usize) {
					lru.add(key, value);
				}
			}
		}

		Ok(())
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		if let Some(lru) = self.lru.as_ref()  {
			let mut lru = lru.write();
			if let Some(Some(lru)) = lru.get_mut(col as usize) {
				if let Some(node) = lru.get(key) {
					return Some(node.clone());
				}
			}
		}

		self.db.get(col, key)
			.map(|value| { self.add_val(col, key, &value); value })
	}

	fn contains(&self, col: ColumnId, key: &[u8]) -> bool {
		if let Some(lru) = self.lru.as_ref()  {
			let mut lru = lru.write();
			if let Some(Some(lru)) = lru.get_mut(col as usize) {
				if lru.get(key).is_some() {
					return true;
				}
			}
		}

		self.db.get(col, key)
			.map(|value| { self.add_val(col, key, &value); () })
			.is_some()
	}

	fn value_size(&self, col: ColumnId, key: &[u8]) -> Option<usize> {
		if let Some(lru) = self.lru.as_ref()  {
			let mut lru = lru.write();
			if let Some(Some(lru)) = lru.get_mut(col as usize) {
				if let Some(node) = lru.get(key) {
					return Some(node.len());
				}
			}
		}

		self.db.get(col, key)
			.map(|value| { self.add_val(col, key, &value); value.len() })
	}

	fn with_get(&self, col: ColumnId, key: &[u8], f: &mut dyn FnMut(&[u8])) {
		if let Some(lru) = self.lru.as_ref()  {
			let mut lru = lru.write();
			if let Some(Some(lru)) = lru.get_mut(col as usize) {
				if let Some(node) = lru.get(key) {
					return f(node);
				}
			}
		}

		self.db.with_get(col, key, &mut |value| {
			self.add_val_slice(col, key, value);
			f(value)
		})
	}

	fn supports_ref_counting(&self) -> bool {
		self.db.supports_ref_counting()
	}
}

unsafe impl<H: Clone + AsRef<[u8]>, DB: Database<H>> Sync for DatabaseCache<H, DB> { }
unsafe impl<H: Clone + AsRef<[u8]>, DB: Database<H>> Send for DatabaseCache<H, DB> { }
