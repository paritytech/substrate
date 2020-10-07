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

/// A wrapper around `kvdb::Database` that implements `sp_database::Database` trait

use ::kvdb::{DBTransaction, KeyValueDB};

use crate::{Database, Change, ColumnId, Transaction, error};

struct DbAdapter<D: KeyValueDB + 'static>(D);

fn handle_err<T>(result: std::io::Result<T>) -> T {
	match result {
		Ok(r) => r,
		Err(e) =>  {
			panic!("Critical database eror: {:?}", e);
		}
	}
}

/// Wrap RocksDb database into a trait object that implements `sp_database::Database`
pub fn as_database<D: KeyValueDB + 'static, H: Clone>(db: D) -> std::sync::Arc<dyn Database<H>> {
	std::sync::Arc::new(DbAdapter(db))
}

/// Wrap RocksDb database into a trait object that implements `sp_database::Database`
pub fn arc_as_database<D: KeyValueDB + 'static, H: Clone>(db: std::sync::Arc<D>) -> std::sync::Arc<dyn Database<H>> {
	std::sync::Arc::new(DbAdapter(WrapArc(db)))
}

struct WrapArc<D: KeyValueDB>(std::sync::Arc<D>);

impl<D: KeyValueDB> parity_util_mem::MallocSizeOf for WrapArc<D> {
	fn size_of(&self, ops: &mut parity_util_mem::MallocSizeOfOps) -> usize {
		<D as parity_util_mem::MallocSizeOf>::size_of(&self.0, ops)
	}
}

impl<D: KeyValueDB> KeyValueDB for WrapArc<D> {
	fn transaction(&self) -> DBTransaction {
		<D as KeyValueDB>::transaction(&self.0)
	}

	fn get(&self, col: u32, key: &[u8]) -> std::io::Result<Option<Vec<u8>>> {
		<D as KeyValueDB>::get(&self.0, col, key)
	}

	fn get_by_prefix(&self, col: u32, prefix: &[u8]) -> Option<Box<[u8]>> {
		<D as KeyValueDB>::get_by_prefix(&self.0, col, prefix)
	}

	fn write(&self, transaction: DBTransaction) -> std::io::Result<()> {
		<D as KeyValueDB>::write(&self.0, transaction)
	}

	fn iter<'a>(&'a self, col: u32) -> Box<dyn Iterator<Item = (Box<[u8]>, Box<[u8]>)> + 'a> {
		<D as KeyValueDB>::iter(&self.0, col)
	}

	fn iter_with_prefix<'a>(
		&'a self,
		col: u32,
		prefix: &'a [u8],
	) -> Box<dyn Iterator<Item = (Box<[u8]>, Box<[u8]>)> + 'a> {
		<D as KeyValueDB>::iter_with_prefix(&self.0, col, prefix)
	}

	fn restore(&self, new_db: &str) -> std::io::Result<()> {
		<D as KeyValueDB>::restore(&self.0, new_db)
	}
}

impl<D: KeyValueDB, H: Clone> Database<H> for DbAdapter<D> {
	fn commit(&self, transaction: Transaction<H>) -> error::Result<()> {
		let mut tx = DBTransaction::new();
		for change in transaction.0.into_iter() {
			match change {
				Change::Set(col, key, value) => tx.put_vec(col, &key, value),
				Change::Remove(col, key) => tx.delete(col, &key),
				_ => unimplemented!(),
			}
		}
		self.0.write(tx).map_err(|e| error::DatabaseError(Box::new(e)))
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		handle_err(self.0.get(col, key))
	}

	fn lookup(&self, _hash: &H) -> Option<Vec<u8>> {
		unimplemented!();
	}
}
