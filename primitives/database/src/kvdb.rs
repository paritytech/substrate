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
