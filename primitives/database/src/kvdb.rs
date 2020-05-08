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

/// A wrapper around `kvdb::Database` that implements `sp_database::Database` trait

use ::kvdb::{DBTransaction, KeyValueDB};

use crate::{Database, Change, Transaction, ColumnId};

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
	fn commit(&self, transaction: Transaction<H>) {
		let mut tx = DBTransaction::new();
		for change in transaction.0.into_iter() {
			match change {
				Change::Set(col, key, value) => tx.put_vec(col, &key, value),
				Change::Remove(col, key) => tx.delete(col, &key),
				_ => unimplemented!(),
			}
		}
		handle_err(self.0.write(tx));
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		handle_err(self.0.get(col, key))
	}

	fn lookup(&self, _hash: &H) -> Option<Vec<u8>> {
		unimplemented!();
	}
}
