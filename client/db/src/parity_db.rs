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

/// A `Database` adapter for parity-db.

use sp_database::{Database, Change, Transaction, ColumnId};
use crate::utils::NUM_COLUMNS;
use crate::columns;

struct DbAdapter(parity_db::Db);

fn handle_err<T>(result: parity_db::Result<T>) -> T {
	match result {
		Ok(r) => r,
		Err(e) =>  {
			panic!("Critical database eror: {:?}", e);
		}
	}
}

/// Wrap RocksDb database into a trait object that implements `sp_database::Database`
pub fn open<H: Clone>(path: &std::path::Path) -> parity_db::Result<std::sync::Arc<dyn Database<H>>> {
	let mut config = parity_db::Options::with_columns(path, NUM_COLUMNS as u8);
	let mut state_col = &mut config.columns[columns::STATE as usize];
	state_col.ref_counted = true;
	state_col.preimage = true;
	state_col.uniform = true;
	let db = parity_db::Db::open(&config)?;
	Ok(std::sync::Arc::new(DbAdapter(db)))
}

impl<H: Clone> Database<H> for DbAdapter {
	fn commit(&self, transaction: Transaction<H>) {
		handle_err(self.0.commit(transaction.0.into_iter().map(|change|
			match change {
				Change::Set(col, key, value) => (col as u8, key, Some(value)),
				Change::Remove(col, key) => (col as u8, key, None),
				_ => unimplemented!(),
			}))
		);
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		handle_err(self.0.get(col as u8, key))
	}

	fn lookup(&self, _hash: &H) -> Option<Vec<u8>> {
		unimplemented!();
	}
}
