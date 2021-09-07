// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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
use crate::{
	columns, light,
	utils::{DatabaseType, NUM_COLUMNS},
};
/// A `Database` adapter for parity-db.
use sp_database::{error::DatabaseError, Change, ColumnId, Database, Transaction};

struct DbAdapter(parity_db::Db);

fn handle_err<T>(result: parity_db::Result<T>) -> T {
	match result {
		Ok(r) => r,
		Err(e) => {
			panic!("Critical database error: {:?}", e);
		},
	}
}

/// Wrap parity-db database into a trait object that implements `sp_database::Database`
pub fn open<H: Clone + AsRef<[u8]>>(
	path: &std::path::Path,
	db_type: DatabaseType,
	create: bool,
) -> parity_db::Result<std::sync::Arc<dyn Database<H>>> {
	let mut config = parity_db::Options::with_columns(path, NUM_COLUMNS as u8);

	match db_type {
		DatabaseType::Full => {
			let indexes = [
				columns::STATE,
				columns::HEADER,
				columns::BODY,
				columns::TRANSACTION,
				columns::JUSTIFICATIONS,
			];

			for i in indexes {
				let mut column = &mut config.columns[i as usize];
				column.compression = parity_db::CompressionType::Lz4;
			}

			let mut state_col = &mut config.columns[columns::STATE as usize];
			state_col.ref_counted = true;
			state_col.preimage = true;
			state_col.uniform = true;
		},
		DatabaseType::Light => {
			config.columns[light::columns::HEADER as usize].compression =
				parity_db::CompressionType::Lz4;
		},
	}

	let db = if create {
		parity_db::Db::open_or_create(&config)?
	} else {
		parity_db::Db::open(&config)?
	};

	Ok(std::sync::Arc::new(DbAdapter(db)))
}

impl<H: Clone + AsRef<[u8]>> Database<H> for DbAdapter {
	fn commit(&self, transaction: Transaction<H>) -> Result<(), DatabaseError> {
		handle_err(self.0.commit(transaction.0.into_iter().map(|change| match change {
			Change::Set(col, key, value) => (col as u8, key, Some(value)),
			Change::Remove(col, key) => (col as u8, key, None),
			_ => unimplemented!(),
		})));

		Ok(())
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		handle_err(self.0.get(col as u8, key))
	}

	fn contains(&self, col: ColumnId, key: &[u8]) -> bool {
		handle_err(self.0.get_size(col as u8, key)).is_some()
	}

	fn value_size(&self, col: ColumnId, key: &[u8]) -> Option<usize> {
		handle_err(self.0.get_size(col as u8, key)).map(|s| s as usize)
	}

	fn supports_ref_counting(&self) -> bool {
		true
	}
}
