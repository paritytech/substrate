// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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
	columns,
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
	upgrade: bool,
) -> parity_db::Result<std::sync::Arc<dyn Database<H>>> {
	let mut config = parity_db::Options::with_columns(path, NUM_COLUMNS as u8);

	match db_type {
		DatabaseType::Full => {
			let compressed = [
				columns::STATE,
				columns::HEADER,
				columns::BODY,
				columns::BODY_INDEX,
				columns::TRANSACTION,
				columns::JUSTIFICATIONS,
			];

			for i in compressed {
				let mut column = &mut config.columns[i as usize];
				column.compression = parity_db::CompressionType::Lz4;
			}

			let mut state_col = &mut config.columns[columns::STATE as usize];
			state_col.ref_counted = true;
			state_col.preimage = true;
			state_col.uniform = true;

			let mut tx_col = &mut config.columns[columns::TRANSACTION as usize];
			tx_col.ref_counted = true;
			tx_col.preimage = true;
			tx_col.uniform = true;
		},
	}

	if upgrade {
		log::info!("Upgrading database metadata.");
		if let Some(meta) = parity_db::Options::load_metadata(path)? {
			config.write_metadata_with_version(path, &meta.salt, Some(meta.version))?;
		}
	}

	let db = if create {
		parity_db::Db::open_or_create(&config)?
	} else {
		parity_db::Db::open(&config)?
	};

	Ok(std::sync::Arc::new(DbAdapter(db)))
}

fn ref_counted_column(col: u32) -> bool {
	col == columns::TRANSACTION || col == columns::STATE
}

impl<H: Clone + AsRef<[u8]>> Database<H> for DbAdapter {
	fn commit(&self, transaction: Transaction<H>) -> Result<(), DatabaseError> {
		let mut not_ref_counted_column = Vec::new();
		let result = self.0.commit(transaction.0.into_iter().filter_map(|change| {
			Some(match change {
				Change::Set(col, key, value) => (col as u8, key, Some(value)),
				Change::Remove(col, key) => (col as u8, key, None),
				Change::Store(col, key, value) =>
					if ref_counted_column(col) {
						(col as u8, key.as_ref().to_vec(), Some(value))
					} else {
						if !not_ref_counted_column.contains(&col) {
							not_ref_counted_column.push(col);
						}
						return None
					},
				Change::Reference(col, key) => {
					if ref_counted_column(col) {
						// FIXME accessing value is not strictly needed, optimize this in parity-db.
						let value = <Self as Database<H>>::get(self, col, key.as_ref());
						(col as u8, key.as_ref().to_vec(), value)
					} else {
						if !not_ref_counted_column.contains(&col) {
							not_ref_counted_column.push(col);
						}
						return None
					}
				},
				Change::Release(col, key) =>
					if ref_counted_column(col) {
						(col as u8, key.as_ref().to_vec(), None)
					} else {
						if !not_ref_counted_column.contains(&col) {
							not_ref_counted_column.push(col);
						}
						return None
					},
			})
		}));

		if not_ref_counted_column.len() > 0 {
			return Err(DatabaseError(Box::new(parity_db::Error::InvalidInput(format!(
				"Ref counted operation on non ref counted columns {:?}",
				not_ref_counted_column
			)))))
		}

		result.map_err(|e| DatabaseError(Box::new(e)))
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

	fn sanitize_key(&self, key: &mut Vec<u8>) {
		let _prefix = key.drain(0..key.len() - crate::DB_HASH_LEN);
	}
}
