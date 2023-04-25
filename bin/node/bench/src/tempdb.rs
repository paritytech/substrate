// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use kvdb::{DBKeyValue, DBTransaction, KeyValueDB};
use kvdb_rocksdb::{Database, DatabaseConfig};
use std::{io, path::PathBuf, sync::Arc};

#[derive(Clone, Copy, Debug)]
pub enum DatabaseType {
	RocksDb,
	ParityDb,
}

pub struct TempDatabase(tempfile::TempDir);

struct ParityDbWrapper(parity_db::Db);

impl KeyValueDB for ParityDbWrapper {
	/// Get a value by key.
	fn get(&self, col: u32, key: &[u8]) -> io::Result<Option<Vec<u8>>> {
		Ok(self.0.get(col as u8, &key[key.len() - 32..]).expect("db error"))
	}

	/// Get a value by partial key. Only works for flushed data.
	fn get_by_prefix(&self, _col: u32, _prefix: &[u8]) -> io::Result<Option<Vec<u8>>> {
		unimplemented!()
	}

	/// Write a transaction of changes to the buffer.
	fn write(&self, transaction: DBTransaction) -> io::Result<()> {
		self.0
			.commit(transaction.ops.iter().map(|op| match op {
				kvdb::DBOp::Insert { col, key, value } =>
					(*col as u8, &key[key.len() - 32..], Some(value.to_vec())),
				kvdb::DBOp::Delete { col, key } => (*col as u8, &key[key.len() - 32..], None),
				kvdb::DBOp::DeletePrefix { col: _, prefix: _ } => unimplemented!(),
			}))
			.expect("db error");
		Ok(())
	}

	/// Iterate over flushed data for a given column.
	fn iter<'a>(&'a self, _col: u32) -> Box<dyn Iterator<Item = io::Result<DBKeyValue>> + 'a> {
		unimplemented!()
	}

	/// Iterate over flushed data for a given column, starting from a given prefix.
	fn iter_with_prefix<'a>(
		&'a self,
		_col: u32,
		_prefix: &'a [u8],
	) -> Box<dyn Iterator<Item = io::Result<DBKeyValue>> + 'a> {
		unimplemented!()
	}
}

impl TempDatabase {
	pub fn new() -> Self {
		let dir = tempfile::tempdir().expect("temp dir creation failed");
		log::trace!(
			target: "bench-logistics",
			"Created temp db at {}",
			dir.path().to_string_lossy(),
		);

		TempDatabase(dir)
	}

	pub fn open(&mut self, db_type: DatabaseType) -> Arc<dyn KeyValueDB> {
		match db_type {
			DatabaseType::RocksDb => {
				let db_cfg = DatabaseConfig::with_columns(1);
				let db = Database::open(&db_cfg, &self.0.path()).expect("Database backend error");
				Arc::new(db)
			},
			DatabaseType::ParityDb => Arc::new(ParityDbWrapper({
				let mut options = parity_db::Options::with_columns(self.0.path(), 1);
				let mut column_options = &mut options.columns[0];
				column_options.ref_counted = true;
				column_options.preimage = true;
				column_options.uniform = true;
				parity_db::Db::open_or_create(&options).expect("db open error")
			})),
		}
	}
}

impl Clone for TempDatabase {
	fn clone(&self) -> Self {
		let new_dir = tempfile::tempdir().expect("temp dir creation failed");
		let self_dir = self.0.path();

		log::trace!(
			target: "bench-logistics",
			"Cloning db ({}) to {}",
			self_dir.to_string_lossy(),
			new_dir.path().to_string_lossy(),
		);
		let self_db_files = std::fs::read_dir(self_dir)
			.expect("failed to list file in seed dir")
			.map(|f_result| f_result.expect("failed to read file in seed db").path())
			.collect::<Vec<PathBuf>>();
		fs_extra::copy_items(&self_db_files, new_dir.path(), &fs_extra::dir::CopyOptions::new())
			.expect("Copy of seed database is ok");

		TempDatabase(new_dir)
	}
}
