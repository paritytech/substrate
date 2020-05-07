// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
use std::{io, sync::Arc};
use kvdb::{KeyValueDB, DBTransaction};
use kvdb_rocksdb::{DatabaseConfig, Database};

#[derive(Debug, Clone, Copy, derive_more::Display)]
pub enum DatabaseType {
	RocksDb,
	ParityDb,
}

pub struct TempDatabase(tempfile::TempDir);

struct ParityDbWrapper(parity_db::Db);
parity_util_mem::malloc_size_of_is_0!(ParityDbWrapper);

impl KeyValueDB for ParityDbWrapper {
	/// Get a value by key.
	fn get(&self, col: u32, key: &[u8]) -> io::Result<Option<Vec<u8>>> {
		Ok(self.0.get(col as u8, &key[key.len() - 32..]).expect("db error"))
	}

	/// Get a value by partial key. Only works for flushed data.
	fn get_by_prefix(&self, _col: u32, _prefix: &[u8]) -> Option<Box<[u8]>> {
		unimplemented!()
	}

	/// Write a transaction of changes to the buffer.
	fn write_buffered(&self, transaction: DBTransaction) {
		self.0.commit(
			transaction.ops.iter().map(|op| match op {
				kvdb::DBOp::Insert { col, key, value } => (*col as u8, &key[key.len() - 32..], Some(value.to_vec())),
				kvdb::DBOp::Delete { col, key } => (*col as u8, &key[key.len() - 32..], None),
			})
		).expect("db error");
	}

	/// Flush all buffered data.
	fn flush(&self) -> io::Result<()> {
		Ok(())
	}

	/// Iterate over flushed data for a given column.
	fn iter<'a>(&'a self, _col: u32) -> Box<dyn Iterator<Item = (Box<[u8]>, Box<[u8]>)> + 'a> {
		unimplemented!()
	}

	/// Iterate over flushed data for a given column, starting from a given prefix.
	fn iter_from_prefix<'a>(
		&'a self,
		_col: u32,
		_prefix: &'a [u8],
	) -> Box<dyn Iterator<Item = (Box<[u8]>, Box<[u8]>)> + 'a> {
		unimplemented!()
	}

	/// Attempt to replace this database with a new one located at the given path.
	fn restore(&self, _new_db: &str) -> io::Result<()> {
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
				let db = Database::open(&db_cfg, &self.0.path().to_string_lossy()).expect("Database backend error");
				Arc::new(db)
			},
			DatabaseType::ParityDb => {
				Arc::new(ParityDbWrapper({
					let mut options = parity_db::Options::with_columns(self.0.path(), 1);
					let mut column_options = &mut options.columns[0];
					column_options.ref_counted = true;
					column_options.preimage = true;
					column_options.uniform = true;
					parity_db::Db::open(&options).expect("db open error")
				}))
			}
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
			.map(|f_result|
				f_result.expect("failed to read file in seed db")
					.path()
					.clone()
			).collect();
		fs_extra::copy_items(
			&self_db_files,
			new_dir.path(),
			&fs_extra::dir::CopyOptions::new(),
		).expect("Copy of seed database is ok");

		TempDatabase(new_dir)
	}
}
