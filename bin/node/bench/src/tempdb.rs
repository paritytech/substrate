// Copyright 2020 Parity Technologies (UK) Ltd.
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

use std::sync::Arc;
use kvdb::KeyValueDB;
use kvdb_rocksdb::{DatabaseConfig, Database};

pub struct TempDatabase(tempfile::TempDir);

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

	pub fn open(&mut self) -> Arc<dyn KeyValueDB> {
		let db_cfg = DatabaseConfig::with_columns(1);
		let db = Database::open(&db_cfg, &self.0.path().to_string_lossy()).expect("Database backend error");
		Arc::new(db)
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
