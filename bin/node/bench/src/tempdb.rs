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

use sc_client_db::DatabaseSource;
use node_primitives::Block;
use std::path::PathBuf;

#[derive(Clone, Copy, Debug)]
pub enum DatabaseType {
	RocksDb,
	ParityDb,
}

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

	pub fn open(&mut self, db_type: DatabaseType) -> sc_client_db::StorageDb<Block> {
		match db_type {
			DatabaseType::RocksDb => {
				let db = sc_client_db::open_database::<Block>(
					&DatabaseSource::RocksDb { path: self.0.path().into(), cache_size: 128*1024*1024 },
					true,
					false,
				).expect("Database backend error");
				sc_client_db::StorageDb::<Block> { db, state_db: None }
			},
			DatabaseType::ParityDb => {
				let db = sc_client_db::open_database::<Block>(
					&DatabaseSource::ParityDb { path: self.0.path().into() },
					true,
					false,
				).expect("Database backend error");
				sc_client_db::StorageDb::<Block> { db, state_db: None }
			},
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
