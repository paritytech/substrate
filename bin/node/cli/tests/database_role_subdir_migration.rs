// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use sc_client_db::{
	light::LightStorage, DatabaseSettings, DatabaseSource, KeepBlocks, PruningMode,
	TransactionStorageMode,
};
use sp_runtime::testing::{Block as RawBlock, ExtrinsicWrapper};
use tempfile::tempdir;

pub mod common;

#[tokio::test]
#[cfg(unix)]
async fn database_role_subdir_migration() {
	type Block = RawBlock<ExtrinsicWrapper<u64>>;

	let base_path = tempdir().expect("could not create a temp dir");
	let path = base_path.path().join("chains/dev/db");
	// create a dummy database dir
	{
		let _old_db = LightStorage::<Block>::new(DatabaseSettings {
			state_cache_size: 0,
			state_cache_child_ratio: None,
			state_pruning: PruningMode::ArchiveAll,
			source: DatabaseSource::RocksDb { path: path.to_path_buf(), cache_size: 128 },
			keep_blocks: KeepBlocks::All,
			transaction_storage: TransactionStorageMode::BlockBody,
		})
		.unwrap();
	}

	assert!(path.join("db_version").exists());
	assert!(!path.join("light").exists());

	// start a light client
	common::run_node_for_a_while(
		base_path.path(),
		&[
			"--dev",
			"--light",
			"--port",
			"30335",
			"--rpc-port",
			"44444",
			"--ws-port",
			"44445",
			"--no-prometheus",
		],
	)
	.await;

	// check if the database dir had been migrated
	assert!(!path.join("db_version").exists());
	assert!(path.join("light/db_version").exists());
}

#[test]
#[cfg(unix)]
fn database_role_subdir_migration_fail_on_different_role() {
	type Block = RawBlock<ExtrinsicWrapper<u64>>;

	let base_path = tempdir().expect("could not create a temp dir");
	let path = base_path.path().join("chains/dev/db");

	// create a database with the old layout
	{
		let _old_db = LightStorage::<Block>::new(DatabaseSettings {
			state_cache_size: 0,
			state_cache_child_ratio: None,
			state_pruning: PruningMode::ArchiveAll,
			source: DatabaseSource::RocksDb { path: path.to_path_buf(), cache_size: 128 },
			keep_blocks: KeepBlocks::All,
			transaction_storage: TransactionStorageMode::BlockBody,
		})
		.unwrap();
	}

	assert!(path.join("db_version").exists());
	assert!(!path.join("light/db_version").exists());

	// start a client with a different role (full), it should fail and not change any files on disk
	common::run_node_assert_fail(
		&base_path.path(),
		&[
			"--dev",
			"--port",
			"30334",
			"--rpc-port",
			"44446",
			"--ws-port",
			"44447",
			"--no-prometheus",
		],
	);

	// check if the files are unchanged
	assert!(path.join("db_version").exists());
	assert!(!path.join("light/db_version").exists());
	assert!(!path.join("full/db_version").exists());
}
