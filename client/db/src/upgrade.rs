// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Database upgrade logic.

use std::fs;
use std::io::{Read, Write, ErrorKind};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use codec::Encode;
use kvdb_rocksdb::{Database, DatabaseConfig};
use parking_lot::RwLock;
use sp_blockchain::{well_known_cache_keys, Cache};
use sp_core::ChangesTrieConfiguration;
use sp_runtime::traits::Block as BlockT;
use crate::{
	cache::{ComplexBlockId, DbCache, DbCacheSync},
	utils::{DatabaseType, check_database_type, db_err, read_genesis_hash},
};

/// Version file name.
const VERSION_FILE_NAME: &'static str = "db_version";

/// Current db version.
const CURRENT_VERSION: u32 = 1;

/// Number of columns in v0.
const V0_NUM_COLUMNS: u32 = 10;

/// Upgrade database to current version.
pub fn upgrade_db<Block: BlockT>(db_path: &Path, db_type: DatabaseType) -> sp_blockchain::Result<()> {
	let db_version = current_version(db_path)?;
	match db_version {
		0 => migrate_0_to_1::<Block>(db_path, db_type)?,
		1 => (),
		_ => Err(sp_blockchain::Error::Backend(format!("Future database version: {}", db_version)))?,
	}

	update_version(db_path)
}

/// Migration from version0 to version1:
/// 1) the number of columns has changed from 10 to 11;
/// 2) changes tries configuration are now cached.
fn migrate_0_to_1<Block: BlockT>(db_path: &Path, db_type: DatabaseType) -> sp_blockchain::Result<()> {
	{
		let db = open_database(db_path, db_type, V0_NUM_COLUMNS)?;
		db.add_column().map_err(db_err)?;
		db.flush().map_err(db_err)?;
	}

	let db = open_database(db_path, db_type, V0_NUM_COLUMNS + 1)?;

	const V0_FULL_KEY_LOOKUP_COLUMN: u32 = 3;
	const V0_FULL_HEADER_COLUMN: u32 = 4;
	const V0_FULL_CACHE_COLUMN: u32 = 10; // that's the column we have just added
	const V0_LIGHT_KEY_LOOKUP_COLUMN: u32 = 1;
	const V0_LIGHT_HEADER_COLUMN: u32 = 2;
	const V0_LIGHT_CACHE_COLUMN: u32 = 3;

	let (key_lookup_column, header_column, cache_column) = match db_type {
		DatabaseType::Full => (
			V0_FULL_KEY_LOOKUP_COLUMN,
			V0_FULL_HEADER_COLUMN,
			V0_FULL_CACHE_COLUMN,
		),
		DatabaseType::Light => (
			V0_LIGHT_KEY_LOOKUP_COLUMN,
			V0_LIGHT_HEADER_COLUMN,
			V0_LIGHT_CACHE_COLUMN,
		),
	};

	let genesis_hash: Option<Block::Hash> = read_genesis_hash(&db)?;
	if let Some(genesis_hash) = genesis_hash {
		let cache: DbCacheSync<Block> = DbCacheSync(RwLock::new(DbCache::new(
			Arc::new(db),
			key_lookup_column,
			header_column,
			cache_column,
			genesis_hash,
			ComplexBlockId::new(genesis_hash, 0.into()),
		)));
		let changes_trie_config: Option<ChangesTrieConfiguration> = None;
		cache.initialize(&well_known_cache_keys::CHANGES_TRIE_CONFIG, changes_trie_config.encode())?;
	}

	Ok(())
}

/// Reads current database version from the file at given path.
/// If the file does not exist returns 0.
fn current_version(path: &Path) -> sp_blockchain::Result<u32> {
	let unknown_version_err = || sp_blockchain::Error::Backend("Unknown database version".into());

	match fs::File::open(version_file_path(path)) {
		Err(ref err) if err.kind() == ErrorKind::NotFound => Ok(0),
		Err(_) => Err(unknown_version_err()),
		Ok(mut file) => {
			let mut s = String::new();
			file.read_to_string(&mut s).map_err(|_| unknown_version_err())?;
			u32::from_str_radix(&s, 10).map_err(|_| unknown_version_err())
		},
	}
}

/// Opens database of givent type with given number of columns.
fn open_database(db_path: &Path, db_type: DatabaseType, db_columns: u32) -> sp_blockchain::Result<Database> {
	let db_path = db_path.to_str()
		.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;
	let db_cfg = DatabaseConfig::with_columns(db_columns);
	let db = Database::open(&db_cfg, db_path).map_err(db_err)?;
	check_database_type(&db, db_type)?;
	Ok(db)
}

/// Writes current database version to the file.
/// Creates a new file if the version file does not exist yet.
fn update_version(path: &Path) -> sp_blockchain::Result<()> {
	fs::create_dir_all(path).map_err(db_err)?;
	let mut file = fs::File::create(version_file_path(path)).map_err(db_err)?;
	file.write_all(format!("{}", CURRENT_VERSION).as_bytes()).map_err(db_err)?;
	Ok(())
}

/// Returns the version file path.
fn version_file_path(path: &Path) -> PathBuf {
	let mut file_path = path.to_owned();
	file_path.push(VERSION_FILE_NAME);
	file_path
}

#[cfg(test)]
mod tests {
	use sc_state_db::PruningMode;
	use crate::{DatabaseSettings, DatabaseSettingsSrc};
	use crate::tests::Block;
	use super::*;

	fn create_db(db_path: &Path, version: Option<u32>) {
		let db_cfg = DatabaseConfig::with_columns(V0_NUM_COLUMNS);
		Database::open(&db_cfg, db_path.to_str().unwrap()).unwrap();
		if let Some(version) = version {
			fs::create_dir_all(db_path).unwrap();
			let mut file = fs::File::create(version_file_path(db_path)).unwrap();
			file.write_all(format!("{}", version).as_bytes()).unwrap();
		}
	}

	fn open_database(db_path: &Path) -> sp_blockchain::Result<()> {
		crate::utils::open_database::<Block>(&DatabaseSettings {
			state_cache_size: 0,
			state_cache_child_ratio: None,
			pruning: PruningMode::ArchiveAll,
			source: DatabaseSettingsSrc::Path { path: db_path.to_owned(), cache_size: None },
		}, DatabaseType::Full).map(|_| ())
	}

	#[test]
	fn downgrade_never_happens() {
		let db_dir = tempdir::TempDir::new("").unwrap();
		create_db(db_dir.path(), Some(CURRENT_VERSION + 1));
		assert!(open_database(db_dir.path()).is_err());
	}

	#[test]
	fn open_empty_database_works() {
		let db_dir = tempdir::TempDir::new("").unwrap();
		open_database(db_dir.path()).unwrap();
		open_database(db_dir.path()).unwrap();
		assert_eq!(current_version(db_dir.path()).unwrap(), CURRENT_VERSION);
	}

	#[test]
	fn upgrade_from_0_to_1_works() {
		for version_from_file in &[None, Some(0)] {
			let db_dir = tempdir::TempDir::new("").unwrap();
			let db_path = db_dir.path();
			create_db(db_path, *version_from_file);
			open_database(db_path).unwrap();
			assert_eq!(current_version(db_path).unwrap(), CURRENT_VERSION);
		}
	}
}
