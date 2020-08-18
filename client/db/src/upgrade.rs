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
use log::warn;
use std::marker::PhantomData;
use std::time::{Duration, Instant};

use sp_runtime::traits::{Block as BlockT, HashFor, NumberFor, Header as HeaderT};
use crate::utils::DatabaseType;
use crate::{StateDb, PruningMode, StateMetaDb};
use codec::{Decode, Encode};
use kvdb::KeyValueDB;
use std::io;

use std::sync::Arc;

/// Version file name.
const VERSION_FILE_NAME: &'static str = "db_version";

/// Current db version.
const CURRENT_VERSION: u32 = 1;

/// Upgrade database to current version.
pub fn upgrade_db<Block: BlockT>(db_path: &Path, db_type: DatabaseType) -> sp_blockchain::Result<()> {
	let is_empty = db_path.read_dir().map_or(true, |mut d| d.next().is_none());
	if !is_empty {
		let db_version = current_version(db_path)?;
		match db_version {
			0 => Err(sp_blockchain::Error::Backend(format!("Unsupported database version: {}", db_version)))?,
			1 => (),
			42 => {
				test_thing::<Block>(db_path, db_type)?;
			},
			_ => Err(sp_blockchain::Error::Backend(format!("Future database version: {}", db_version)))?,
		}
	}

	update_version(db_path)
}

/// Database backed tree management for a rocksdb database.
pub struct RocksdbStorage(Arc<kvdb_rocksdb::Database>);

impl RocksdbStorage {
/*	pub fn resolve_collection(c: &'static [u8]) -> Option<u32> {
		if c.len() != 4 {
			return None;
		}
		let index = Self::resolve_collection_inner(c);
		if index < crate::utils::NUM_COLUMNS {
			return Some(index);
		}
		None
	}
	const fn resolve_collection_inner(c: &'static [u8]) -> u32 {
		let mut buf = [0u8; 4];
		buf[0] = c[0];
		buf[1] = c[1];
		buf[2] = c[2];
		buf[3] = c[3];
		u32::from_le_bytes(buf)
	}

	fn write(&mut self, c: &'static [u8], k: &[u8], v: &[u8]) {
		Self::resolve_collection(c).map(|c| {
			let mut tx = self.0.transaction();
			tx.put(c, k, v);
			self.0.write(tx)
				.expect("Unsupported serialize error")
		});
	}

	fn remove(&mut self, c: &'static [u8], k: &[u8]) {
		Self::resolve_collection(c).map(|c| {
			let mut tx = self.0.transaction();
			tx.delete(c, k);
			self.0.write(tx)
				.expect("Unsupported serialize error")
		});
	}

	fn clear(&mut self, c: &'static [u8]) {
		Self::resolve_collection(c).map(|c| {
			let mut tx = self.0.transaction();
			tx.delete_prefix(c, &[]);
			self.0.write(tx)
				.expect("Unsupported serialize error")
		});
	}

	fn read(&self, c: &'static [u8], k: &[u8]) -> Option<Vec<u8>> {
		Self::resolve_collection(c).and_then(|c| {
			self.0.get(c, k)
				.expect("Unsupported readdb error")
		})
	}
	fn iter<'a>(&'a self, c: &'static [u8]) -> SerializeDBIter<'a> {
		let iter = Self::resolve_collection(c).map(|c| {
			self.0.iter(c).map(|(k, v)| (Vec::<u8>::from(k), Vec::<u8>::from(v)))
		}).into_iter().flat_map(|i| i);

		Box::new(iter)
	}
*/
	fn iter<'a>(&'a self, c: u32) -> SerializeDBIter<'a> {
		let iter = self.0.iter(c).map(|(k, v)| (Vec::<u8>::from(k), Vec::<u8>::from(v)));

		Box::new(iter)
	}

/*
	fn contains_collection(collection: &'static [u8]) -> bool {
		Self::resolve_collection(collection).is_some()
	}*/
}
type SerializeDBIter<'a> = Box<dyn Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a>;

/// Hacky migrate to trigger action on db.
/// Here drop historied state content.
fn test_thing<Block: BlockT>(db_path: &Path, db_type: DatabaseType) -> sp_blockchain::Result<()> {

	let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(crate::utils::NUM_COLUMNS);
   {
		let option = rocksdb::Options::default();
		 let cfs = rocksdb::DB::list_cf(&option, db_path).unwrap();
		 let db = rocksdb::DB::open_cf(&option, db_path, cfs.clone()).unwrap();
		 let mut i = 0;
		 for cf in cfs {

		 if let Some(col) = db.cf_handle(&cf) {
				println!("{:?}, {:?}", cf, db.property_int_value_cf(col, "rocksdb.estimate-table-readers-mem"));
				println!("{:?}, {:?}", cf, db.property_int_value_cf(col, "rocksdb.size-all-mem-tables"));
				println!("{:?}, {:?}", cf, db.property_int_value_cf(col, "rocksdb.cur-size-all-mem-tables"));
			}
		 }

	}

		 let mut i = 0;
		 {
				let path = db_path.to_str()
					.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;
		 while i < 6 {
				let db_read = Arc::new(kvdb_rocksdb::Database::open(&db_config, path)
					.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?);

				let db_r = RocksdbStorage(db_read.clone());
				let iter_kv = db_r.iter(i);
				println!("{:?}, nb_iter {:?}", i, iter_kv.count());
				i += 1;

		 }
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

/// Maps database error to client error
fn db_err(err: std::io::Error) -> sp_blockchain::Error {
	sp_blockchain::Error::Backend(format!("{}", err))
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
			source: DatabaseSettingsSrc::RocksDb { path: db_path.to_owned(), cache_size: 128 },
		}, DatabaseType::Full).map(|_| ())
	}

	#[test]
	fn downgrade_never_happens() {
		let db_dir = tempfile::TempDir::new().unwrap();
		create_db(db_dir.path(), Some(CURRENT_VERSION + 1));
		assert!(open_database(db_dir.path()).is_err());
	}

	#[test]
	fn open_empty_database_works() {
		let db_dir = tempfile::TempDir::new().unwrap();
		open_database(db_dir.path()).unwrap();
		open_database(db_dir.path()).unwrap();
		assert_eq!(current_version(db_dir.path()).unwrap(), CURRENT_VERSION);
	}
}
