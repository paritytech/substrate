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

//! Db-based backend utility structures and functions, used by both
//! full and light storages.

use std::{convert::TryInto, fmt, fs, io, path::Path, sync::Arc};

use log::{debug, info};

use crate::{Database, DatabaseSettings, DatabaseSource, DbHash};
use codec::Decode;
use sp_database::Transaction;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT, UniqueSaturatedFrom, UniqueSaturatedInto, Zero},
};
use sp_trie::DBValue;

/// Number of columns in the db. Must be the same for both full && light dbs.
/// Otherwise RocksDb will fail to open database && check its type.
#[cfg(any(
	feature = "with-kvdb-rocksdb",
	feature = "with-parity-db",
	feature = "test-helpers",
	test
))]
pub const NUM_COLUMNS: u32 = 12;
/// Meta column. The set of keys in the column is shared by full && light storages.
pub const COLUMN_META: u32 = 0;

/// Keys of entries in COLUMN_META.
pub mod meta_keys {
	/// Type of storage (full or light).
	pub const TYPE: &[u8; 4] = b"type";
	/// Best block key.
	pub const BEST_BLOCK: &[u8; 4] = b"best";
	/// Last finalized block key.
	pub const FINALIZED_BLOCK: &[u8; 5] = b"final";
	/// Last finalized state key.
	pub const FINALIZED_STATE: &[u8; 6] = b"fstate";
	/// Meta information prefix for list-based caches.
	pub const CACHE_META_PREFIX: &[u8; 5] = b"cache";
	/// Meta information for changes tries key.
	pub const CHANGES_TRIES_META: &[u8; 5] = b"ctrie";
	/// Genesis block hash.
	pub const GENESIS_HASH: &[u8; 3] = b"gen";
	/// Leaves prefix list key.
	pub const LEAF_PREFIX: &[u8; 4] = b"leaf";
	/// Children prefix list key.
	pub const CHILDREN_PREFIX: &[u8; 8] = b"children";
}

/// Database metadata.
#[derive(Debug)]
pub struct Meta<N, H> {
	/// Hash of the best known block.
	pub best_hash: H,
	/// Number of the best known block.
	pub best_number: N,
	/// Hash of the best finalized block.
	pub finalized_hash: H,
	/// Number of the best finalized block.
	pub finalized_number: N,
	/// Hash of the genesis block.
	pub genesis_hash: H,
	/// Finalized state, if any
	pub finalized_state: Option<(H, N)>,
}

/// A block lookup key: used for canonical lookup from block number to hash
pub type NumberIndexKey = [u8; 4];

/// Database type.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum DatabaseType {
	/// Full node database.
	Full,
	/// Light node database.
	Light,
}

/// Convert block number into short lookup key (LE representation) for
/// blocks that are in the canonical chain.
///
/// In the current database schema, this kind of key is only used for
/// lookups into an index, NOT for storing header data or others.
pub fn number_index_key<N: TryInto<u32>>(n: N) -> sp_blockchain::Result<NumberIndexKey> {
	let n = n.try_into().map_err(|_| {
		sp_blockchain::Error::Backend("Block number cannot be converted to u32".into())
	})?;

	Ok([(n >> 24) as u8, ((n >> 16) & 0xff) as u8, ((n >> 8) & 0xff) as u8, (n & 0xff) as u8])
}

/// Convert number and hash into long lookup key for blocks that are
/// not in the canonical chain.
pub fn number_and_hash_to_lookup_key<N, H>(number: N, hash: H) -> sp_blockchain::Result<Vec<u8>>
where
	N: TryInto<u32>,
	H: AsRef<[u8]>,
{
	let mut lookup_key = number_index_key(number)?.to_vec();
	lookup_key.extend_from_slice(hash.as_ref());
	Ok(lookup_key)
}

/// Convert block lookup key into block number.
/// all block lookup keys start with the block number.
pub fn lookup_key_to_number<N>(key: &[u8]) -> sp_blockchain::Result<N>
where
	N: From<u32>,
{
	if key.len() < 4 {
		return Err(sp_blockchain::Error::Backend("Invalid block key".into()))
	}
	Ok((key[0] as u32) << 24 | (key[1] as u32) << 16 | (key[2] as u32) << 8 | (key[3] as u32))
		.map(Into::into)
}

/// Delete number to hash mapping in DB transaction.
pub fn remove_number_to_key_mapping<N: TryInto<u32>>(
	transaction: &mut Transaction<DbHash>,
	key_lookup_col: u32,
	number: N,
) -> sp_blockchain::Result<()> {
	transaction.remove(key_lookup_col, number_index_key(number)?.as_ref());
	Ok(())
}

/// Remove key mappings.
pub fn remove_key_mappings<N: TryInto<u32>, H: AsRef<[u8]>>(
	transaction: &mut Transaction<DbHash>,
	key_lookup_col: u32,
	number: N,
	hash: H,
) -> sp_blockchain::Result<()> {
	remove_number_to_key_mapping(transaction, key_lookup_col, number)?;
	transaction.remove(key_lookup_col, hash.as_ref());
	Ok(())
}

/// Place a number mapping into the database. This maps number to current perceived
/// block hash at that position.
pub fn insert_number_to_key_mapping<N: TryInto<u32> + Clone, H: AsRef<[u8]>>(
	transaction: &mut Transaction<DbHash>,
	key_lookup_col: u32,
	number: N,
	hash: H,
) -> sp_blockchain::Result<()> {
	transaction.set_from_vec(
		key_lookup_col,
		number_index_key(number.clone())?.as_ref(),
		number_and_hash_to_lookup_key(number, hash)?,
	);
	Ok(())
}

/// Insert a hash to key mapping in the database.
pub fn insert_hash_to_key_mapping<N: TryInto<u32>, H: AsRef<[u8]> + Clone>(
	transaction: &mut Transaction<DbHash>,
	key_lookup_col: u32,
	number: N,
	hash: H,
) -> sp_blockchain::Result<()> {
	transaction.set_from_vec(
		key_lookup_col,
		hash.as_ref(),
		number_and_hash_to_lookup_key(number, hash.clone())?,
	);
	Ok(())
}

/// Convert block id to block lookup key.
/// block lookup key is the DB-key header, block and justification are stored under.
/// looks up lookup key by hash from DB as necessary.
pub fn block_id_to_lookup_key<Block>(
	db: &dyn Database<DbHash>,
	key_lookup_col: u32,
	id: BlockId<Block>,
) -> Result<Option<Vec<u8>>, sp_blockchain::Error>
where
	Block: BlockT,
	::sp_runtime::traits::NumberFor<Block>: UniqueSaturatedFrom<u64> + UniqueSaturatedInto<u64>,
{
	Ok(match id {
		BlockId::Number(n) => db.get(key_lookup_col, number_index_key(n)?.as_ref()),
		BlockId::Hash(h) => db.get(key_lookup_col, h.as_ref()),
	})
}

fn backend_err(feat: &'static str) -> sp_blockchain::Error {
	sp_blockchain::Error::Backend(feat.to_string())
}

/// Opens the configured database.
pub fn open_database<Block: BlockT>(
	config: &DatabaseSettings,
	db_type: DatabaseType,
) -> sp_blockchain::Result<Arc<dyn Database<DbHash>>> {
	// Maybe migrate (copy) the database to a type specific subdirectory to make it
	// possible that light and full databases coexist
	// NOTE: This function can be removed in a few releases
	maybe_migrate_to_type_subdir::<Block>(&config.source, db_type).map_err(|e| {
		sp_blockchain::Error::Backend(format!("Error in migration to role subdirectory: {}", e))
	})?;

	open_database_at::<Block>(&config.source, db_type)
}

fn open_database_at<Block: BlockT>(
	source: &DatabaseSource,
	db_type: DatabaseType,
) -> sp_blockchain::Result<Arc<dyn Database<DbHash>>> {
	let db: Arc<dyn Database<DbHash>> = match &source {
		DatabaseSource::ParityDb { path } => open_parity_db::<Block>(&path, db_type, true)?,
		DatabaseSource::RocksDb { path, cache_size } =>
			open_kvdb_rocksdb::<Block>(&path, db_type, true, *cache_size)?,
		DatabaseSource::Custom(db) => db.clone(),
		DatabaseSource::Auto { paritydb_path, rocksdb_path, cache_size } => {
			// check if rocksdb exists first, if not, open paritydb
			match open_kvdb_rocksdb::<Block>(&rocksdb_path, db_type, false, *cache_size) {
				Ok(db) => db,
				Err(OpenDbError::NotEnabled(_)) | Err(OpenDbError::DoesNotExist) =>
					open_parity_db::<Block>(&paritydb_path, db_type, true)?,
				Err(_) => return Err(backend_err("cannot open rocksdb. corrupted database")),
			}
		},
	};

	check_database_type(&*db, db_type)?;
	Ok(db)
}

#[derive(Debug)]
enum OpenDbError {
	// constructed only when rocksdb and paritydb are disabled
	#[allow(dead_code)]
	NotEnabled(&'static str),
	DoesNotExist,
	Internal(String),
}

type OpenDbResult = Result<Arc<dyn Database<DbHash>>, OpenDbError>;

impl fmt::Display for OpenDbError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			OpenDbError::Internal(e) => write!(f, "{}", e.to_string()),
			OpenDbError::DoesNotExist => write!(f, "Database does not exist at given location"),
			OpenDbError::NotEnabled(feat) => {
				write!(f, "`{}` feature not enabled, database can not be opened", feat)
			},
		}
	}
}

impl From<OpenDbError> for sp_blockchain::Error {
	fn from(err: OpenDbError) -> Self {
		sp_blockchain::Error::Backend(err.to_string())
	}
}

#[cfg(feature = "with-parity-db")]
impl From<parity_db::Error> for OpenDbError {
	fn from(err: parity_db::Error) -> Self {
		if err.to_string().contains("use open_or_create") {
			OpenDbError::DoesNotExist
		} else {
			OpenDbError::Internal(err.to_string())
		}
	}
}

impl From<io::Error> for OpenDbError {
	fn from(err: io::Error) -> Self {
		if err.to_string().contains("create_if_missing is false") {
			OpenDbError::DoesNotExist
		} else {
			OpenDbError::Internal(err.to_string())
		}
	}
}

#[cfg(feature = "with-parity-db")]
fn open_parity_db<Block: BlockT>(path: &Path, db_type: DatabaseType, create: bool) -> OpenDbResult {
	let db = crate::parity_db::open(path, db_type, create)?;
	Ok(db)
}

#[cfg(not(feature = "with-parity-db"))]
fn open_parity_db<Block: BlockT>(
	_path: &Path,
	_db_type: DatabaseType,
	_create: bool,
) -> OpenDbResult {
	Err(OpenDbError::NotEnabled("with-parity-db"))
}

#[cfg(any(feature = "with-kvdb-rocksdb", test))]
fn open_kvdb_rocksdb<Block: BlockT>(
	path: &Path,
	db_type: DatabaseType,
	create: bool,
	cache_size: usize,
) -> OpenDbResult {
	// first upgrade database to required version
	match crate::upgrade::upgrade_db::<Block>(&path, db_type) {
		// in case of missing version file, assume that database simply does not exist at given
		// location
		Ok(_) | Err(crate::upgrade::UpgradeError::MissingDatabaseVersionFile) => (),
		Err(err) => return Err(io::Error::new(io::ErrorKind::Other, err.to_string()).into()),
	}

	// and now open database assuming that it has the latest version
	let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(NUM_COLUMNS);
	db_config.create_if_missing = create;

	let mut memory_budget = std::collections::HashMap::new();
	match db_type {
		DatabaseType::Full => {
			let state_col_budget = (cache_size as f64 * 0.9) as usize;
			let other_col_budget = (cache_size - state_col_budget) / (NUM_COLUMNS as usize - 1);

			for i in 0..NUM_COLUMNS {
				if i == crate::columns::STATE {
					memory_budget.insert(i, state_col_budget);
				} else {
					memory_budget.insert(i, other_col_budget);
				}
			}
			log::trace!(
				target: "db",
				"Open RocksDB database at {:?}, state column budget: {} MiB, others({}) column cache: {} MiB",
				path,
				state_col_budget,
				NUM_COLUMNS,
				other_col_budget,
			);
		},
		DatabaseType::Light => {
			let col_budget = cache_size / (NUM_COLUMNS as usize);
			for i in 0..NUM_COLUMNS {
				memory_budget.insert(i, col_budget);
			}
			log::trace!(
				target: "db",
				"Open RocksDB light database at {:?}, column cache: {} MiB",
				path,
				col_budget,
			);
		},
	}
	db_config.memory_budget = memory_budget;

	let db = kvdb_rocksdb::Database::open(&db_config, path)?;
	// write database version only after the database is succesfully opened
	crate::upgrade::update_version(path)?;
	Ok(sp_database::as_database(db))
}

#[cfg(not(any(feature = "with-kvdb-rocksdb", test)))]
fn open_kvdb_rocksdb<Block: BlockT>(
	_path: &Path,
	_db_type: DatabaseType,
	_create: bool,
	_cache_size: usize,
) -> OpenDbResult {
	Err(OpenDbError::NotEnabled("with-kvdb-rocksdb"))
}

/// Check database type.
pub fn check_database_type(
	db: &dyn Database<DbHash>,
	db_type: DatabaseType,
) -> sp_blockchain::Result<()> {
	match db.get(COLUMN_META, meta_keys::TYPE) {
		Some(stored_type) =>
			if db_type.as_str().as_bytes() != &*stored_type {
				return Err(sp_blockchain::Error::Backend(format!(
					"Unexpected database type. Expected: {}",
					db_type.as_str()
				))
				.into())
			},
		None => {
			let mut transaction = Transaction::new();
			transaction.set(COLUMN_META, meta_keys::TYPE, db_type.as_str().as_bytes());
			db.commit(transaction)?;
		},
	}

	Ok(())
}

fn maybe_migrate_to_type_subdir<Block: BlockT>(
	source: &DatabaseSource,
	db_type: DatabaseType,
) -> io::Result<()> {
	if let Some(p) = source.path() {
		let mut basedir = p.to_path_buf();
		basedir.pop();

		// Do we have to migrate to a database-type-based subdirectory layout:
		// See if there's a file identifying a rocksdb or paritydb folder in the parent dir and
		// the target path ends in a role specific directory
		if (basedir.join("db_version").exists() || basedir.join("metadata").exists()) &&
			(p.ends_with(DatabaseType::Full.as_str()) ||
				p.ends_with(DatabaseType::Light.as_str()))
		{
			// Try to open the database to check if the current `DatabaseType` matches the type of
			// database stored in the target directory and close the database on success.
			let mut old_source = source.clone();
			old_source.set_path(&basedir);
			open_database_at::<Block>(&old_source, db_type)
				.map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

			info!(
				"Migrating database to a database-type-based subdirectory: '{:?}' -> '{:?}'",
				basedir,
				basedir.join(db_type.as_str())
			);
			let mut tmp_dir = basedir.clone();
			tmp_dir.pop();
			tmp_dir.push("tmp");

			fs::rename(&basedir, &tmp_dir)?;
			fs::create_dir_all(&p)?;
			fs::rename(tmp_dir, &p)?;
		}
	}

	Ok(())
}

/// Read database column entry for the given block.
pub fn read_db<Block>(
	db: &dyn Database<DbHash>,
	col_index: u32,
	col: u32,
	id: BlockId<Block>,
) -> sp_blockchain::Result<Option<DBValue>>
where
	Block: BlockT,
{
	block_id_to_lookup_key(db, col_index, id).and_then(|key| match key {
		Some(key) => Ok(db.get(col, key.as_ref())),
		None => Ok(None),
	})
}

/// Remove database column entry for the given block.
pub fn remove_from_db<Block>(
	transaction: &mut Transaction<DbHash>,
	db: &dyn Database<DbHash>,
	col_index: u32,
	col: u32,
	id: BlockId<Block>,
) -> sp_blockchain::Result<()>
where
	Block: BlockT,
{
	block_id_to_lookup_key(db, col_index, id).and_then(|key| match key {
		Some(key) => Ok(transaction.remove(col, key.as_ref())),
		None => Ok(()),
	})
}

/// Read a header from the database.
pub fn read_header<Block: BlockT>(
	db: &dyn Database<DbHash>,
	col_index: u32,
	col: u32,
	id: BlockId<Block>,
) -> sp_blockchain::Result<Option<Block::Header>> {
	match read_db(db, col_index, col, id)? {
		Some(header) => match Block::Header::decode(&mut &header[..]) {
			Ok(header) => Ok(Some(header)),
			Err(_) => return Err(sp_blockchain::Error::Backend("Error decoding header".into())),
		},
		None => Ok(None),
	}
}

/// Required header from the database.
pub fn require_header<Block: BlockT>(
	db: &dyn Database<DbHash>,
	col_index: u32,
	col: u32,
	id: BlockId<Block>,
) -> sp_blockchain::Result<Block::Header> {
	read_header(db, col_index, col, id).and_then(|header| {
		header.ok_or_else(|| sp_blockchain::Error::UnknownBlock(format!("Require header: {}", id)))
	})
}

/// Read meta from the database.
pub fn read_meta<Block>(
	db: &dyn Database<DbHash>,
	col_header: u32,
) -> Result<Meta<<<Block as BlockT>::Header as HeaderT>::Number, Block::Hash>, sp_blockchain::Error>
where
	Block: BlockT,
{
	let genesis_hash: Block::Hash = match read_genesis_hash(db)? {
		Some(genesis_hash) => genesis_hash,
		None =>
			return Ok(Meta {
				best_hash: Default::default(),
				best_number: Zero::zero(),
				finalized_hash: Default::default(),
				finalized_number: Zero::zero(),
				genesis_hash: Default::default(),
				finalized_state: None,
			}),
	};

	let load_meta_block = |desc, key| -> Result<_, sp_blockchain::Error> {
		if let Some(Some(header)) = db
			.get(COLUMN_META, key)
			.and_then(|id| db.get(col_header, &id).map(|b| Block::Header::decode(&mut &b[..]).ok()))
		{
			let hash = header.hash();
			debug!(
				target: "db",
				"Opened blockchain db, fetched {} = {:?} ({})",
				desc,
				hash,
				header.number()
			);
			Ok((hash, *header.number()))
		} else {
			Ok((Default::default(), Zero::zero()))
		}
	};

	let (best_hash, best_number) = load_meta_block("best", meta_keys::BEST_BLOCK)?;
	let (finalized_hash, finalized_number) = load_meta_block("final", meta_keys::FINALIZED_BLOCK)?;
	let (finalized_state_hash, finalized_state_number) =
		load_meta_block("final_state", meta_keys::FINALIZED_STATE)?;
	let finalized_state = if finalized_state_hash != Default::default() {
		Some((finalized_state_hash, finalized_state_number))
	} else {
		None
	};

	Ok(Meta {
		best_hash,
		best_number,
		finalized_hash,
		finalized_number,
		genesis_hash,
		finalized_state,
	})
}

/// Read genesis hash from database.
pub fn read_genesis_hash<Hash: Decode>(
	db: &dyn Database<DbHash>,
) -> sp_blockchain::Result<Option<Hash>> {
	match db.get(COLUMN_META, meta_keys::GENESIS_HASH) {
		Some(h) => match Decode::decode(&mut &h[..]) {
			Ok(h) => Ok(Some(h)),
			Err(err) =>
				Err(sp_blockchain::Error::Backend(format!("Error decoding genesis hash: {}", err))),
		},
		None => Ok(None),
	}
}

impl DatabaseType {
	/// Returns str representation of the type.
	pub fn as_str(&self) -> &'static str {
		match *self {
			DatabaseType::Full => "full",
			DatabaseType::Light => "light",
		}
	}
}

pub(crate) struct JoinInput<'a, 'b>(&'a [u8], &'b [u8]);

pub(crate) fn join_input<'a, 'b>(i1: &'a [u8], i2: &'b [u8]) -> JoinInput<'a, 'b> {
	JoinInput(i1, i2)
}

impl<'a, 'b> codec::Input for JoinInput<'a, 'b> {
	fn remaining_len(&mut self) -> Result<Option<usize>, codec::Error> {
		Ok(Some(self.0.len() + self.1.len()))
	}

	fn read(&mut self, into: &mut [u8]) -> Result<(), codec::Error> {
		let mut read = 0;
		if self.0.len() > 0 {
			read = std::cmp::min(self.0.len(), into.len());
			self.0.read(&mut into[..read])?;
		}
		if read < into.len() {
			self.1.read(&mut into[read..])?;
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{KeepBlocks, TransactionStorageMode};
	use codec::Input;
	use sc_state_db::PruningMode;
	use sp_runtime::testing::{Block as RawBlock, ExtrinsicWrapper};
	use std::path::PathBuf;
	type Block = RawBlock<ExtrinsicWrapper<u32>>;

	#[cfg(any(feature = "with-kvdb-rocksdb", test))]
	#[test]
	fn database_type_subdir_migration() {
		type Block = RawBlock<ExtrinsicWrapper<u64>>;

		fn check_dir_for_db_type(
			db_type: DatabaseType,
			mut source: DatabaseSource,
			db_check_file: &str,
		) {
			let base_path = tempfile::TempDir::new().unwrap();
			let old_db_path = base_path.path().join("chains/dev/db");

			source.set_path(&old_db_path);
			let settings = db_settings(source.clone());

			{
				let db_res = open_database::<Block>(&settings, db_type);
				assert!(db_res.is_ok(), "New database should be created.");
				assert!(old_db_path.join(db_check_file).exists());
				assert!(!old_db_path.join(db_type.as_str()).join("db_version").exists());
			}

			source.set_path(&old_db_path.join(db_type.as_str()));
			let settings = db_settings(source);
			let db_res = open_database::<Block>(&settings, db_type);
			assert!(db_res.is_ok(), "Reopening the db with the same role should work");
			// check if the database dir had been migrated
			assert!(!old_db_path.join(db_check_file).exists());
			assert!(old_db_path.join(db_type.as_str()).join(db_check_file).exists());
		}

		check_dir_for_db_type(
			DatabaseType::Light,
			DatabaseSource::RocksDb { path: PathBuf::new(), cache_size: 128 },
			"db_version",
		);
		check_dir_for_db_type(
			DatabaseType::Full,
			DatabaseSource::RocksDb { path: PathBuf::new(), cache_size: 128 },
			"db_version",
		);

		#[cfg(feature = "with-parity-db")]
		check_dir_for_db_type(
			DatabaseType::Light,
			DatabaseSource::ParityDb { path: PathBuf::new() },
			"metadata",
		);
		#[cfg(feature = "with-parity-db")]
		check_dir_for_db_type(
			DatabaseType::Full,
			DatabaseSource::ParityDb { path: PathBuf::new() },
			"metadata",
		);

		// check failure on reopening with wrong role
		{
			let base_path = tempfile::TempDir::new().unwrap();
			let old_db_path = base_path.path().join("chains/dev/db");

			let source = DatabaseSource::RocksDb { path: old_db_path.clone(), cache_size: 128 };
			let settings = db_settings(source);
			{
				let db_res = open_database::<Block>(&settings, DatabaseType::Full);
				assert!(db_res.is_ok(), "New database should be created.");

				// check if the database dir had been migrated
				assert!(old_db_path.join("db_version").exists());
				assert!(!old_db_path.join("light/db_version").exists());
				assert!(!old_db_path.join("full/db_version").exists());
			}
			let source = DatabaseSource::RocksDb {
				path: old_db_path.join(DatabaseType::Light.as_str()),
				cache_size: 128,
			};
			let settings = db_settings(source);
			let db_res = open_database::<Block>(&settings, DatabaseType::Light);
			assert!(db_res.is_err(), "Opening a light database in full role should fail");
			// assert nothing was changed
			assert!(old_db_path.join("db_version").exists());
			assert!(!old_db_path.join("light/db_version").exists());
			assert!(!old_db_path.join("full/db_version").exists());
		}
	}

	#[test]
	fn number_index_key_doesnt_panic() {
		let id = BlockId::<Block>::Number(72340207214430721);
		match id {
			BlockId::Number(n) => number_index_key(n).expect_err("number should overflow u32"),
			_ => unreachable!(),
		};
	}

	#[test]
	fn database_type_as_str_works() {
		assert_eq!(DatabaseType::Full.as_str(), "full");
		assert_eq!(DatabaseType::Light.as_str(), "light");
	}

	#[test]
	fn join_input_works() {
		let buf1 = [1, 2, 3, 4];
		let buf2 = [5, 6, 7, 8];
		let mut test = [0, 0, 0];
		let mut joined = join_input(buf1.as_ref(), buf2.as_ref());
		assert_eq!(joined.remaining_len().unwrap(), Some(8));

		joined.read(&mut test).unwrap();
		assert_eq!(test, [1, 2, 3]);
		assert_eq!(joined.remaining_len().unwrap(), Some(5));

		joined.read(&mut test).unwrap();
		assert_eq!(test, [4, 5, 6]);
		assert_eq!(joined.remaining_len().unwrap(), Some(2));

		joined.read(&mut test[0..2]).unwrap();
		assert_eq!(test, [7, 8, 6]);
		assert_eq!(joined.remaining_len().unwrap(), Some(0));
	}

	fn db_settings(source: DatabaseSource) -> DatabaseSettings {
		DatabaseSettings {
			state_cache_size: 0,
			state_cache_child_ratio: None,
			state_pruning: PruningMode::ArchiveAll,
			source,
			keep_blocks: KeepBlocks::All,
			transaction_storage: TransactionStorageMode::BlockBody,
		}
	}

	#[cfg(feature = "with-parity-db")]
	#[cfg(any(feature = "with-kvdb-rocksdb", test))]
	#[test]
	fn test_open_database_auto_new() {
		let db_dir = tempfile::TempDir::new().unwrap();
		let db_path = db_dir.path().to_owned();
		let paritydb_path = db_path.join("paritydb");
		let rocksdb_path = db_path.join("rocksdb_path");
		let source = DatabaseSource::Auto {
			paritydb_path: paritydb_path.clone(),
			rocksdb_path: rocksdb_path.clone(),
			cache_size: 128,
		};
		let mut settings = db_settings(source);

		// it should create new auto (paritydb) database
		{
			let db_res = open_database::<Block>(&settings, DatabaseType::Full);
			assert!(db_res.is_ok(), "New database should be created.");
		}

		// it should reopen existing auto (pairtydb) database
		{
			let db_res = open_database::<Block>(&settings, DatabaseType::Full);
			assert!(db_res.is_ok(), "Existing parity database should be reopened");
		}

		// it should fail to open existing auto (pairtydb) database
		{
			settings.source = DatabaseSource::RocksDb { path: rocksdb_path, cache_size: 128 };
			let db_res = open_database::<Block>(&settings, DatabaseType::Full);
			assert!(db_res.is_ok(), "New database should be opened.");
		}

		// it should reopen existing auto (pairtydb) database
		{
			settings.source = DatabaseSource::ParityDb { path: paritydb_path };
			let db_res = open_database::<Block>(&settings, DatabaseType::Full);
			assert!(db_res.is_ok(), "Existing parity database should be reopened");
		}
	}

	#[cfg(feature = "with-parity-db")]
	#[cfg(any(feature = "with-kvdb-rocksdb", test))]
	#[test]
	fn test_open_database_rocksdb_new() {
		let db_dir = tempfile::TempDir::new().unwrap();
		let db_path = db_dir.path().to_owned();
		let paritydb_path = db_path.join("paritydb");
		let rocksdb_path = db_path.join("rocksdb_path");

		let source = DatabaseSource::RocksDb { path: rocksdb_path.clone(), cache_size: 128 };
		let mut settings = db_settings(source);

		// it should create new rocksdb database
		{
			let db_res = open_database::<Block>(&settings, DatabaseType::Full);
			assert!(db_res.is_ok(), "New rocksdb database should be created");
		}

		// it should reopen existing auto (rocksdb) database
		{
			settings.source = DatabaseSource::Auto {
				paritydb_path: paritydb_path.clone(),
				rocksdb_path: rocksdb_path.clone(),
				cache_size: 128,
			};
			let db_res = open_database::<Block>(&settings, DatabaseType::Full);
			assert!(db_res.is_ok(), "Existing rocksdb database should be reopened");
		}

		// it should fail to open existing auto (rocksdb) database
		{
			settings.source = DatabaseSource::ParityDb { path: paritydb_path };
			let db_res = open_database::<Block>(&settings, DatabaseType::Full);
			assert!(db_res.is_ok(), "New paritydb database should be created");
		}

		// it should reopen existing auto (pairtydb) database
		{
			settings.source = DatabaseSource::RocksDb { path: rocksdb_path, cache_size: 128 };
			let db_res = open_database::<Block>(&settings, DatabaseType::Full);
			assert!(db_res.is_ok(), "Existing rocksdb database should be reopened");
		}
	}

	#[cfg(feature = "with-parity-db")]
	#[cfg(any(feature = "with-kvdb-rocksdb", test))]
	#[test]
	fn test_open_database_paritydb_new() {
		let db_dir = tempfile::TempDir::new().unwrap();
		let db_path = db_dir.path().to_owned();
		let paritydb_path = db_path.join("paritydb");
		let rocksdb_path = db_path.join("rocksdb_path");

		let source = DatabaseSource::ParityDb { path: paritydb_path.clone() };
		let mut settings = db_settings(source);

		// it should create new paritydb database
		{
			let db_res = open_database::<Block>(&settings, DatabaseType::Full);
			assert!(db_res.is_ok(), "New database should be created.");
		}

		// it should reopen existing pairtydb database
		{
			let db_res = open_database::<Block>(&settings, DatabaseType::Full);
			assert!(db_res.is_ok(), "Existing parity database should be reopened");
		}

		// it should fail to open existing pairtydb database
		{
			settings.source =
				DatabaseSource::RocksDb { path: rocksdb_path.clone(), cache_size: 128 };
			let db_res = open_database::<Block>(&settings, DatabaseType::Full);
			assert!(db_res.is_ok(), "New rocksdb database should be created");
		}

		// it should reopen existing auto (pairtydb) database
		{
			settings.source = DatabaseSource::Auto { paritydb_path, rocksdb_path, cache_size: 128 };
			let db_res = open_database::<Block>(&settings, DatabaseType::Full);
			assert!(db_res.is_ok(), "Existing parity database should be reopened");
		}
	}
}
