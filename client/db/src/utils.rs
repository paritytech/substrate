// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Db-based backend utility structures and functions, used by both
//! full and light storages.

use std::sync::Arc;
use std::{io, convert::TryInto};

use kvdb::{KeyValueDB, DBTransaction};
#[cfg(any(feature = "kvdb-rocksdb", test))]
use kvdb_rocksdb::{Database, DatabaseConfig};
use log::debug;

use codec::Decode;
use sp_trie::DBValue;
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{
	Block as BlockT, Header as HeaderT, Zero,
	UniqueSaturatedFrom, UniqueSaturatedInto,
};
use crate::{DatabaseSettings, DatabaseSettingsSrc};

/// Number of columns in the db. Must be the same for both full && light dbs.
/// Otherwise RocksDb will fail to open database && check its type.
pub const NUM_COLUMNS: u32 = 11;
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
	let n = n.try_into().map_err(|_|
		sp_blockchain::Error::Backend("Block number cannot be converted to u32".into())
	)?;

	Ok([
		(n >> 24) as u8,
		((n >> 16) & 0xff) as u8,
		((n >> 8) & 0xff) as u8,
		(n & 0xff) as u8
	])
}

/// Convert number and hash into long lookup key for blocks that are
/// not in the canonical chain.
pub fn number_and_hash_to_lookup_key<N, H>(
	number: N,
	hash: H,
) -> sp_blockchain::Result<Vec<u8>>	where
	N: TryInto<u32>,
	H: AsRef<[u8]>,
{
	let mut lookup_key = number_index_key(number)?.to_vec();
	lookup_key.extend_from_slice(hash.as_ref());
	Ok(lookup_key)
}

/// Convert block lookup key into block number.
/// all block lookup keys start with the block number.
pub fn lookup_key_to_number<N>(key: &[u8]) -> sp_blockchain::Result<N> where
	N: From<u32>
{
	if key.len() < 4 {
		return Err(sp_blockchain::Error::Backend("Invalid block key".into()));
	}
	Ok((key[0] as u32) << 24
		| (key[1] as u32) << 16
		| (key[2] as u32) << 8
		| (key[3] as u32)).map(Into::into)
}

/// Delete number to hash mapping in DB transaction.
pub fn remove_number_to_key_mapping<N: TryInto<u32>>(
	transaction: &mut DBTransaction,
	key_lookup_col: u32,
	number: N,
) -> sp_blockchain::Result<()> {
	transaction.delete(key_lookup_col, number_index_key(number)?.as_ref());
	Ok(())
}

/// Remove key mappings.
pub fn remove_key_mappings<N: TryInto<u32>, H: AsRef<[u8]>>(
	transaction: &mut DBTransaction,
	key_lookup_col: u32,
	number: N,
	hash: H,
) -> sp_blockchain::Result<()> {
	remove_number_to_key_mapping(transaction, key_lookup_col, number)?;
	transaction.delete(key_lookup_col, hash.as_ref());
	Ok(())
}

/// Place a number mapping into the database. This maps number to current perceived
/// block hash at that position.
pub fn insert_number_to_key_mapping<N: TryInto<u32> + Clone, H: AsRef<[u8]>>(
	transaction: &mut DBTransaction,
	key_lookup_col: u32,
	number: N,
	hash: H,
) -> sp_blockchain::Result<()> {
	transaction.put_vec(
		key_lookup_col,
		number_index_key(number.clone())?.as_ref(),
		number_and_hash_to_lookup_key(number, hash)?,
	);
	Ok(())
}

/// Insert a hash to key mapping in the database.
pub fn insert_hash_to_key_mapping<N: TryInto<u32>, H: AsRef<[u8]> + Clone>(
	transaction: &mut DBTransaction,
	key_lookup_col: u32,
	number: N,
	hash: H,
) -> sp_blockchain::Result<()> {
	transaction.put_vec(
		key_lookup_col,
		hash.clone().as_ref(),
		number_and_hash_to_lookup_key(number, hash)?,
	);
	Ok(())
}

/// Convert block id to block lookup key.
/// block lookup key is the DB-key header, block and justification are stored under.
/// looks up lookup key by hash from DB as necessary.
pub fn block_id_to_lookup_key<Block>(
	db: &dyn KeyValueDB,
	key_lookup_col: u32,
	id: BlockId<Block>
) -> Result<Option<Vec<u8>>, sp_blockchain::Error> where
	Block: BlockT,
	::sp_runtime::traits::NumberFor<Block>: UniqueSaturatedFrom<u64> + UniqueSaturatedInto<u64>,
{
	let res = match id {
		BlockId::Number(n) => db.get(
			key_lookup_col,
			number_index_key(n)?.as_ref(),
		),
		BlockId::Hash(h) => db.get(key_lookup_col, h.as_ref()),
	};

	res.map_err(db_err)
}

/// Maps database error to client error
pub fn db_err(err: io::Error) -> sp_blockchain::Error {
	sp_blockchain::Error::Backend(format!("{}", err))
}

/// Open RocksDB database.
pub fn open_database<Block: BlockT>(
	config: &DatabaseSettings,
	db_type: DatabaseType,
) -> sp_blockchain::Result<Arc<dyn KeyValueDB>> {
	let db: Arc<dyn KeyValueDB> = match &config.source {
		#[cfg(any(feature = "kvdb-rocksdb", test))]
		DatabaseSettingsSrc::Path { path, cache_size } => {
			// first upgrade database to required version
			crate::upgrade::upgrade_db::<Block>(&path, db_type)?;

			// and now open database assuming that it has the latest version
			let mut db_config = DatabaseConfig::with_columns(NUM_COLUMNS);

			if let Some(cache_size) = cache_size {
				let state_col_budget = (*cache_size as f64 * 0.9) as usize;
				let other_col_budget = (cache_size - state_col_budget) / (NUM_COLUMNS as usize - 1);

				let mut memory_budget = std::collections::HashMap::new();
				for i in 0..NUM_COLUMNS {
					if i == crate::columns::STATE {
						memory_budget.insert(i, state_col_budget);
					} else {
						memory_budget.insert(i, other_col_budget);
					}
				}

				db_config.memory_budget = memory_budget;
			}
			let path = path.to_str()
				.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;
			Arc::new(Database::open(&db_config, &path).map_err(db_err)?)
		},
		#[cfg(not(any(feature = "kvdb-rocksdb", test)))]
		DatabaseSettingsSrc::Path { .. } => {
			let msg = "Try to open RocksDB database with RocksDB disabled".into();
			return Err(sp_blockchain::Error::Backend(msg));
		},
		DatabaseSettingsSrc::Custom(db) => db.clone(),
	};

	check_database_type(&*db, db_type)?;

	Ok(db)
}

/// Check database type.
pub fn check_database_type(db: &dyn KeyValueDB, db_type: DatabaseType) -> sp_blockchain::Result<()> {
	match db.get(COLUMN_META, meta_keys::TYPE).map_err(db_err)? {
		Some(stored_type) => {
			if db_type.as_str().as_bytes() != &*stored_type {
				return Err(sp_blockchain::Error::Backend(
					format!("Unexpected database type. Expected: {}", db_type.as_str())).into());
			}
		},
		None => {
			let mut transaction = DBTransaction::new();
			transaction.put(COLUMN_META, meta_keys::TYPE, db_type.as_str().as_bytes());
			db.write(transaction).map_err(db_err)?;
		},
	}

	Ok(())
}

/// Read database column entry for the given block.
pub fn read_db<Block>(
	db: &dyn KeyValueDB,
	col_index: u32,
	col: u32,
	id: BlockId<Block>
) -> sp_blockchain::Result<Option<DBValue>>
	where
		Block: BlockT,
{
	block_id_to_lookup_key(db, col_index, id).and_then(|key| match key {
		Some(key) => db.get(col, key.as_ref()).map_err(db_err),
		None => Ok(None),
	})
}

/// Read a header from the database.
pub fn read_header<Block: BlockT>(
	db: &dyn KeyValueDB,
	col_index: u32,
	col: u32,
	id: BlockId<Block>,
) -> sp_blockchain::Result<Option<Block::Header>> {
	match read_db(db, col_index, col, id)? {
		Some(header) => match Block::Header::decode(&mut &header[..]) {
			Ok(header) => Ok(Some(header)),
			Err(_) => return Err(
				sp_blockchain::Error::Backend("Error decoding header".into())
			),
		}
		None => Ok(None),
	}
}

/// Required header from the database.
pub fn require_header<Block: BlockT>(
	db: &dyn KeyValueDB,
	col_index: u32,
	col: u32,
	id: BlockId<Block>,
) -> sp_blockchain::Result<Block::Header> {
	read_header(db, col_index, col, id)
		.and_then(|header| header.ok_or_else(|| sp_blockchain::Error::UnknownBlock(format!("{}", id))))
}

/// Read meta from the database.
pub fn read_meta<Block>(db: &dyn KeyValueDB, col_header: u32) -> Result<
	Meta<<<Block as BlockT>::Header as HeaderT>::Number, Block::Hash>,
	sp_blockchain::Error,
>
	where
		Block: BlockT,
{
	let genesis_hash: Block::Hash = match read_genesis_hash(db)? {
		Some(genesis_hash) => genesis_hash,
		None => return Ok(Meta {
			best_hash: Default::default(),
			best_number: Zero::zero(),
			finalized_hash: Default::default(),
			finalized_number: Zero::zero(),
			genesis_hash: Default::default(),
		}),
	};

	let load_meta_block = |desc, key| -> Result<_, sp_blockchain::Error> {
		if let Some(Some(header)) = db.get(COLUMN_META, key).and_then(|id|
			match id {
				Some(id) => db.get(col_header, &id).map(|h| h.map(|b| Block::Header::decode(&mut &b[..]).ok())),
				None => Ok(None),
			}).map_err(db_err)?
		{
			let hash = header.hash();
			debug!("DB Opened blockchain db, fetched {} = {:?} ({})", desc, hash, header.number());
			Ok((hash, *header.number()))
		} else {
			Ok((genesis_hash.clone(), Zero::zero()))
		}
	};

	let (best_hash, best_number) = load_meta_block("best", meta_keys::BEST_BLOCK)?;
	let (finalized_hash, finalized_number) = load_meta_block("final", meta_keys::FINALIZED_BLOCK)?;

	Ok(Meta {
		best_hash,
		best_number,
		finalized_hash,
		finalized_number,
		genesis_hash,
	})
}

/// Read genesis hash from database.
pub fn read_genesis_hash<Hash: Decode>(db: &dyn KeyValueDB) -> sp_blockchain::Result<Option<Hash>> {
	match db.get(COLUMN_META, meta_keys::GENESIS_HASH).map_err(db_err)? {
		Some(h) => match Decode::decode(&mut &h[..]) {
			Ok(h) => Ok(Some(h)),
			Err(err) => Err(sp_blockchain::Error::Backend(
				format!("Error decoding genesis hash: {}", err)
			)),
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

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::testing::{Block as RawBlock, ExtrinsicWrapper};
	type Block = RawBlock<ExtrinsicWrapper<u32>>;

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
}
