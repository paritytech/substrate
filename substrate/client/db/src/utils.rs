// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Db-based backend utility structures and functions, used by both
//! full and light storages.

use std::sync::Arc;

use kvdb::{self, KeyValueDB, DBTransaction};
use kvdb_rocksdb::{Database, DatabaseConfig};

use client;
use codec::Decode;
use hashdb::DBValue;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{As, Block as BlockT, Header as HeaderT, Hash, HashFor, Zero};
use DatabaseSettings;

/// Number of columns in the db. Must be the same for both full && light dbs.
/// Otherwise RocksDb will fail to open database && check its type.
pub const NUM_COLUMNS: u32 = 7;
/// Meta column. Thes set of keys in the column is shared by full && light storages.
pub const COLUMN_META: Option<u32> = Some(0);

/// Keys of entries in COLUMN_META.
pub mod meta_keys {
	/// Type of storage (full or light).
	pub const TYPE: &[u8; 4] = b"type";
	/// Best block key.
	pub const BEST_BLOCK: &[u8; 4] = b"best";
	/// Best authorities block key.
	pub const BEST_AUTHORITIES: &[u8; 4] = b"auth";
}

/// Database metadata.
pub struct Meta<N, H> {
	/// Hash of the best known block.
	pub best_hash: H,
	/// Number of the best known block.
	pub best_number: N,
	/// Hash of the genesis block.
	pub genesis_hash: H,
}

/// Type of block key in the database (LE block number).
pub type BlockKey = [u8; 4];

/// Convert block number into key (LE representation).
pub fn number_to_db_key<N>(n: N) -> BlockKey where N: As<u64> {
	let n: u64 = n.as_();
	assert!(n & 0xffffffff00000000 == 0);

	[
		(n >> 24) as u8,
		((n >> 16) & 0xff) as u8,
		((n >> 8) & 0xff) as u8,
		(n & 0xff) as u8
	]
}

/// Convert block key into block number.
pub fn db_key_to_number<N>(key: &[u8]) -> client::error::Result<N> where N: As<u64> {
	match key.len() {
		4 => Ok((key[0] as u64) << 24
			| (key[1] as u64) << 16
			| (key[2] as u64) << 8
			| (key[3] as u64)).map(As::sa),
		_ => Err(client::error::ErrorKind::Backend("Invalid block key".into()).into()),
	}
}

/// Maps database error to client error
pub fn db_err(err: kvdb::Error) -> client::error::Error {
	use std::error::Error;
	match err.kind() {
		&kvdb::ErrorKind::Io(ref err) => client::error::ErrorKind::Backend(err.description().into()).into(),
		&kvdb::ErrorKind::Msg(ref m) => client::error::ErrorKind::Backend(m.clone()).into(),
		_ => client::error::ErrorKind::Backend("Unknown backend error".into()).into(),
	}
}

/// Open RocksDB database.
pub fn open_database(config: &DatabaseSettings, db_type: &str) -> client::error::Result<Arc<KeyValueDB>> {
	let mut db_config = DatabaseConfig::with_columns(Some(NUM_COLUMNS));
	db_config.memory_budget = config.cache_size;
	db_config.wal = true;
	let path = config.path.to_str().ok_or_else(|| client::error::ErrorKind::Backend("Invalid database path".into()))?;
	let db = Database::open(&db_config, &path).map_err(db_err)?;

	// check database type
	match db.get(COLUMN_META, meta_keys::TYPE).map_err(db_err)? {
		Some(stored_type) => {
			if db_type.as_bytes() != &*stored_type {
				return Err(client::error::ErrorKind::Backend(
					format!("Unexpected database type. Expected: {}", db_type)).into());
			}
		},
		None => {
			let mut transaction = DBTransaction::new();
			transaction.put(COLUMN_META, meta_keys::TYPE, db_type.as_bytes());
			db.write(transaction).map_err(db_err)?;
		},
	}

	Ok(Arc::new(db))
}

/// Convert block id to block key, reading number from db if required.
pub fn read_id<Block>(db: &KeyValueDB, col_index: Option<u32>, id: BlockId<Block>) -> Result<Option<BlockKey>, client::error::Error>
	where
		Block: BlockT,
{
	match id {
		BlockId::Hash(h) => db.get(col_index, h.as_ref())
			.map(|v| v.map(|v| {
				let mut key: [u8; 4] = [0; 4];
				key.copy_from_slice(&v);
				key
			})).map_err(db_err),
		BlockId::Number(n) => Ok(Some(number_to_db_key(n))),
	}
}

/// Read database column entry for the given block.
pub fn read_db<Block>(db: &KeyValueDB, col_index: Option<u32>, col: Option<u32>, id: BlockId<Block>) -> client::error::Result<Option<DBValue>>
	where
		Block: BlockT,
{
	read_id(db, col_index, id).and_then(|key| match key {
		Some(key) => db.get(col, &key).map_err(db_err),
		None => Ok(None),
	})
}

/// Read meta from the database.
pub fn read_meta<Block>(db: &KeyValueDB, col_header: Option<u32>) -> Result<Meta<<<Block as BlockT>::Header as HeaderT>::Number, Block::Hash>, client::error::Error>
	where
		Block: BlockT,
{
	let genesis_number = <<Block as BlockT>::Header as HeaderT>::Number::zero();
	let (best_hash, best_number) = if let Some(Some(header)) = db.get(COLUMN_META, meta_keys::BEST_BLOCK).and_then(|id|
		match id {
			Some(id) => db.get(col_header, &id).map(|h| h.map(|b| Block::Header::decode(&mut &b[..]))),
			None => Ok(None),
		}).map_err(db_err)?
	{
		let hash = header.hash();
		debug!("DB Opened blockchain db, best {:?} ({})", hash, header.number());
		(hash, *header.number())
	} else {
		(Default::default(), genesis_number)
	};

	let genesis_hash = db.get(col_header, &number_to_db_key(genesis_number))
		.map_err(db_err)?
		.map(|raw| HashFor::<Block>::hash(&raw[..]))
		.unwrap_or_default()
		.into();

	Ok(Meta {
		best_hash,
		best_number,
		genesis_hash,
	})
}
