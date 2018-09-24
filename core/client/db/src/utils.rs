// Copyright 2017 Parity Technologies (UK) Ltd.
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
use std::io;

use kvdb::{KeyValueDB, DBTransaction};
use kvdb_rocksdb::{Database, DatabaseConfig};

use client;
use codec::Decode;
use trie::DBValue;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{As, Block as BlockT, Header as HeaderT, Zero};
use DatabaseSettings;

/// Number of columns in the db. Must be the same for both full && light dbs.
/// Otherwise RocksDb will fail to open database && check its type.
pub const NUM_COLUMNS: u32 = 8;
/// Meta column. The set of keys in the column is shared by full && light storages.
pub const COLUMN_META: Option<u32> = Some(0);

/// Keys of entries in COLUMN_META.
pub mod meta_keys {
	/// Type of storage (full or light).
	pub const TYPE: &[u8; 4] = b"type";
	/// Best block key.
	pub const BEST_BLOCK: &[u8; 4] = b"best";
	/// Last finalized block key.
	pub const FINALIZED_BLOCK: &[u8; 5] = b"final";
	/// Best authorities block key.
	pub const BEST_AUTHORITIES: &[u8; 4] = b"auth";
	/// Genesis block hash.
	pub const GENESIS_HASH: &[u8; 3] = b"gen";
}

/// Database metadata.
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
pub type BlockLookupKey = [u8; 4];

/// Convert block number into lookup key (LE representation).
pub fn number_to_lookup_key<N>(n: N) -> BlockLookupKey where N: As<u64> {
	let n: u64 = n.as_();
	assert!(n & 0xffffffff00000000 == 0);

	[
		(n >> 24) as u8,
		((n >> 16) & 0xff) as u8,
		((n >> 8) & 0xff) as u8,
		(n & 0xff) as u8
	]
}

/// Convert block lookup key into block number.
pub fn lookup_key_to_number<N>(key: &[u8]) -> client::error::Result<N> where N: As<u64> {
	match key.len() {
		4 => Ok((key[0] as u64) << 24
			| (key[1] as u64) << 16
			| (key[2] as u64) << 8
			| (key[3] as u64)).map(As::sa),
		_ => Err(client::error::ErrorKind::Backend("Invalid block key".into()).into()),
	}
}

/// Maps database error to client error
pub fn db_err(err: io::Error) -> client::error::Error {
	use std::error::Error;
	client::error::ErrorKind::Backend(err.description().into()).into()
}

/// Open RocksDB database.
pub fn open_database(config: &DatabaseSettings, db_type: &str) -> client::error::Result<Arc<KeyValueDB>> {
	let mut db_config = DatabaseConfig::with_columns(Some(NUM_COLUMNS));
	db_config.memory_budget = config.cache_size;
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

/// Convert block id to block key, looking up canonical hash by number from DB as necessary.
pub fn read_id<Block>(db: &KeyValueDB, col_index: Option<u32>, id: BlockId<Block>) -> Result<Option<Block::Hash>, client::error::Error>
	where
		Block: BlockT,
{
	match id {
		BlockId::Hash(h) => Ok(Some(h)),
		BlockId::Number(n) => db.get(col_index, &number_to_lookup_key(n)).map(|v|
			v.map(|v| {
				let mut h = <Block::Hash>::default();
				{
					let h = h.as_mut();
					let len = ::std::cmp::min(v.len(), h.len());
					h.as_mut().copy_from_slice(&v[..len]);
				}
				h
			})
		).map_err(db_err),
	}
}

/// Read database column entry for the given block.
pub fn read_db<Block>(db: &KeyValueDB, col_index: Option<u32>, col: Option<u32>, id: BlockId<Block>) -> client::error::Result<Option<DBValue>>
	where
		Block: BlockT,
{
	read_id(db, col_index, id).and_then(|key| match key {
		Some(key) => db.get(col, key.as_ref()).map_err(db_err),
		None => Ok(None),
	})
}

/// Read a header from the database.
pub fn read_header<Block: BlockT>(
	db: &KeyValueDB,
	col_index: Option<u32>,
	col: Option<u32>,
	id: BlockId<Block>,
) -> client::error::Result<Option<Block::Header>> {
	match read_db(db, col_index, col, id)? {
		Some(header) => match Block::Header::decode(&mut &header[..]) {
			Some(header) => Ok(Some(header)),
			None => return Err(
				client::error::ErrorKind::Backend("Error decoding header".into()).into()
			),
		}
		None => Ok(None),
	}
}

/// Read meta from the database.
pub fn read_meta<Block>(db: &KeyValueDB, col_header: Option<u32>) -> Result<
	Meta<<<Block as BlockT>::Header as HeaderT>::Number, Block::Hash>,
	client::error::Error,
>
	where
		Block: BlockT,
{
	let genesis_hash: Block::Hash = match db.get(COLUMN_META, meta_keys::GENESIS_HASH).map_err(db_err)? {
		Some(h) => match Decode::decode(&mut &h[..]) {
			Some(h) => h,
			None => return Err(client::error::ErrorKind::Backend("Error decoding genesis hash".into()).into()),
		},
		None => return Ok(Meta {
			best_hash: Default::default(),
			best_number: Zero::zero(),
			finalized_hash: Default::default(),
			finalized_number: Zero::zero(),
			genesis_hash: Default::default(),
		}),
	};

	let load_meta_block = |desc, key| -> Result<_, client::error::Error> {
		if let Some(Some(header)) = db.get(COLUMN_META, key).and_then(|id|
			match id {
				Some(id) => db.get(col_header, &id).map(|h| h.map(|b| Block::Header::decode(&mut &b[..]))),
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

/// An entry in a tree route.
#[derive(Debug)]
pub struct RouteEntry<Block: BlockT> {
	/// The number of the block.
	pub number: <Block::Header as HeaderT>::Number,
	/// The hash of the block.
	pub hash: Block::Hash,
}

/// A tree-route from one block to another in the chain.
///
/// All blocks prior to the pivot in the deque is the reverse-order unique ancestry
/// of the first block, the block at the pivot index is the common ancestor,
/// and all blocks after the pivot is the ancestry of the second block, in
/// order.
///
/// The ancestry sets will include the given blocks, and thus the tree-route is
/// never empty.
///
/// ```ignore
/// Tree route from R1 to E2. Retracted is [R1, R2, R3], Common is C, enacted [E1, E2]
///   <- R3 <- R2 <- R1
///  /
/// C
///  \-> E1 -> E2
/// ```
///
/// ```ignore
/// Tree route from C to E2. Retracted empty. Common is C, enacted [E1, E2]
/// C -> E1 -> E2
/// ```
#[derive(Debug)]
pub struct TreeRoute<Block: BlockT> {
	route: Vec<RouteEntry<Block>>,
	pivot: usize,
}

impl<Block: BlockT> TreeRoute<Block> {
	/// Get an iterator of all retracted blocks in reverse order (towards common ancestor)
	pub fn retracted(&self) -> impl Iterator<Item=&RouteEntry<Block>> {
		self.route.iter().take(self.pivot)
	}

	/// Get the common ancestor block. This might be one of the two blocks of the
	/// route.
	#[allow(unused)]
	pub fn common_block(&self) -> &RouteEntry<Block> {
		self.route.get(self.pivot).expect("tree-routes are computed between blocks; \
			which are included in the route; \
			thus it is never empty; qed")
	}

	/// Get an iterator of enacted blocks (descendents of the common ancestor)
	pub fn enacted(&self) -> impl Iterator<Item=&RouteEntry<Block>> {
		self.route.iter().skip(self.pivot + 1)
	}
}

/// Compute a tree-route between two blocks. See tree-route docs for more details.
pub fn tree_route<Block: BlockT>(
	db: &KeyValueDB,
	col_header: Option<u32>,
	from: Block::Hash,
	to: Block::Hash,
) -> Result<TreeRoute<Block>, client::error::Error> {
	use runtime_primitives::traits::Header;

	let load_header = |hash: &Block::Hash| {
		match db.get(col_header, hash.as_ref()).map_err(db_err) {
			Ok(Some(b)) => match <Block::Header>::decode(&mut &b[..]) {
				Some(hdr) => Ok(hdr),
				None => Err(client::error::ErrorKind::Backend("Error decoding header".into()).into()),
			}
			Ok(None) => Err(client::error::ErrorKind::UnknownBlock(format!("Unknown block {:?}", hash)).into()),
			Err(e) => Err(e),
		}
	};

	let mut from = load_header(&from)?;
	let mut to = load_header(&to)?;

	let mut from_branch = Vec::new();
	let mut to_branch = Vec::new();

	while to.number() > from.number() {
		to_branch.push(RouteEntry {
			number: to.number().clone(),
			hash: to.hash(),
		});

		to = load_header(to.parent_hash())?;
	}

	while from.number() > to.number() {
		from_branch.push(RouteEntry {
			number: from.number().clone(),
			hash: from.hash(),
		});
		from = load_header(from.parent_hash())?;
	}

	// numbers are equal now. walk backwards until the block is the same

	while to != from {
		to_branch.push(RouteEntry {
			number: to.number().clone(),
			hash: to.hash(),
		});
		to = load_header(to.parent_hash())?;

		from_branch.push(RouteEntry {
			number: from.number().clone(),
			hash: from.hash(),
		});
		from = load_header(from.parent_hash())?;
	}

	// add the pivot block. and append the reversed to-branch (note that it's reverse order originalls)
	let pivot = from_branch.len();
	from_branch.push(RouteEntry {
		number: to.number().clone(),
		hash: to.hash(),
	});
	from_branch.extend(to_branch.into_iter().rev());

	Ok(TreeRoute {
		route: from_branch,
		pivot,
	})
}
