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

//! RocksDB-based light client blockchain storage.

use std::sync::Arc;
use parking_lot::RwLock;

use kvdb::{KeyValueDB, DBTransaction};

use client::blockchain::{BlockStatus, Cache as BlockchainCache,
	HeaderBackend as BlockchainHeaderBackend, Info as BlockchainInfo};
use client::error::{ErrorKind as ClientErrorKind, Result as ClientResult};
use client::light::blockchain::Storage as LightBlockchainStorage;
use codec::{Decode, Encode};
use primitives::AuthorityId;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Hash, HashFor, Zero, As};
use cache::DbCache;
use utils::{meta_keys, Meta, db_err, number_to_db_key, open_database, read_db, read_id, read_meta};
use DatabaseSettings;

pub(crate) mod columns {
	pub const META: Option<u32> = ::utils::COLUMN_META;
	pub const BLOCK_INDEX: Option<u32> = Some(1);
	pub const HEADER: Option<u32> = Some(2);
	pub const AUTHORITIES: Option<u32> = Some(3);
}

/// Keep authorities for last 'AUTHORITIES_ENTRIES_TO_KEEP' blocks.
pub(crate) const AUTHORITIES_ENTRIES_TO_KEEP: u64 = 2048;

/// Light blockchain storage. Stores most recent headers + CHTs for older headers.
pub struct LightStorage<Block: BlockT> {
	db: Arc<KeyValueDB>,
	meta: RwLock<Meta<<<Block as BlockT>::Header as HeaderT>::Number, Block::Hash>>,
	cache: DbCache<Block>,
}

#[derive(Clone, PartialEq, Debug)]
struct BestAuthorities<N> {
	/// first block, when this set became actual
	valid_from: N,
	/// None means that we do not know the set starting from `valid_from` block
	authorities: Option<Vec<AuthorityId>>,
}

impl<Block> LightStorage<Block>
	where
		Block: BlockT,
{
	/// Create new storage with given settings.
	pub fn new(config: DatabaseSettings) -> ClientResult<Self> {
		let db = open_database(&config, "light")?;

		Self::from_kvdb(db as Arc<_>)
	}

	#[cfg(test)]
	pub(crate) fn new_test() -> Self {
		use utils::NUM_COLUMNS;

		let db = Arc::new(::kvdb_memorydb::create(NUM_COLUMNS));

		Self::from_kvdb(db as Arc<_>).expect("failed to create test-db")
	}

	fn from_kvdb(db: Arc<KeyValueDB>) -> ClientResult<Self> {
		let cache = DbCache::new(db.clone(), columns::BLOCK_INDEX, columns::AUTHORITIES)?;
		let meta = RwLock::new(read_meta::<Block>(&*db, columns::HEADER)?);

		Ok(LightStorage {
			db,
			meta,
			cache,
		})
	}

	#[cfg(test)]
	pub(crate) fn db(&self) -> &Arc<KeyValueDB> {
		&self.db
	}

	#[cfg(test)]
	pub(crate) fn cache(&self) -> &DbCache<Block> {
		&self.cache
	}

	fn update_meta(&self, hash: Block::Hash, number: <<Block as BlockT>::Header as HeaderT>::Number, is_best: bool) {
		if is_best {
			let mut meta = self.meta.write();
			if number == <<Block as BlockT>::Header as HeaderT>::Number::zero() {
				meta.genesis_hash = hash;
			}

			meta.best_number = number;
			meta.best_hash = hash;
		}
	}
}

impl<Block> BlockchainHeaderBackend<Block> for LightStorage<Block>
	where
		Block: BlockT,
{
	fn header(&self, id: BlockId<Block>) -> ClientResult<Option<Block::Header>> {
		match read_db(&*self.db, columns::BLOCK_INDEX, columns::HEADER, id)? {
			Some(header) => match Block::Header::decode(&mut &header[..]) {
				Some(header) => Ok(Some(header)),
				None => return Err(ClientErrorKind::Backend("Error decoding header".into()).into()),
			}
			None => Ok(None),
		}
	}

	fn info(&self) -> ClientResult<BlockchainInfo<Block>> {
		let meta = self.meta.read();
		Ok(BlockchainInfo {
			best_hash: meta.best_hash,
			best_number: meta.best_number,
			genesis_hash: meta.genesis_hash,
		})
	}

	fn status(&self, id: BlockId<Block>) -> ClientResult<BlockStatus> {
		let exists = match id {
			BlockId::Hash(_) => read_id(&*self.db, columns::BLOCK_INDEX, id)?.is_some(),
			BlockId::Number(n) => n <= self.meta.read().best_number,
		};
		match exists {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	fn hash(&self, number: <<Block as BlockT>::Header as HeaderT>::Number) -> ClientResult<Option<Block::Hash>> {
		read_db::<Block>(&*self.db, columns::BLOCK_INDEX, columns::HEADER, BlockId::Number(number)).map(|x|
			x.map(|raw| HashFor::<Block>::hash(&raw[..])).map(Into::into)
		)
	}
}

impl<Block> LightBlockchainStorage<Block> for LightStorage<Block>
	where
		Block: BlockT,
{
	fn import_header(&self, is_new_best: bool, header: Block::Header, authorities: Option<Vec<AuthorityId>>) -> ClientResult<()> {
		let mut transaction = DBTransaction::new();

		let hash = header.hash();
		let number = *header.number();
		let key = number_to_db_key(number);

		transaction.put(columns::HEADER, &key, &header.encode());
		transaction.put(columns::BLOCK_INDEX, hash.as_ref(), &key);

		let best_authorities = if is_new_best {
			transaction.put(columns::META, meta_keys::BEST_BLOCK, &key);

			// cache authorities for previous block
			let number: u64 = number.as_();
			let previous_number = number.checked_sub(1);
			let best_authorities = previous_number
				.and_then(|previous_number| self.cache.authorities_at_cache()
					.commit_best_entry(&mut transaction, As::sa(previous_number), authorities));

			// prune authorities from 'ancient' blocks
			if let Some(ancient_number) = number.checked_sub(AUTHORITIES_ENTRIES_TO_KEEP) {
				self.cache.authorities_at_cache().prune_entries(&mut transaction, As::sa(ancient_number))?;
			}

			best_authorities
		} else {
			None
		};

		debug!("Light DB Commit {:?} ({})", hash, number);
		self.db.write(transaction).map_err(db_err)?;
		self.update_meta(hash, number, is_new_best);
		if let Some(best_authorities) = best_authorities {
			self.cache.authorities_at_cache().update_best_entry(Some(best_authorities));
		}

		Ok(())
	}

	fn cache(&self) -> Option<&BlockchainCache<Block>> {
		Some(&self.cache)
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use runtime_primitives::testing::{H256 as Hash, Header, Block as RawBlock};
	use super::*;

	type Block = RawBlock<u32>;

	pub fn insert_block(
		db: &LightStorage<Block>,
		parent: &Hash,
		number: u64,
		authorities: Option<Vec<AuthorityId>>
	) -> Hash {
		let header = Header {
			number: number.into(),
			parent_hash: *parent,
			state_root: Default::default(),
			digest: Default::default(),
			extrinsics_root: Default::default(),
		};

		let hash = header.hash();
		db.import_header(true, header, authorities).unwrap();
		hash
	}

	#[test]
	fn returns_known_header() {
		let db = LightStorage::new_test();
		let known_hash = insert_block(&db, &Default::default(), 0, None);
		let header_by_hash = db.header(BlockId::Hash(known_hash)).unwrap().unwrap();
		let header_by_number = db.header(BlockId::Number(0)).unwrap().unwrap();
		assert_eq!(header_by_hash, header_by_number);
	}

	#[test]
	fn does_not_return_unknown_header() {
		let db = LightStorage::<Block>::new_test();
		assert!(db.header(BlockId::Hash(1.into())).unwrap().is_none());
		assert!(db.header(BlockId::Number(0)).unwrap().is_none());
	}

	#[test]
	fn returns_info() {
		let db = LightStorage::new_test();
		let genesis_hash = insert_block(&db, &Default::default(), 0, None);
		let info = db.info().unwrap();
		assert_eq!(info.best_hash, genesis_hash);
		assert_eq!(info.best_number, 0);
		assert_eq!(info.genesis_hash, genesis_hash);
		let best_hash = insert_block(&db, &genesis_hash, 1, None);
		let info = db.info().unwrap();
		assert_eq!(info.best_hash, best_hash);
		assert_eq!(info.best_number, 1);
		assert_eq!(info.genesis_hash, genesis_hash);
	}

	#[test]
	fn returns_block_status() {
		let db = LightStorage::new_test();
		let genesis_hash = insert_block(&db, &Default::default(), 0, None);
		assert_eq!(db.status(BlockId::Hash(genesis_hash)).unwrap(), BlockStatus::InChain);
		assert_eq!(db.status(BlockId::Number(0)).unwrap(), BlockStatus::InChain);
		assert_eq!(db.status(BlockId::Hash(1.into())).unwrap(), BlockStatus::Unknown);
		assert_eq!(db.status(BlockId::Number(1)).unwrap(), BlockStatus::Unknown);
	}

	#[test]
	fn returns_block_hash() {
		let db = LightStorage::new_test();
		let genesis_hash = insert_block(&db, &Default::default(), 0, None);
		assert_eq!(db.hash(0).unwrap(), Some(genesis_hash));
		assert_eq!(db.hash(1).unwrap(), None);
	}

	#[test]
	fn import_header_works() {
		let db = LightStorage::new_test();

		let genesis_hash = insert_block(&db, &Default::default(), 0, None);
		assert_eq!(db.db.iter(columns::HEADER).count(), 1);
		assert_eq!(db.db.iter(columns::BLOCK_INDEX).count(), 1);

		let _ = insert_block(&db, &genesis_hash, 1, None);
		assert_eq!(db.db.iter(columns::HEADER).count(), 2);
		assert_eq!(db.db.iter(columns::BLOCK_INDEX).count(), 2);
	}
}
