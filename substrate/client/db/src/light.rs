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
use client::cht;
use client::error::{ErrorKind as ClientErrorKind, Result as ClientResult};
use client::light::blockchain::Storage as LightBlockchainStorage;
use codec::Slicable;
use primitives::{blake2_256, AuthorityId};
use primitives::block::{Id as BlockId, Header, HeaderHash, Number as BlockNumber};
use runtime_support::Hashable;
use cache::DbCache;
use utils::{meta_keys, Meta, db_err, number_to_db_key, open_database, read_db, read_id, read_meta};
use DatabaseSettings;

pub(crate) mod columns {
	pub const META: Option<u32> = ::utils::COLUMN_META;
	pub const BLOCK_INDEX: Option<u32> = Some(1);
	pub const HEADER: Option<u32> = Some(2);
	pub const AUTHORITIES: Option<u32> = Some(3);
	pub const CHT: Option<u32> = Some(4);
	pub const NUM_COLUMNS: u32 = 5;
}

/// Keep authorities for last 'AUTHORITIES_ENTRIES_TO_KEEP' blocks.
pub(crate) const AUTHORITIES_ENTRIES_TO_KEEP: BlockNumber = cht::SIZE;

/// Light blockchain storage. Stores most recent headers + CHTs for older headers.
pub struct LightStorage {
	db: Arc<KeyValueDB>,
	meta: RwLock<Meta>,
	cache: DbCache,
}

#[derive(Clone, PartialEq, Debug)]
struct BestAuthorities {
	/// first block, when this set became actual
	valid_from: BlockNumber,
	/// None means that we do not know the set starting from `valid_from` block
	authorities: Option<Vec<AuthorityId>>,
}

impl LightStorage {
	/// Create new storage with given settings.
	pub fn new(config: DatabaseSettings) -> ClientResult<Self> {
		let db = open_database(config, columns::NUM_COLUMNS, b"light")?;

		Self::from_kvdb(db as Arc<_>)
	}

	#[cfg(test)]
	pub(crate) fn new_test() -> Self {
		let db = Arc::new(::kvdb_memorydb::create(columns::NUM_COLUMNS));

		Self::from_kvdb(db as Arc<_>).expect("failed to create test-db")
	}

	#[cfg(test)]
	pub(crate) fn db(&self) -> &Arc<KeyValueDB> {
		&self.db
	}

	#[cfg(test)]
	pub(crate) fn cache(&self) -> &DbCache {
		&self.cache
	}

	fn from_kvdb(db: Arc<KeyValueDB>) -> ClientResult<Self> {
		let cache = DbCache::new(db.clone(), columns::BLOCK_INDEX, columns::AUTHORITIES)?;
		let meta = RwLock::new(read_meta(&*db, columns::HEADER)?);

		Ok(LightStorage {
			db,
			meta,
			cache,
		})
	}

	fn update_meta(&self, hash: HeaderHash, number: BlockNumber, is_best: bool) {
		if is_best {
			let mut meta = self.meta.write();
			if number == 0 {
				meta.genesis_hash = hash;
			}
			meta.best_number = number;
			meta.best_hash = hash;
		}
	}
}

impl BlockchainHeaderBackend for LightStorage {
	fn header(&self, id: BlockId) -> ClientResult<Option<Header>> {
		match read_db(&*self.db, columns::BLOCK_INDEX, columns::HEADER, id)? {
			Some(header) => match Header::decode(&mut &header[..]) {
				Some(header) => Ok(Some(header)),
				None => return Err(ClientErrorKind::Backend("Error decoding header".into()).into()),
			}
			None => Ok(None),
		}
	}

	fn info(&self) -> ClientResult<BlockchainInfo> {
		let meta = self.meta.read();
		Ok(BlockchainInfo {
			best_hash: meta.best_hash,
			best_number: meta.best_number,
			genesis_hash: meta.genesis_hash,
		})
	}

	fn status(&self, id: BlockId) -> ClientResult<BlockStatus> {
		let exists = match id {
			BlockId::Hash(_) => read_id(&*self.db, columns::BLOCK_INDEX, id)?.is_some(),
			BlockId::Number(n) => n <= self.meta.read().best_number,
		};
		match exists {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	fn hash(&self, number: BlockNumber) -> ClientResult<Option<HeaderHash>> {
		read_db(&*self.db, columns::BLOCK_INDEX, columns::HEADER, BlockId::Number(number))
			.map(|x| x.map(|raw| blake2_256(&raw[..])).map(Into::into))
	}
}

impl LightBlockchainStorage for LightStorage {
	fn import_header(&self, is_new_best: bool, header: Header, authorities: Option<Vec<AuthorityId>>) -> ClientResult<()> {
		let mut transaction = DBTransaction::new();

		let hash: HeaderHash = header.blake2_256().into();
		let number = header.number;
		let key = number_to_db_key(header.number);

		transaction.put(columns::HEADER, &key, &header.encode());
		transaction.put(columns::BLOCK_INDEX, &hash, &key);

		let (update_best_authorities, best_authorities) = if is_new_best {
			transaction.put(columns::META, meta_keys::BEST_BLOCK, &key);

			// save authorities for previous block
			let mut best_authorities = number.checked_sub(1)
				.and_then(|previous_number| self.cache.authorities_at_cache()
					.commit_best_entry(&mut transaction, previous_number, authorities));

			// prune authorities from 'ancient' blocks
			// TODO: when there'll be proper removal criteria, change this condition
			let mut update_best_authorities = best_authorities.is_some();
			if let Some(ancient_number) = number.checked_sub(AUTHORITIES_ENTRIES_TO_KEEP) {
				if self.cache.authorities_at_cache().prune_entries(&mut transaction, ancient_number)?.1 {
					update_best_authorities = true;
					best_authorities = None;
				}
			}

			(update_best_authorities, best_authorities)
		} else {
			(false, None)
		};

		// build new CHT if required
		if let Some(new_cht_number) = cht::is_build_required(number) {
			let new_cht_start = cht::start_number(new_cht_number);
			let new_cht_root = cht::compute_root(new_cht_number, (new_cht_start..)
				.map(|num| self.hash(num).unwrap_or_default()));

			if let Some(new_cht_root) = new_cht_root {
				transaction.put(columns::CHT, &number_to_db_key(new_cht_start), &*new_cht_root);
				for prune_block in new_cht_start..cht::end_number(new_cht_number) + 1 {
					transaction.delete(columns::HEADER, &number_to_db_key(prune_block));
				}
			}
		}

		debug!("Light DB Commit {:?} ({})", hash, number);
		self.db.write(transaction).map_err(db_err)?;
		self.update_meta(hash, number, is_new_best);
		if update_best_authorities {
			self.cache.authorities_at_cache().update_best_entry(best_authorities);
		}

		Ok(())
	}

	fn cht_root(&self, block: BlockNumber) -> ClientResult<HeaderHash> {
		let no_cht_for_block = || ClientErrorKind::Backend(format!("CHT for block {} not exists", block)).into();

		let cht_number = cht::block_to_cht_number(block).ok_or_else(no_cht_for_block)?;
		let cht_start = cht::start_number(cht_number);
		self.db.get(columns::CHT, &number_to_db_key(cht_start)).map_err(db_err)?
			.ok_or_else(no_cht_for_block)
			.map(|h| HeaderHash::from(&*h))
	}

	fn cache(&self) -> Option<&BlockchainCache> {
		Some(&self.cache)
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use client::cht;
	use primitives::Header;
	use super::*;

	pub fn insert_block(db: &LightStorage, parent: &HeaderHash, number: u64, authorities: Option<Vec<AuthorityId>>) -> HeaderHash {
		let header = Header {
			number,
			parent_hash: *parent,
			state_root: Default::default(),
			digest: Default::default(),
			extrinsics_root: Default::default(),
		};

		let hash = header.blake2_256().into();
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
		let db = LightStorage::new_test();
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

	#[test]
	fn ancient_headers_are_replaced_with_cht() {
		let db = LightStorage::new_test();

		// insert genesis block header (never pruned)
		let mut prev_hash = insert_block(&db, &Default::default(), 0, None);

		// insert SIZE blocks && ensure that nothing is pruned
		for number in 0..cht::SIZE {
			prev_hash = insert_block(&db, &prev_hash, 1 + number, None);
		}
		assert_eq!(db.db.iter(columns::HEADER).count(), (1 + cht::SIZE) as usize);
		assert_eq!(db.db.iter(columns::CHT).count(), 0);

		// insert next SIZE blocks && ensure that nothing is pruned
		for number in 0..cht::SIZE {
			prev_hash = insert_block(&db, &prev_hash, 1 + cht::SIZE + number, None);
		}
		assert_eq!(db.db.iter(columns::HEADER).count(), (1 + cht::SIZE + cht::SIZE) as usize);
		assert_eq!(db.db.iter(columns::CHT).count(), 0);

		// insert block #{2 * cht::SIZE + 1} && check that new CHT is created + headers of this CHT are pruned
		insert_block(&db, &prev_hash, 1 + cht::SIZE + cht::SIZE, None);
		assert_eq!(db.db.iter(columns::HEADER).count(), (1 + cht::SIZE + 1) as usize);
		assert_eq!(db.db.iter(columns::CHT).count(), 1);
		assert!((0..cht::SIZE).all(|i| db.db.get(columns::HEADER, &number_to_db_key(1 + i)).unwrap().is_none()));
	}

	#[test]
	fn get_cht_fails_for_genesis_block() {
		assert!(LightStorage::new_test().cht_root(0).is_err());
	}

	#[test]
	fn get_cht_fails_for_non_existant_cht() {
		assert!(LightStorage::new_test().cht_root(cht::SIZE / 2).is_err());
	}

	#[test]
	fn get_cht_works() {
		let db = LightStorage::new_test();

		// insert 1 + SIZE + SIZE + 1 blocks so that CHT#0 is created
		let mut prev_hash = Default::default();
		for i in 0..1 + cht::SIZE + cht::SIZE + 1 {
			prev_hash = insert_block(&db, &prev_hash, i, None);
		}

		let cht_root_1 = db.cht_root(cht::start_number(0)).unwrap();
		let cht_root_2 = db.cht_root(cht::start_number(0) + cht::SIZE / 2).unwrap();
		let cht_root_3 = db.cht_root(cht::end_number(0)).unwrap();
		assert_eq!(cht_root_1, cht_root_2);
		assert_eq!(cht_root_2, cht_root_3);
	}
}
