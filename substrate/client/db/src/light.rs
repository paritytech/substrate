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
use codec::{Slicable, Input};
use primitives::{blake2_256, AuthorityId};
use primitives::block::{Id as BlockId, Header, HeaderHash, Number as BlockNumber};
use runtime_support::Hashable;
use utils::{meta_keys, BlockKey, Meta, db_err, db_key_to_number, number_to_db_key, open_database, read_db, read_id, read_meta};
use DatabaseSettings;

mod columns {
	pub const META: Option<u32> = ::utils::COLUMN_META;
	pub const BLOCK_INDEX: Option<u32> = Some(1);
	pub const HEADER: Option<u32> = Some(2);
	pub const AUTHORITIES: Option<u32> = Some(3);
	pub const CHT: Option<u32> = Some(4);
	pub const NUM_COLUMNS: u32 = 5;
}

/// Keep authorities for last 'AUTHORITIES_ENTRIES_TO_KEEP' blocks.
const AUTHORITIES_ENTRIES_TO_KEEP: BlockNumber = cht::SIZE;

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
	fn new_test() -> Self {
		let db = Arc::new(::kvdb_memorydb::create(columns::NUM_COLUMNS));

		Self::from_kvdb(db as Arc<_>).expect("failed to create test-db")
	}

	fn from_kvdb(db: Arc<KeyValueDB>) -> ClientResult<Self> {
		let cache = DbCache::new(db.clone())?;
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
				.and_then(|previous_number| self.cache
					.commit_best_authorities(&mut transaction, previous_number, authorities));

			// prune authorities from 'ancient' blocks
			// TODO: when there'll be proper removal criteria, change this condition
			let mut update_best_authorities = best_authorities.is_some();
			if let Some(ancient_number) = number.checked_sub(AUTHORITIES_ENTRIES_TO_KEEP) {
				if self.cache.prune_authorities(&mut transaction, ancient_number)?.1 {
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
			self.cache.update_best_authorities(best_authorities);
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

/// Database-backed blockchain cache.
struct DbCache {
	db: Arc<KeyValueDB>,
	/// Best authorities at the moent. None means that cache has no entries at all.
	best_authorities: RwLock<Option<BestAuthorities>>,
}

impl DbCache {
	fn new(db: Arc<KeyValueDB>) -> ClientResult<Self> {
		let best_authorities = RwLock::new(db.get(columns::META, meta_keys::BEST_AUTHORITIES)
			.map_err(db_err)
			.and_then(|block| match block {
				Some(block) => {
					let valid_from = db_key_to_number(&block)?;
					Self::read_authorities_entry(&*db, valid_from)
						.map(|entry| Some(BestAuthorities {
							valid_from: valid_from,
							authorities: entry
								.expect("BEST_AUTHORITIES points to the block; authorities entry at block exists when referenced; qed")
								.authorities,
						}))
				},
				None => Ok(None),
			})?);

		Ok(DbCache {
			db,
			best_authorities,
		})
	}

	fn best_authorities(&self) -> Option<BestAuthorities> {
		self.best_authorities.read().clone()
	}

	fn commit_best_authorities(&self, transaction: &mut DBTransaction, valid_from: BlockNumber, pending_authorities: Option<Vec<AuthorityId>>) -> Option<BestAuthorities> {
		let best_authorities = self.best_authorities();
		let update_best_authorities = match (best_authorities.as_ref().and_then(|a| a.authorities.as_ref()), pending_authorities.as_ref()) {
			(Some(best_authorities), Some(pending_authorities)) => best_authorities != pending_authorities,
			(None, Some(_)) | (Some(_), None) => true,
			(None, None) => false,
		};
		if !update_best_authorities {
			return None;
		}

		let valid_from_key = number_to_db_key(valid_from);
		transaction.put(columns::META, meta_keys::BEST_AUTHORITIES, &valid_from_key);
		transaction.put(columns::AUTHORITIES, &valid_from_key, &BestAuthoritiesEntry {
			prev_valid_from: best_authorities.map(|b| b.valid_from),
			authorities: pending_authorities.clone(),
		}.encode());

		Some(BestAuthorities {
			valid_from,
			authorities: pending_authorities,
		})
	}

	fn update_best_authorities(&self, best_authorities: Option<BestAuthorities>) {
		*self.best_authorities.write() = best_authorities;
	}

	fn read_authorities_entry(db: &KeyValueDB, number: BlockNumber) -> ClientResult<Option<BestAuthoritiesEntry>> {
		db.get(columns::AUTHORITIES, &number_to_db_key(number))
			.and_then(|authorities| match authorities {
				Some(authorities) => Ok(BestAuthoritiesEntry::decode(&mut &authorities[..])),
				None => Ok(None),
			})
		.map_err(db_err)
	}

	fn authorities_at_key(&self, key: BlockKey) -> ClientResult<Option<Vec<AuthorityId>>> {
		let at = db_key_to_number(&key)?;
		let best_authorities_valid_from = match self.best_authorities() {
			// there are entries in cache
			Some(best_authorities) => {
				// we're looking for the current set
				if at >= best_authorities.valid_from {
					return Ok(best_authorities.authorities);
				}

				// we're looking for the set of older blocks
				best_authorities.valid_from
			},
			// there are no entries in the cache
			None => return Ok(None),
		};

		let mut authorities_entry = Self::read_authorities_entry(&*self.db, best_authorities_valid_from)?
			.expect("self.best_authorities().is_some() if there's entry for valid_from; qed");
		loop {
			let prev_valid_from = match authorities_entry.prev_valid_from {
				Some(prev_valid_from) => prev_valid_from,
				None => return Ok(None),
			};

			let prev_authorities_entry = Self::read_authorities_entry(&*self.db, prev_valid_from)?
				.expect("entry referenced from next blocks; entry exists when referenced; qed");
			if at >= prev_valid_from {
				return Ok(prev_authorities_entry.authorities);
			}

			authorities_entry = prev_authorities_entry;
		}
	}

	/// Prune all authorities entries from the beginning up to the given key (including entry at the number).
	fn prune_authorities(&self, transaction: &mut DBTransaction, last_to_prune: BlockNumber) -> ClientResult<(usize, bool)> {
		let mut last_entry_to_keep = match self.best_authorities() {
			Some(best_authorities) => best_authorities.valid_from,
			None => return Ok((0, false)),
		};

		// find the last entry we want to keep
		let mut first_entry_to_remove = last_entry_to_keep;
		while first_entry_to_remove > last_to_prune {
			last_entry_to_keep = first_entry_to_remove;

			let entry = Self::read_authorities_entry(&*self.db, first_entry_to_remove)?
				.expect("entry referenced from next blocks; entry exists when referenced; qed");
			first_entry_to_remove = match entry.prev_valid_from {
				Some(prev_valid_from) => prev_valid_from,
				None => return Ok((0, false)),
			}
		}

		// remove all entries, starting from entry_to_remove
		let mut pruned = 0;
		let mut entry_to_remove = Some(first_entry_to_remove);
		while let Some(current_entry) = entry_to_remove {
			let entry = Self::read_authorities_entry(&*self.db, current_entry)?
				.expect("referenced entry exists; entry_to_remove is a reference to the entry; qed");

			transaction.delete(columns::AUTHORITIES, &number_to_db_key(current_entry));
			entry_to_remove = entry.prev_valid_from;
			pruned += 1;
		}

		// update last entry to keep if required
		let clear_cache = if last_entry_to_keep > first_entry_to_remove {
			let mut entry = Self::read_authorities_entry(&*self.db, last_entry_to_keep)?
				.expect("last_entry_to_keep > first_entry_to_remove; that means that we're leaving this entry in the db; qed");
			entry.prev_valid_from = None;
			transaction.put(columns::AUTHORITIES, &number_to_db_key(last_entry_to_keep), &entry.encode());

			false
		} else {
			true
		};

		Ok((pruned, clear_cache))
	}
}

impl BlockchainCache for DbCache {
	fn authorities_at(&self, at: BlockId) -> Option<Vec<AuthorityId>> {
		let authorities_at = read_id(&*self.db, columns::BLOCK_INDEX, at).and_then(|at| match at {
			Some(at) => self.authorities_at_key(at),
			None => Ok(None),
		});
		
		match authorities_at {
			Ok(authorities) => authorities,
			Err(error) => {
				warn!("Trying to read authorities from db cache has failed with: {}", error);
				None
			},
		}
	}
}

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
struct BestAuthoritiesEntry {
	/// None if valid from the beginning
	prev_valid_from: Option<BlockNumber>,
	/// None means that we do not know the set starting from `valid_from` block
	authorities: Option<Vec<AuthorityId>>,
}

impl Slicable for BestAuthoritiesEntry {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		match self.prev_valid_from {
			Some(ref prev_valid_from) => {
				v.push(1);
				v.extend(prev_valid_from.encode());
			},
			None => v.push(0),
		}

		match self.authorities {
			Some(ref authorities) => {
				v.push(1);
				v.extend(authorities.encode());
			},
			None => v.push(0),
		}

		v
	}

	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(BestAuthoritiesEntry {
			prev_valid_from: match input.read_byte() {
				None | Some(0) => None,
				_ => Slicable::decode(input),
			},
			authorities: match input.read_byte() {
				None | Some(0) => None,
				_ => Slicable::decode(input),
			},
		})
	}
}

#[cfg(test)]
mod tests {
	use client::cht;
	use primitives::Header;
	use super::*;

	fn insert_block(db: &LightStorage, parent: &HeaderHash, number: u64, authorities: Option<Vec<AuthorityId>>) -> HeaderHash {
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
	fn best_authorities_serialized() {
		let test_cases = vec![
			BestAuthoritiesEntry { prev_valid_from: Some(42), authorities: Some(vec![[1u8; 32]]) },
			BestAuthoritiesEntry { prev_valid_from: None, authorities: Some(vec![[1u8; 32], [2u8; 32]]) },
			BestAuthoritiesEntry { prev_valid_from: None, authorities: None },
		];

		for expected in test_cases {
			let serialized = expected.encode();
			let deserialized = BestAuthoritiesEntry::decode(&mut &serialized[..]).unwrap();
			assert_eq!(expected, deserialized);
		}
	}

	#[test]
	fn best_authorities_are_updated() {
		let db = LightStorage::new_test();
		let authorities_at = vec![
			(0, None),
			(0, None),
			(1, Some(BestAuthorities { valid_from: 1, authorities: Some(vec![[2u8; 32]]) })),
			(1, Some(BestAuthorities { valid_from: 1, authorities: Some(vec![[2u8; 32]]) })),
			(2, Some(BestAuthorities { valid_from: 3, authorities: Some(vec![[4u8; 32]]) })),
			(2, Some(BestAuthorities { valid_from: 3, authorities: Some(vec![[4u8; 32]]) })),
			(3, Some(BestAuthorities { valid_from: 5, authorities: None })),
			(3, Some(BestAuthorities { valid_from: 5, authorities: None })),
		];

		// before any block, there are no entries in cache
		assert!(db.cache.best_authorities().is_none());
		assert_eq!(db.db.iter(columns::AUTHORITIES).count(), 0);

		// insert blocks and check that best_authorities() returns correct result
		let mut prev_hash = Default::default();
		for number in 0..authorities_at.len() {
			let authorities_at_number = authorities_at[number].1.clone().and_then(|e| e.authorities);
			prev_hash = insert_block(&db, &prev_hash, number as u64, authorities_at_number);
			assert_eq!(db.cache.best_authorities(), authorities_at[number].1);
			assert_eq!(db.db.iter(columns::AUTHORITIES).count(), authorities_at[number].0);
		}

		// check that authorities_at() returns correct results for all retrospective blocks
		for number in 1..authorities_at.len() + 1 {
			assert_eq!(db.cache.authorities_at(BlockId::Number(number as u64)),
				authorities_at.get(number + 1)
					.or_else(|| authorities_at.last())
					.unwrap().1.clone().and_then(|e| e.authorities));
		}

		// now check that cache entries are pruned when new blocks are inserted
		let mut current_entries_count = authorities_at.last().unwrap().0;
		let pruning_starts_at = AUTHORITIES_ENTRIES_TO_KEEP as usize;
		for number in authorities_at.len()..authorities_at.len() + pruning_starts_at {
			prev_hash = insert_block(&db, &prev_hash, number as u64, None);
			if number > pruning_starts_at {
				let prev_entries_count = authorities_at[number - pruning_starts_at].0;
				let entries_count = authorities_at.get(number - pruning_starts_at + 1).map(|e| e.0)
					.unwrap_or_else(|| authorities_at.last().unwrap().0);
				current_entries_count -= entries_count - prev_entries_count;
			}

			assert_eq!(db.db.iter(columns::AUTHORITIES).count(), current_entries_count);
		}
	}

	#[test]
	fn best_authorities_are_pruned() {
		let db = LightStorage::new_test();
		let mut transaction = DBTransaction::new();
		db.cache.update_best_authorities(
			db.cache.commit_best_authorities(&mut transaction, 100, Some(vec![[1u8; 32]])));
		db.db.write(transaction).unwrap();

		let mut transaction = DBTransaction::new();
		assert_eq!(db.cache.prune_authorities(&mut transaction, 50).unwrap().0, 0);
		assert_eq!(db.cache.prune_authorities(&mut transaction, 100).unwrap().0, 1);
		assert_eq!(db.cache.prune_authorities(&mut transaction, 150).unwrap().0, 1);

		let mut transaction = DBTransaction::new();
		db.cache.update_best_authorities(
			db.cache.commit_best_authorities(&mut transaction, 200, Some(vec![[2u8; 32]])));
		db.db.write(transaction).unwrap();

		let mut transaction = DBTransaction::new();
		assert_eq!(db.cache.prune_authorities(&mut transaction, 50).unwrap().0, 0);
		assert_eq!(db.cache.prune_authorities(&mut transaction, 100).unwrap().0, 1);
		assert_eq!(db.cache.prune_authorities(&mut transaction, 150).unwrap().0, 1);
		assert_eq!(db.cache.prune_authorities(&mut transaction, 200).unwrap().0, 2);
		assert_eq!(db.cache.prune_authorities(&mut transaction, 250).unwrap().0, 2);

		let mut transaction = DBTransaction::new();
		assert_eq!(db.cache.prune_authorities(&mut transaction, 150).unwrap(), (1, false));
		db.db.write(transaction).unwrap();

		assert_eq!(db.cache.best_authorities().unwrap().authorities, Some(vec![[2u8; 32]]));
		assert_eq!(db.cache.authorities_at(BlockId::Number(50)), None);
		assert_eq!(db.cache.authorities_at(BlockId::Number(100)), None);
		assert_eq!(db.cache.authorities_at(BlockId::Number(150)), None);
		assert_eq!(db.cache.authorities_at(BlockId::Number(200)), Some(vec![[2u8; 32]]));
		assert_eq!(db.cache.authorities_at(BlockId::Number(250)), Some(vec![[2u8; 32]]));

		let mut transaction = DBTransaction::new();
		assert_eq!(db.cache.prune_authorities(&mut transaction, 300).unwrap(), (1, true));
		db.db.write(transaction).unwrap();
		db.cache.update_best_authorities(None);

		assert_eq!(db.cache.best_authorities(), None);
		assert_eq!(db.cache.authorities_at(BlockId::Number(50)), None);
		assert_eq!(db.cache.authorities_at(BlockId::Number(100)), None);
		assert_eq!(db.cache.authorities_at(BlockId::Number(150)), None);
		assert_eq!(db.cache.authorities_at(BlockId::Number(200)), None);
		assert_eq!(db.cache.authorities_at(BlockId::Number(250)), None);
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
