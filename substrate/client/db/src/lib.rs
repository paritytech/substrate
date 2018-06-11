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

//! Client backend that uses RocksDB database as storage. State is still kept in memory.

extern crate substrate_client as client;
extern crate kvdb_rocksdb;
extern crate kvdb;
extern crate hashdb;
extern crate memorydb;
extern crate parking_lot;
extern crate serde;
extern crate substrate_state_machine as state_machine;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_codec as codec;

#[macro_use]
extern crate log;
#[macro_use]
extern crate serde_derive;

#[cfg(test)]
extern crate kvdb_memorydb;

use std::sync::Arc;
use std::path::PathBuf;

use codec::{Slicable, Input};
use hashdb::DBValue;
use kvdb_rocksdb::{Database, DatabaseConfig};
use kvdb::{KeyValueDB, DBTransaction};
use memorydb::MemoryDB;
use parking_lot::RwLock;
use primitives::{blake2_256, AuthorityId};
use primitives::block::{self, Id as BlockId, HeaderHash};
use runtime_support::Hashable;
use state_machine::{CodeExecutor, Backend as StateBackend};

/// DB-backed patricia trie state, transaction type is an overlay of changes to commit.
pub type DbState = state_machine::TrieBackend;

/// Database settings.
pub struct DatabaseSettings {
	/// Cache size in bytes. If `None` default is used.
	pub cache_size: Option<usize>,
	/// Path to the database.
	pub path: PathBuf,
}

/// Create an instance of db-backed client backend.
pub fn new_backend(
	settings: DatabaseSettings,
) -> Result<Backend, client::error::Error>
{
	Backend::new(&settings)
}

/// Create an instance of db-backed client.
pub fn new_client<E, F>(
	backend: Backend,
	executor: E,
	genesis_builder: F,
) -> Result<client::Client<Backend, client::LocalCallExecutor<Backend, E>>, client::error::Error>
	where
		E: CodeExecutor,
		F: client::GenesisBuilder,
{
	let backend = Arc::new(backend);
	let executor = client::LocalCallExecutor::new(backend.clone(), executor);
	Ok(client::Client::new(backend, executor, genesis_builder)?)
}

mod columns {
	pub const META: Option<u32> = Some(0);
	pub const STATE: Option<u32> = Some(1);
	pub const BLOCK_INDEX: Option<u32> = Some(2);
	pub const HEADER: Option<u32> = Some(3);
	pub const BODY: Option<u32> = Some(4);
	pub const JUSTIFICATION: Option<u32> = Some(5);
	pub const AUTHORITIES: Option<u32> = Some(6);
	pub const NUM_COLUMNS: u32 = 7;
}

mod meta {
	pub const BEST_BLOCK: &[u8; 4] = b"best";
	pub const BEST_AUTHORITIES: &[u8; 4] = b"auth";
}

struct PendingBlock {
	header: block::Header,
	justification: Option<primitives::bft::Justification>,
	body: Option<block::Body>,
	is_best: bool,
}

#[derive(Clone)]
struct Meta {
	best_hash: HeaderHash,
	best_number: block::Number,
	genesis_hash: HeaderHash,
}

#[derive(Clone, PartialEq, Debug)]
struct BestAuthorities {
	/// first block, when this set became actual
	valid_from: block::Number,
	/// None means that we do not know the set starting from `valid_from` block
	authorities: Option<Vec<AuthorityId>>,
}

type BlockKey = [u8; 4];

// Little endian
fn number_to_db_key(n: block::Number) -> BlockKey {
	[
		(n >> 24) as u8,
		((n >> 16) & 0xff) as u8,
		((n >> 8) & 0xff) as u8,
		(n & 0xff) as u8
	]
}

fn db_key_to_number(key: &[u8]) -> Result<block::Number, client::error::Error> {
	match key.len() {
		4 => Ok((key[0] as block::Number) << 24
			| (key[1] as block::Number) << 16
			| (key[2] as block::Number) << 8
			| (key[3] as block::Number)),
		_ => Err(client::error::ErrorKind::Backend("Invalid block key".into()).into()),
	}
}

// Maps database error to client error
fn db_err(err: kvdb::Error) -> client::error::Error {
	use std::error::Error;
	match err.kind() {
		&kvdb::ErrorKind::Io(ref err) => client::error::ErrorKind::Backend(err.description().into()).into(),
		&kvdb::ErrorKind::Msg(ref m) => client::error::ErrorKind::Backend(m.clone()).into(),
		_ => client::error::ErrorKind::Backend("Unknown backend error".into()).into(),
	}
}

/// Block database
pub struct BlockchainDb {
	db: Arc<KeyValueDB>,
	meta: RwLock<Meta>,
}

impl BlockchainDb {
	fn id(&self, id: BlockId) -> Result<Option<BlockKey>, client::error::Error> {
		match id {
			BlockId::Hash(h) => {
				{
					let meta = self.meta.read();
					if meta.best_hash == h {
						return Ok(Some(number_to_db_key(meta.best_number)));
					}
				}

				read_id(&*self.db, BlockId::Hash(h))
			},
			BlockId::Number(n) => read_id(&*self.db, BlockId::Number(n)),
		}
	}

	fn new(db: Arc<KeyValueDB>) -> Result<BlockchainDb, client::error::Error> {
		let (best_hash, best_number) = if let Some(Some(header)) = db.get(columns::META, meta::BEST_BLOCK).and_then(|id|
			match id {
				Some(id) => db.get(columns::HEADER, &id).map(|h| h.map(|b| block::Header::decode(&mut &b[..]))),
				None => Ok(None),
			}).map_err(db_err)?
		{
			let hash = header.blake2_256().into();
			debug!("DB Opened blockchain db, best {:?} ({})", hash, header.number);
			(hash, header.number)
		} else {
			(Default::default(), Default::default())
		};
		let genesis_hash = db.get(columns::HEADER, &number_to_db_key(0)).map_err(db_err)?
			.map(|b| blake2_256(&b)).unwrap_or_default().into();

		Ok(BlockchainDb {
			db,
			meta: RwLock::new(Meta {
				best_hash,
				best_number,
				genesis_hash,
			})
		})
	}

	fn read_db(&self, id: BlockId, column: Option<u32>) -> Result<Option<DBValue>, client::error::Error> {
		self.id(id).and_then(|key|
		match key {
			Some(key) => self.db.get(column, &key).map_err(db_err),
			None => Ok(None),
		})
	}

	fn update_meta(&self, hash: block::HeaderHash, number: block::Number, is_best: bool) {
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

impl client::blockchain::Backend for BlockchainDb {
	fn header(&self, id: BlockId) -> Result<Option<block::Header>, client::error::Error> {
		match self.read_db(id, columns::HEADER)? {
			Some(header) => match block::Header::decode(&mut &header[..]) {
				Some(header) => Ok(Some(header)),
				None => return Err(client::error::ErrorKind::Backend("Error decoding header".into()).into()),
			}
			None => Ok(None),
		}
	}

	fn body(&self, id: BlockId) -> Result<Option<block::Body>, client::error::Error> {
		match self.read_db(id, columns::BODY)? {
			Some(body) => match block::Body::decode(&mut &body[..]) {
				Some(body) => Ok(Some(body)),
				None => return Err(client::error::ErrorKind::Backend("Error decoding body".into()).into()),
			}
			None => Ok(None),
		}
	}

	fn justification(&self, id: BlockId) -> Result<Option<primitives::bft::Justification>, client::error::Error> {
		match self.read_db(id, columns::JUSTIFICATION)? {
			Some(justification) => match primitives::bft::Justification::decode(&mut &justification[..]) {
				Some(justification) => Ok(Some(justification)),
				None => return Err(client::error::ErrorKind::Backend("Error decoding justification".into()).into()),
			}
			None => Ok(None),
		}
	}

	fn info(&self) -> Result<client::blockchain::Info, client::error::Error> {
		let meta = self.meta.read();
		Ok(client::blockchain::Info {
			best_hash: meta.best_hash,
			best_number: meta.best_number,
			genesis_hash: meta.genesis_hash,
		})
	}

	fn status(&self, id: BlockId) -> Result<client::blockchain::BlockStatus, client::error::Error> {
		let exists = match id {
			BlockId::Hash(_) => self.id(id)?.is_some(),
			BlockId::Number(n) => n <= self.meta.read().best_number,
		};
		match exists {
			true => Ok(client::blockchain::BlockStatus::InChain),
			false => Ok(client::blockchain::BlockStatus::Unknown),
		}
	}

	fn hash(&self, number: block::Number) -> Result<Option<block::HeaderHash>, client::error::Error> {
		self.read_db(BlockId::Number(number), columns::HEADER).map(|x|
			x.map(|raw| blake2_256(&raw[..])).map(Into::into)
		)
	}
}

/// Database transaction
pub struct BlockImportOperation {
	cache_authorities: bool,
	old_state: DbState,
	updates: MemoryDB,
	pending_block: Option<PendingBlock>,
	pending_authorities: Option<Vec<AuthorityId>>,
}

impl client::backend::BlockImportOperation for BlockImportOperation {
	type State = DbState;

	fn state(&self) -> Result<Option<&Self::State>, client::error::Error> {
		Ok(Some(&self.old_state))
	}

	fn set_block_data(&mut self, header: block::Header, body: Option<block::Body>, justification: Option<primitives::bft::Justification>, is_best: bool) -> Result<(), client::error::Error> {
		assert!(self.pending_block.is_none(), "Only one block per operation is allowed");
		self.pending_block = Some(PendingBlock {
			header,
			body,
			justification,
			is_best,
		});
		Ok(())
	}

	fn update_authorities(&mut self, authorities: Vec<AuthorityId>) {
		if self.cache_authorities {
			self.pending_authorities = Some(authorities);
		}
	}

	fn update_storage(&mut self, update: MemoryDB) -> Result<(), client::error::Error> {
		self.updates = update;
		Ok(())
	}

	fn reset_storage<I: Iterator<Item=(Vec<u8>, Vec<u8>)>>(&mut self, iter: I) -> Result<(), client::error::Error> {
		// TODO: wipe out existing trie.
		let (_, update) = self.old_state.storage_root(iter.into_iter().map(|(k, v)| (k, Some(v))));
		self.updates = update;
		Ok(())
	}
}

/// Disk backend. Keeps data in a key-value store. In archive mode, trie nodes are kept from all blocks.
/// Otherwise, trie nodes are kept only from the most recent block.
pub struct Backend {
	db: Arc<KeyValueDB>,
	blockchain: BlockchainDb,
	authorities_cache: Arc<DbAuthoritiesCache>,
	archive: bool,
}

impl Backend {
	/// Create a new instance of database backend.
	pub fn new(config: &DatabaseSettings) -> Result<Backend, client::error::Error> {
		let mut db_config = DatabaseConfig::with_columns(Some(columns::NUM_COLUMNS));
		db_config.memory_budget = config.cache_size;
		db_config.wal = true;
		let path = config.path.to_str().ok_or_else(|| client::error::ErrorKind::Backend("Invalid database path".into()))?;
		let db = Arc::new(Database::open(&db_config, &path).map_err(db_err)?);

		Backend::from_kvdb(db as Arc<_>, true)
	}

	/// Get shared authorities cache reference.
	pub fn authorities_cache(&self) -> Arc<client::backend::AuthoritiesCache> {
		self.authorities_cache.clone()
	}

	#[cfg(test)]
	fn new_test() -> Backend {
		let db = Arc::new(::kvdb_memorydb::create(columns::NUM_COLUMNS));

		Backend::from_kvdb(db as Arc<_>, false).expect("failed to create test-db")
	}

	fn from_kvdb(db: Arc<KeyValueDB>, archive: bool) -> Result<Backend, client::error::Error> {
		let blockchain = BlockchainDb::new(db.clone())?;
		let authorities_cache = Arc::new(DbAuthoritiesCache::new(db.clone())?);

		Ok(Backend {
			db,
			blockchain,
			authorities_cache,
			archive
		})
	}
}

impl client::backend::Backend for Backend {
	type BlockImportOperation = BlockImportOperation;
	type Blockchain = BlockchainDb;
	type State = DbState;

	fn begin_operation(&self, block: BlockId) -> Result<Self::BlockImportOperation, client::error::Error> {
		let state = self.state_at(block)?;
		Ok(BlockImportOperation {
			cache_authorities: false,
			pending_block: None,
			pending_authorities: None,
			old_state: state,
			updates: MemoryDB::default(),
		})
	}

	fn commit_operation(&self, mut operation: Self::BlockImportOperation) -> Result<(), client::error::Error> {
		let mut transaction = DBTransaction::new();
		if let Some(pending_block) = operation.pending_block {
			let hash: block::HeaderHash = pending_block.header.blake2_256().into();
			let number = pending_block.header.number;
			let key = number_to_db_key(pending_block.header.number);
			transaction.put(columns::HEADER, &key, &pending_block.header.encode());
			if let Some(body) = pending_block.body {
				transaction.put(columns::BODY, &key, &body.encode());
			}
			if let Some(justification) = pending_block.justification {
				transaction.put(columns::JUSTIFICATION, &key, &justification.encode());
			}
			transaction.put(columns::BLOCK_INDEX, &hash, &key);
			let updated_best_authorities = if pending_block.is_best {
				transaction.put(columns::META, meta::BEST_BLOCK, &key);

				if let Some(previous_number) = number.checked_sub(1) {
					self.authorities_cache.commit_best_authorities(&mut transaction, previous_number, operation.pending_authorities)
				} else {
					None
				}
			} else {
				None
			};
			for (key, (val, rc)) in operation.updates.drain() {
				if rc > 0 {
					transaction.put(columns::STATE, &key.0[..], &val);
				} else if rc < 0 && !self.archive {
					transaction.delete(columns::STATE, &key.0[..]);
				}
			}

			debug!("DB Commit {:?} ({})", hash, number);
			self.db.write(transaction).map_err(db_err)?;
			self.blockchain.update_meta(hash, number, pending_block.is_best);
			if let Some(updated_best_authorities) = updated_best_authorities {
				self.authorities_cache.update_best_authorities(updated_best_authorities);
			}
		}
		Ok(())
	}

	fn blockchain(&self) -> &BlockchainDb {
		&self.blockchain
	}

	fn state_at(&self, block: BlockId) -> Result<Self::State, client::error::Error> {
		use client::blockchain::Backend as BcBackend;

		// special case for genesis initialization
		match block {
			BlockId::Hash(h) if h == Default::default() =>
				return Ok(DbState::with_kvdb_for_genesis(self.db.clone(), ::columns::STATE)),
			_ => {}
		}

		self.blockchain.header(block).and_then(|maybe_hdr| maybe_hdr.map(|hdr| {
			DbState::with_kvdb(self.db.clone(), ::columns::STATE, hdr.state_root.0.into())
		}).ok_or_else(|| client::error::ErrorKind::UnknownBlock(block).into()))
	}
}

impl client::backend::LocalBackend for Backend {}

/// Database-backed authorities cache.
struct DbAuthoritiesCache {
	db: Arc<KeyValueDB>,
	/// None means that cache has no entries at all
	best_authorities: RwLock<Option<BestAuthorities>>,
}

impl DbAuthoritiesCache {
	fn new(db: Arc<KeyValueDB>) -> Result<Self, client::error::Error> {
		let best_authorities = RwLock::new(db.get(columns::META, meta::BEST_AUTHORITIES)
			.map_err(db_err)
			.and_then(|block| match block {
				Some(block) => {
					let valid_from = db_key_to_number(&block)?;
					Self::read_authorities_entry(&*db, valid_from)
						.map(|entry| Some(BestAuthorities {
							valid_from: valid_from,
							authorities: entry.expect("TODO").authorities,
						}))
				},
				None => Ok(None),
			})?);

		Ok(DbAuthoritiesCache {
			db,
			best_authorities,
		})
	}

	fn best_authorities(&self) -> Option<BestAuthorities> {
		self.best_authorities.read().clone()
	}

	fn commit_best_authorities(&self, transaction: &mut DBTransaction, valid_from: block::Number, pending_authorities: Option<Vec<AuthorityId>>) -> Option<BestAuthorities> {
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
		transaction.put(columns::META, meta::BEST_AUTHORITIES, &valid_from_key);
		transaction.put(columns::AUTHORITIES, &valid_from_key, &BestAuthoritiesEntry {
			prev_valid_from: best_authorities.map(|b| b.valid_from),
			authorities: pending_authorities.clone(),
		}.encode());

		Some(BestAuthorities {
			valid_from,
			authorities: pending_authorities,
		})
	}

	fn update_best_authorities(&self, best_authorities: BestAuthorities) {
		*self.best_authorities.write() = Some(best_authorities);
	}

	fn read_authorities_entry(db: &KeyValueDB, number: block::Number) -> Result<Option<BestAuthoritiesEntry>, client::error::Error> {
		db.get(columns::AUTHORITIES, &number_to_db_key(number))
			.and_then(|authorities| match authorities {
				Some(authorities) => Ok(BestAuthoritiesEntry::decode(&mut &authorities[..])),
				None => Ok(None),
			})
		.map_err(db_err)
	}

	fn authorities_at_key(&self, key: BlockKey) -> Result<Option<Vec<AuthorityId>>, client::error::Error> {
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
			let prev_authorities_entry = match authorities_entry.prev_valid_from {
				Some(prev_valid_from) => Some(Self::read_authorities_entry(&*self.db, prev_valid_from)?.expect("TODO")),
				None => None,
			};

			if prev_authorities_entry.is_none() || at >= authorities_entry.prev_valid_from.expect("TODO") {
				return Ok(prev_authorities_entry.and_then(|e| e.authorities));
			}

			authorities_entry = prev_authorities_entry.expect("TODO");
		}
	}
}

impl client::backend::AuthoritiesCache for DbAuthoritiesCache {
	fn authorities_at(&self, at: BlockId) -> Option<Vec<AuthorityId>> {
		let authorities_at = read_id(&*self.db, at).and_then(|at| match at {
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
	prev_valid_from: Option<block::Number>,
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

fn read_id(db: &KeyValueDB, id: BlockId) -> Result<Option<BlockKey>, client::error::Error> {
	match id {
		BlockId::Hash(h) => db.get(columns::BLOCK_INDEX, &h)
			.map(|v| v.map(|v| {
				let mut key: [u8; 4] = [0; 4];
				key.copy_from_slice(&v);
				key
			})).map_err(db_err),
		BlockId::Number(n) => Ok(Some(number_to_db_key(n))),
	}
}

#[cfg(test)]
mod tests {
	use hashdb::HashDB;
	use super::*;
	use client::backend::Backend as BTrait;
	use client::backend::BlockImportOperation as Op;
	use client::backend::AuthoritiesCache;
	use client::blockchain::{Backend as BlockchainBackend};

	#[test]
	fn block_hash_inserted_correctly() {
		let db = Backend::new_test();
		for i in 0..10 {
			assert!(db.blockchain().hash(i).unwrap().is_none());

			{
				let id = if i == 0 {
					BlockId::Hash(Default::default())
				} else {
					BlockId::Number(i - 1)
				};

				let mut op = db.begin_operation(id).unwrap();
				let header = block::Header {
					number: i,
					parent_hash: Default::default(),
					state_root: Default::default(),
					digest: Default::default(),
					extrinsics_root: Default::default(),
				};

				op.set_block_data(
					header,
					Some(vec![]),
					None,
					true,
				).unwrap();
				db.commit_operation(op).unwrap();
			}

			assert!(db.blockchain().hash(i).unwrap().is_some())
		}
	}

	#[test]
	fn set_state_data() {
		let db = Backend::new_test();
		{
			let mut op = db.begin_operation(BlockId::Hash(Default::default())).unwrap();
			let mut header = block::Header {
				number: 0,
				parent_hash: Default::default(),
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage = vec![
				(vec![1, 3, 5], vec![2, 4, 6]),
				(vec![1, 2, 3], vec![9, 9, 9]),
			];

			header.state_root = op.old_state.storage_root(storage
				.iter()
				.cloned()
				.map(|(x, y)| (x, Some(y)))
			).0.into();

			op.reset_storage(storage.iter().cloned()).unwrap();
			op.set_block_data(
				header,
				Some(vec![]),
				None,
				true
			).unwrap();

			db.commit_operation(op).unwrap();

			let state = db.state_at(BlockId::Number(0)).unwrap();

			assert_eq!(state.storage(&[1, 3, 5]).unwrap(), Some(vec![2, 4, 6]));
			assert_eq!(state.storage(&[1, 2, 3]).unwrap(), Some(vec![9, 9, 9]));
			assert_eq!(state.storage(&[5, 5, 5]).unwrap(), None);

		}

		{
			let mut op = db.begin_operation(BlockId::Number(0)).unwrap();
			let mut header = block::Header {
				number: 1,
				parent_hash: Default::default(),
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage = vec![
				(vec![1, 3, 5], None),
				(vec![5, 5, 5], Some(vec![4, 5, 6])),
			];

			let (root, overlay) = op.old_state.storage_root(storage.iter().cloned());
			op.update_storage(overlay).unwrap();
			header.state_root = root.into();

			op.set_block_data(
				header,
				Some(vec![]),
				None,
				true
			).unwrap();

			db.commit_operation(op).unwrap();

			let state = db.state_at(BlockId::Number(1)).unwrap();

			assert_eq!(state.storage(&[1, 3, 5]).unwrap(), None);
			assert_eq!(state.storage(&[1, 2, 3]).unwrap(), Some(vec![9, 9, 9]));
			assert_eq!(state.storage(&[5, 5, 5]).unwrap(), Some(vec![4, 5, 6]));
		}
	}

	#[test]
	fn delete_only_when_negative_rc() {
		let key;
		let db = Backend::new_test();

		{
			let mut op = db.begin_operation(BlockId::Hash(Default::default())).unwrap();
			let mut header = block::Header {
				number: 0,
				parent_hash: Default::default(),
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage: Vec<(_, _)> = vec![];

			header.state_root = op.old_state.storage_root(storage
				.iter()
				.cloned()
				.map(|(x, y)| (x, Some(y)))
			).0.into();

			op.reset_storage(storage.iter().cloned()).unwrap();

			key = op.updates.insert(b"hello");
			op.set_block_data(
				header,
				Some(vec![]),
				None,
				true
			).unwrap();

			db.commit_operation(op).unwrap();

			assert_eq!(db.db.get(::columns::STATE, &key.0[..]).unwrap().unwrap(), &b"hello"[..]);
		}

		{
			let mut op = db.begin_operation(BlockId::Number(0)).unwrap();
			let mut header = block::Header {
				number: 1,
				parent_hash: Default::default(),
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage: Vec<(_, _)> = vec![];

			header.state_root = op.old_state.storage_root(storage
				.iter()
				.cloned()
				.map(|(x, y)| (x, Some(y)))
			).0.into();

			op.updates.insert(b"hello");
			op.updates.remove(&key);
			op.set_block_data(
				header,
				Some(vec![]),
				None,
				true
			).unwrap();

			db.commit_operation(op).unwrap();

			assert_eq!(db.db.get(::columns::STATE, &key.0[..]).unwrap().unwrap(), &b"hello"[..]);
		}

		{
			let mut op = db.begin_operation(BlockId::Number(1)).unwrap();
			let mut header = block::Header {
				number: 1,
				parent_hash: Default::default(),
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage: Vec<(_, _)> = vec![];

			header.state_root = op.old_state.storage_root(storage
				.iter()
				.cloned()
				.map(|(x, y)| (x, Some(y)))
			).0.into();

			op.updates.remove(&key);
			op.set_block_data(
				header,
				Some(vec![]),
				None,
				true
			).unwrap();

			db.commit_operation(op).unwrap();

			assert!(db.db.get(::columns::STATE, &key.0[..]).unwrap().is_none());
		}
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
		let insert_block: Box<Fn(&Backend, &HeaderHash, u64, Option<Vec<AuthorityId>>) -> HeaderHash> = Box::new(|db, parent, number, authorities| {
			let header = block::Header {
				number: number,
				parent_hash: *parent,
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};
			let hash = header.blake2_256().into();

			let mut op = db.begin_operation(BlockId::Hash(*parent)).unwrap();
			op.cache_authorities = true;
			op.set_block_data(header, None, None, true).unwrap();
			if let Some(authorities) = authorities {
				op.update_authorities(authorities);
			}
			db.commit_operation(op).unwrap();
			hash
		});

		let db = Backend::new_test();
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
		assert!(db.authorities_cache.best_authorities().is_none());
		assert_eq!(db.db.iter(columns::AUTHORITIES).count(), 0);

		// insert blocks and check that best_authorities() returns correct result
		let mut prev_hash = Default::default();
		for number in 0..authorities_at.len() {
			let authorities_at_number = authorities_at[number].1.clone().and_then(|e| e.authorities);
			prev_hash = insert_block(&db, &prev_hash, number as u64, authorities_at_number);
			assert_eq!(db.authorities_cache.best_authorities(), authorities_at[number].1);
			assert_eq!(db.db.iter(columns::AUTHORITIES).count(), authorities_at[number].0);
		}

		// check that authorities_at() returns correct results for all retrospective blocks
		for number in 1..authorities_at.len() + 1 {
			assert_eq!(db.authorities_cache.authorities_at(BlockId::Number(number as u64)),
				authorities_at.get(number + 1)
					.or_else(|| authorities_at.last())
					.unwrap().1.clone().and_then(|e| e.authorities));
		}
	}
}
