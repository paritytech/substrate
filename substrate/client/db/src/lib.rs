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
extern crate substrate_state_machine as state_machine;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_codec as codec;

#[macro_use]
extern crate log;

#[cfg(test)]
extern crate kvdb_memorydb;

use std::sync::Arc;
use std::path::PathBuf;

use codec::Slicable;
use hashdb::DBValue;
use kvdb_rocksdb::{Database, DatabaseConfig};
use kvdb::{KeyValueDB, DBTransaction};
use memorydb::MemoryDB;
use parking_lot::RwLock;
use primitives::blake2_256;
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

/// Create an instance of db-backed client.
pub fn new_client<E, F>(
	settings: DatabaseSettings,
	executor: E,
	genesis_builder: F,
) -> Result<client::Client<Backend, client::LocalCallExecutor<Backend, E>>, client::error::Error>
	where
		E: CodeExecutor,
		F: client::GenesisBuilder,
{
	let backend = Arc::new(Backend::new(&settings)?);
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
	pub const NUM_COLUMNS: u32 = 6;
}

mod meta {
	pub const BEST_BLOCK: &[u8; 4] = b"best";
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
				self.db.get(columns::BLOCK_INDEX, &h).map(|v| v.map(|v| {
					let mut key: [u8; 4] = [0; 4];
					key.copy_from_slice(&v);
					key
				})).map_err(db_err)
			},
			BlockId::Number(n) => Ok(Some(number_to_db_key(n))),
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
	old_state: DbState,
	updates: MemoryDB,
	pending_block: Option<PendingBlock>,
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

	#[cfg(test)]
	fn new_test() -> Backend {
		let db = Arc::new(::kvdb_memorydb::create(columns::NUM_COLUMNS));

		Backend::from_kvdb(db as Arc<_>, false).expect("failed to create test-db")
	}

	fn from_kvdb(db: Arc<KeyValueDB>, archive: bool) -> Result<Backend, client::error::Error> {
		let blockchain = BlockchainDb::new(db.clone())?;

		Ok(Backend {
			db,
			blockchain,
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
			pending_block: None,
			old_state: state,
			updates: MemoryDB::default(),
		})
	}

	fn commit_operation(&self, mut operation: Self::BlockImportOperation) -> Result<(), client::error::Error> {
		let mut transaction = DBTransaction::new();
		if let Some(pending_block) = operation.pending_block {
			let hash: block::HeaderHash = pending_block.header.blake2_256().into();
			let number = pending_block.header.number;;
			let key = number_to_db_key(pending_block.header.number);
			transaction.put(columns::HEADER, &key, &pending_block.header.encode());
			if let Some(body) = pending_block.body {
				transaction.put(columns::BODY, &key, &body.encode());
			}
			if let Some(justification) = pending_block.justification {
				transaction.put(columns::JUSTIFICATION, &key, &justification.encode());
			}
			transaction.put(columns::BLOCK_INDEX, &hash, &key);
			if pending_block.is_best {
				transaction.put(columns::META, meta::BEST_BLOCK, &key);
			}
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

#[cfg(test)]
mod tests {
	use hashdb::HashDB;
	use super::*;
	use client::backend::Backend as BTrait;
	use client::backend::BlockImportOperation as Op;
	use client::blockchain::Backend as BCTrait;

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
}
