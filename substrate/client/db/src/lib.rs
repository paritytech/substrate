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
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_codec as codec;

#[macro_use]
extern crate log;

#[cfg(test)]
extern crate kvdb_memorydb;

pub mod light;

mod utils;

use std::sync::Arc;
use std::path::PathBuf;

use codec::Slicable;
use kvdb::{KeyValueDB, DBTransaction};
use memorydb::MemoryDB;
use parking_lot::RwLock;
use runtime_primitives::generic::BlockId;
use runtime_primitives::bft::Justification;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, As, Hashing, HashingFor, Zero};
use runtime_primitives::BuildStorage;
use state_machine::backend::Backend as StateBackend;
use state_machine::CodeExecutor;
use utils::{Meta, db_err, meta_keys, number_to_db_key, open_database, read_db, read_id, read_meta};

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
pub fn new_client<E, S, Block>(
	settings: DatabaseSettings,
	executor: E,
	genesis_storage: S,
) -> Result<client::Client<Backend<Block>, client::LocalCallExecutor<Backend<Block>, E>, Block>, client::error::Error>
	where
		Block: BlockT,
		<Block::Header as HeaderT>::Number: As<u32>,
		Block::Hash: Into<[u8; 32]>, // TODO: remove when patricia_trie generic.
		E: CodeExecutor,
		S: BuildStorage,
{
	let backend = Arc::new(Backend::new(settings)?);
	let executor = client::LocalCallExecutor::new(backend.clone(), executor);
	Ok(client::Client::new(backend, executor, genesis_storage)?)
}

mod columns {
	pub const META: Option<u32> = Some(0);
	pub const STATE: Option<u32> = Some(1);
	pub const BLOCK_INDEX: Option<u32> = Some(2);
	pub const HEADER: Option<u32> = Some(3);
	pub const BODY: Option<u32> = Some(4);
	pub const JUSTIFICATION: Option<u32> = Some(5);
}

struct PendingBlock<Block: BlockT> {
	header: Block::Header,
	justification: Option<Justification<Block::Hash>>,
	body: Option<Vec<Block::Extrinsic>>,
	is_best: bool,
}

/// Block database
pub struct BlockchainDb<Block: BlockT> {
	db: Arc<KeyValueDB>,
	meta: RwLock<Meta<<Block::Header as HeaderT>::Number, Block::Hash>>,
}

impl<Block: BlockT> BlockchainDb<Block> where <Block::Header as HeaderT>::Number: As<u32> {
	fn new(db: Arc<KeyValueDB>) -> Result<Self, client::error::Error> {
		let meta = read_meta::<Block>(&*db, columns::HEADER)?;
		Ok(BlockchainDb {
			db,
			meta: RwLock::new(meta)
		})
	}

	fn update_meta(&self, hash: Block::Hash, number: <Block::Header as HeaderT>::Number, is_best: bool) {
		if is_best {
			let mut meta = self.meta.write();
			if number == Zero::zero() {
				meta.genesis_hash = hash;
			}
			meta.best_number = number;
			meta.best_hash = hash;
		}
	}
}

impl<Block: BlockT> client::blockchain::HeaderBackend<Block> for BlockchainDb<Block> where <Block::Header as HeaderT>::Number: As<u32> {
	fn header(&self, id: BlockId<Block>) -> Result<Option<Block::Header>, client::error::Error> {
		match read_db(&*self.db, columns::BLOCK_INDEX, columns::HEADER, id)? {
			Some(header) => match Block::Header::decode(&mut &header[..]) {
				Some(header) => Ok(Some(header)),
				None => return Err(client::error::ErrorKind::Backend("Error decoding header".into()).into()),
			}
			None => Ok(None),
		}
	}

	fn info(&self) -> Result<client::blockchain::Info<Block>, client::error::Error> {
		let meta = self.meta.read();
		Ok(client::blockchain::Info {
			best_hash: meta.best_hash,
			best_number: meta.best_number,
			genesis_hash: meta.genesis_hash,
		})
	}

	fn status(&self, id: BlockId<Block>) -> Result<client::blockchain::BlockStatus, client::error::Error> {
		let exists = match id {
			BlockId::Hash(_) => read_id(&*self.db, columns::BLOCK_INDEX, id)?.is_some(),
			BlockId::Number(n) => n <= self.meta.read().best_number,
		};
		match exists {
			true => Ok(client::blockchain::BlockStatus::InChain),
			false => Ok(client::blockchain::BlockStatus::Unknown),
		}
	}

	fn hash(&self, number: <Block::Header as HeaderT>::Number) -> Result<Option<Block::Hash>, client::error::Error> {
		read_db::<Block>(&*self.db, columns::BLOCK_INDEX, columns::HEADER, BlockId::Number(number)).map(|x|
			x.map(|raw| HashingFor::<Block>::hash(&raw[..])).map(Into::into)
		)
	}
}

impl<Block: BlockT> client::blockchain::Backend<Block> for BlockchainDb<Block> where <Block::Header as HeaderT>::Number: As<u32> {
	fn body(&self, id: BlockId<Block>) -> Result<Option<Vec<Block::Extrinsic>>, client::error::Error> {
		match read_db(&*self.db, columns::BLOCK_INDEX, columns::BODY, id)? {
			Some(body) => match Slicable::decode(&mut &body[..]) {
				Some(body) => Ok(Some(body)),
				None => return Err(client::error::ErrorKind::Backend("Error decoding body".into()).into()),
			}
			None => Ok(None),
		}
	}

	fn justification(&self, id: BlockId<Block>) -> Result<Option<Justification<Block::Hash>>, client::error::Error> {
		match read_db(&*self.db, columns::BLOCK_INDEX, columns::JUSTIFICATION, id)? {
			Some(justification) => match Slicable::decode(&mut &justification[..]) {
				Some(justification) => Ok(Some(justification)),
				None => return Err(client::error::ErrorKind::Backend("Error decoding justification".into()).into()),
			}
			None => Ok(None),
		}
	}
}

/// Database transaction
pub struct BlockImportOperation<Block: BlockT> {
	old_state: DbState,
	updates: MemoryDB,
	pending_block: Option<PendingBlock<Block>>,
}

impl<Block: BlockT> client::backend::BlockImportOperation<Block> for BlockImportOperation<Block> {
	type State = DbState;

	fn state(&self) -> Result<Option<&Self::State>, client::error::Error> {
		Ok(Some(&self.old_state))
	}

	fn set_block_data(&mut self, header: Block::Header, body: Option<Vec<Block::Extrinsic>>, justification: Option<Justification<Block::Hash>>, is_best: bool) -> Result<(), client::error::Error> {
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
pub struct Backend<Block: BlockT> {
	db: Arc<KeyValueDB>,
	blockchain: BlockchainDb<Block>,
	archive: bool,
}

impl<Block: BlockT> Backend<Block> where <Block::Header as HeaderT>::Number: As<u32> {
	/// Create a new instance of database backend.
	pub fn new(config: DatabaseSettings) -> Result<Self, client::error::Error> {
		let db = open_database(config, "full")?;

		Backend::from_kvdb(db as Arc<_>, true)
	}

	#[cfg(test)]
	fn new_test() -> Self {
		use utils::NUM_COLUMNS;

		let db = Arc::new(::kvdb_memorydb::create(NUM_COLUMNS));

		Backend::from_kvdb(db as Arc<_>, false).expect("failed to create test-db")
	}

	fn from_kvdb(db: Arc<KeyValueDB>, archive: bool) -> Result<Self, client::error::Error> {
		let blockchain = BlockchainDb::new(db.clone())?;

		Ok(Backend {
			db,
			blockchain,
			archive
		})
	}
}

impl<Block: BlockT> client::backend::Backend<Block> for Backend<Block> where
	<Block::Header as HeaderT>::Number: As<u32>,
	Block::Hash: Into<[u8; 32]>, // TODO: remove when patricia_trie generic.
{
	type BlockImportOperation = BlockImportOperation<Block>;
	type Blockchain = BlockchainDb<Block>;
	type State = DbState;

	fn begin_operation(&self, block: BlockId<Block>) -> Result<Self::BlockImportOperation, client::error::Error> {
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
			let hash = pending_block.header.hash();
			let number = pending_block.header.number().clone();
			let key = number_to_db_key(number.clone());
			transaction.put(columns::HEADER, &key, &pending_block.header.encode());
			if let Some(body) = pending_block.body {
				transaction.put(columns::BODY, &key, &body.encode());
			}
			if let Some(justification) = pending_block.justification {
				transaction.put(columns::JUSTIFICATION, &key, &justification.encode());
			}
			transaction.put(columns::BLOCK_INDEX, hash.as_ref(), &key);
			if pending_block.is_best {
				transaction.put(columns::META, meta_keys::BEST_BLOCK, &key);
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

	fn blockchain(&self) -> &BlockchainDb<Block> {
		&self.blockchain
	}

	fn state_at(&self, block: BlockId<Block>) -> Result<Self::State, client::error::Error> {
		use client::blockchain::HeaderBackend as BcHeaderBackend;

		// special case for genesis initialization
		match block {
			BlockId::Hash(h) if h == Default::default() =>
				return Ok(DbState::with_kvdb_for_genesis(self.db.clone(), ::columns::STATE)),
			_ => {}
		}

		self.blockchain.header(block).and_then(|maybe_hdr| maybe_hdr.map(|hdr| {
			let root: [u8; 32] = hdr.state_root().clone().into();
			DbState::with_kvdb(self.db.clone(), ::columns::STATE, root.into())
		}).ok_or_else(|| client::error::ErrorKind::UnknownBlock(format!("{:?}", block)).into()))
	}
}

impl<Block: BlockT> client::backend::LocalBackend<Block> for Backend<Block> where
	<Block::Header as HeaderT>::Number: As<u32>,
	Block::Hash: Into<[u8; 32]>, // TODO: remove when patricia_trie generic.
{}

#[cfg(test)]
mod tests {
	use hashdb::HashDB;
	use super::*;
	use client::backend::Backend as BTrait;
	use client::backend::BlockImportOperation as Op;
	use client::blockchain::HeaderBackend as BlockchainHeaderBackend;
	use runtime_primitives::testing::{Header, Block as RawBlock};

	type Block = RawBlock<u64>;

	#[test]
	fn block_hash_inserted_correctly() {
		let db = Backend::<Block>::new_test();
		for i in 0..10 {
			assert!(db.blockchain().hash(i).unwrap().is_none());

			{
				let id = if i == 0 {
					BlockId::Hash(Default::default())
				} else {
					BlockId::Number(i - 1)
				};

				let mut op = db.begin_operation(id).unwrap();
				let header = Header {
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
		let db = Backend::<Block>::new_test();
		{
			let mut op = db.begin_operation(BlockId::Hash(Default::default())).unwrap();
			let mut header = Header {
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
			let mut header = Header {
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
		let db = Backend::<Block>::new_test();

		{
			let mut op = db.begin_operation(BlockId::Hash(Default::default())).unwrap();
			let mut header = Header {
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
			let mut header = Header {
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
			let mut header = Header {
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
