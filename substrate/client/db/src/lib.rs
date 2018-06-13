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

//! Client backend that uses RocksDB database as storage.

extern crate substrate_client as client;
extern crate ethereum_types;
extern crate kvdb_rocksdb;
extern crate kvdb;
extern crate hashdb;
extern crate memorydb;
extern crate parking_lot;
extern crate patricia_trie;
extern crate substrate_state_machine as state_machine;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_codec as codec;
extern crate substrate_state_db as state_db;

#[macro_use]
extern crate log;

#[cfg(test)]
extern crate kvdb_memorydb;

use std::sync::Arc;
use std::path::PathBuf;
use std::collections::HashMap;

use codec::Slicable;
use ethereum_types::H256 as TrieH256;
use primitives::H256;
use hashdb::{DBValue, HashDB};
use kvdb_rocksdb::{Database, DatabaseConfig};
use kvdb::{KeyValueDB, DBTransaction};
use memorydb::MemoryDB;
use parking_lot::RwLock;
use patricia_trie::{TrieDB, TrieDBMut, TrieError, Trie, TrieMut};
use runtime_primitives::generic::BlockId;
use runtime_primitives::bft::Justification;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, As, Hashing, HashingFor, Zero};
use state_machine::backend::Backend as StateBackend;
use state_machine::CodeExecutor;
use state_db::StateDb;

const PRUNING_WINDOW: u32 = 256;
const FINALIZATION_WINDOW: u64 = 32;

/// Database settings.
pub struct DatabaseSettings {
	/// Cache size in bytes. If `None` default is used.
	pub cache_size: Option<usize>,
	/// Path to the database.
	pub path: PathBuf,
}

/// Create an instance of db-backed client.
pub fn new_client<E, F, Block>(
	settings: DatabaseSettings,
	executor: E,
	genesis_builder: F,
) -> Result<client::Client<Backend<Block>, client::LocalCallExecutor<Backend<Block>, E>, Block>, client::error::Error>
	where
		Block: BlockT,
		<Block::Header as HeaderT>::Number: As<u32>,
		Block::Hash: Into<[u8; 32]>, // TODO: remove when patricia_trie generic.
		E: CodeExecutor,
		F: client::GenesisBuilder<Block>,
{
	let backend = Arc::new(Backend::new(&settings)?);
	let executor = client::LocalCallExecutor::new(backend.clone(), executor);
	Ok(client::Client::new(backend, executor, genesis_builder)?)
}

mod columns {
	pub const META: Option<u32> = Some(0);
	pub const STATE: Option<u32> = Some(1);
	pub const STATE_META: Option<u32> = Some(2);
	pub const BLOCK_INDEX: Option<u32> = Some(3);
	pub const HEADER: Option<u32> = Some(4);
	pub const BODY: Option<u32> = Some(5);
	pub const JUSTIFICATION: Option<u32> = Some(6);
	pub const NUM_COLUMNS: u32 = 7;
}

mod meta {
	pub const BEST_BLOCK: &[u8; 4] = b"best";
}

struct PendingBlock<Block: BlockT> {
	header: Block::Header,
	justification: Option<Justification<Block::Hash>>,
	body: Option<Vec<Block::Extrinsic>>,
	is_best: bool,
}

#[derive(Clone)]
struct Meta<N, H> {
	best_hash: H,
	best_number: N,
	genesis_hash: H,
}

type BlockKey = [u8; 4];

// Little endian
fn number_to_db_key<N>(n: N) -> BlockKey where N: As<u32> {
	let n: u32 = n.as_();

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

// wrapper that implements trait required for state_db
struct BackingStateDb<'a>(&'a KeyValueDB);

impl<'a> state_db::KeyValueDb for BackingStateDb<'a> {
	type Error = kvdb::Error;
	type Hash = H256;

	fn get(&self, key: &H256) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.get(columns::STATE, &key[..]).map(|r| r.map(|v| v.to_vec()))
	}

	fn get_meta(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.get(columns::STATE_META, key).map(|r| r.map(|v| v.to_vec()))
	}
}

/// Block database
pub struct BlockchainDb<Block: BlockT> {
	db: Arc<KeyValueDB>,
	meta: RwLock<Meta<<Block::Header as HeaderT>::Number, Block::Hash>>,
}

impl<Block: BlockT> BlockchainDb<Block> where <Block::Header as HeaderT>::Number: As<u32> {
	fn id(&self, id: BlockId<Block>) -> Result<Option<BlockKey>, client::error::Error> {
		match id {
			BlockId::Hash(h) => {
				{
					let meta = self.meta.read();
					if meta.best_hash == h {
						return Ok(Some(number_to_db_key(meta.best_number)));
					}
				}
				self.db.get(columns::BLOCK_INDEX, h.as_ref()).map(|v| v.map(|v| {
					let mut key: [u8; 4] = [0; 4];
					key.copy_from_slice(&v);
					key
				})).map_err(db_err)
			},
			BlockId::Number(n) => Ok(Some(number_to_db_key(n))),
		}
	}

	fn new(db: Arc<KeyValueDB>) -> Result<Self, client::error::Error> {
		let (best_hash, best_number) = if let Some(Some(header)) = db.get(columns::META, meta::BEST_BLOCK).and_then(|id|
			match id {
				Some(id) => db.get(columns::HEADER, &id).map(|h| h.map(|b| Block::Header::decode(&mut &b[..]))),
				None => Ok(None),
			}).map_err(db_err)?
		{
			let hash = header.hash();
			debug!("DB Opened blockchain db, best {:?} ({})", hash, header.number());
			(hash, header.number().clone())
		} else {
			(Default::default(), Zero::zero())
		};
		let genesis_hash = db.get(columns::HEADER, &number_to_db_key(<Block::Header as HeaderT>::Number::zero())).map_err(db_err)?
			.map(|b| HashingFor::<Block>::hash(&b)).unwrap_or_default().into();

		Ok(BlockchainDb {
			db,
			meta: RwLock::new(Meta {
				best_hash,
				best_number,
				genesis_hash,
			})
		})
	}

	fn read_db(&self, id: BlockId<Block>, column: Option<u32>) -> Result<Option<DBValue>, client::error::Error> {
		self.id(id).and_then(|key|
		 match key {
			 Some(key) => self.db.get(column, &key).map_err(db_err),
			 None => Ok(None),
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

impl<Block: BlockT> client::blockchain::Backend<Block> for BlockchainDb<Block> where <Block::Header as HeaderT>::Number: As<u32> {
	fn header(&self, id: BlockId<Block>) -> Result<Option<Block::Header>, client::error::Error> {
		match self.read_db(id, columns::HEADER)? {
			Some(header) => match Block::Header::decode(&mut &header[..]) {
				Some(header) => Ok(Some(header)),
				None => return Err(client::error::ErrorKind::Backend("Error decoding header".into()).into()),
			}
			None => Ok(None),
		}
	}

	fn body(&self, id: BlockId<Block>) -> Result<Option<Vec<Block::Extrinsic>>, client::error::Error> {
		match self.read_db(id, columns::BODY)? {
			Some(body) => match Slicable::decode(&mut &body[..]) {
				Some(body) => Ok(Some(body)),
				None => return Err(client::error::ErrorKind::Backend("Error decoding body".into()).into()),
			}
			None => Ok(None),
		}
	}

	fn justification(&self, id: BlockId<Block>) -> Result<Option<Justification<Block::Hash>>, client::error::Error> {
		match self.read_db(id, columns::JUSTIFICATION)? {
			Some(justification) => match Slicable::decode(&mut &justification[..]) {
				Some(justification) => Ok(Some(justification)),
				None => return Err(client::error::ErrorKind::Backend("Error decoding justification".into()).into()),
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
			BlockId::Hash(_) => self.id(id)?.is_some(),
			BlockId::Number(n) => n <= self.meta.read().best_number,
		};
		match exists {
			true => Ok(client::blockchain::BlockStatus::InChain),
			false => Ok(client::blockchain::BlockStatus::Unknown),
		}
	}

	fn hash(&self, number: <Block::Header as HeaderT>::Number) -> Result<Option<Block::Hash>, client::error::Error> {
		self.read_db(BlockId::Number(number), columns::HEADER).map(|x|
			x.map(|raw| HashingFor::<Block>::hash(&raw[..])).map(Into::into)
		)
	}
}

/// Database transaction
pub struct BlockImportOperation<Block: BlockT> {
	old_state: DbState<Block>,
	updates: MemoryDB,
	pending_block: Option<PendingBlock<Block>>,
}

impl<Block: BlockT> client::backend::BlockImportOperation<Block> for BlockImportOperation<Block> {
	type State = DbState<Block>;

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

struct Ephemeral<'a, Block: BlockT> {
	backing: &'a KeyValueDB,
	state_db: &'a StateDb<Block::Hash, H256>,
	overlay: &'a mut MemoryDB,
}

impl<'a, Block: BlockT> HashDB for Ephemeral<'a, Block> {
	fn keys(&self) -> HashMap<TrieH256, i32> {
		self.overlay.keys() // TODO: iterate backing
	}

	fn get(&self, key: &TrieH256) -> Option<DBValue> {
		match self.overlay.raw(key) {
			Some((val, i)) => {
				if i <= 0 {
					None
				} else {
					Some(val)
				}
			}
			None => {
				match self.state_db.get(&H256::from(key.0), &BackingStateDb(self.backing)) {
					Ok(x) => x.map(|v| DBValue::from_slice(&v)),
					Err(e) => {
						panic!("Failed to read from DB: {:?}", e);
					}
				}
			}
		}
	}

	fn contains(&self, key: &TrieH256) -> bool {
		self.get(key).is_some()
	}

	fn insert(&mut self, value: &[u8]) -> TrieH256 {
		self.overlay.insert(value)
	}

	fn emplace(&mut self, key: TrieH256, value: DBValue) {
		self.overlay.emplace(key, value)
	}

	fn remove(&mut self, key: &TrieH256) {
		self.overlay.remove(key)
	}
}

/// DB-backed patricia trie state, transaction type is an overlay of changes to commit.
#[derive(Clone)]
pub struct DbState<Block: BlockT> {
	block_hash: Block::Hash,
	db: Arc<KeyValueDB>,
	state_db: Arc<StateDb<Block::Hash, H256>>,
	root: TrieH256,
}

impl<Block: BlockT> DbState<Block> {
	pub fn new(
			block_hash: &Block::Hash,
			db: Arc<KeyValueDB>,
			state_db: Arc<StateDb<Block::Hash, H256>>,
			root: TrieH256
		) -> DbState<Block>
	{
		state_db.pin(block_hash);
		DbState {
			block_hash: block_hash.clone(),
			db,
			state_db,
			root,
		}
	}
}

impl<Block: BlockT> Drop for DbState<Block> {
	fn drop(&mut self) {
		self.state_db.unpin(&self.block_hash);
	}
}

impl<Block: BlockT> state_machine::Backend for DbState<Block> {
	type Error = client::error::Error;
	type Transaction = MemoryDB;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		let mut read_overlay = MemoryDB::default();
		let eph: Ephemeral<Block> = Ephemeral {
			backing: &*self.db,
			state_db: &*self.state_db,
			overlay: &mut read_overlay,
		};

		let map_e = |e: Box<TrieError>| ::client::error::Error::from(format!("Trie lookup error: {}", e));

		TrieDB::new(&eph, &self.root).map_err(map_e)?
			.get(key).map(|x| x.map(|val| val.to_vec())).map_err(map_e)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		let mut read_overlay = MemoryDB::default();
		let eph: Ephemeral<Block> = Ephemeral {
			backing: &*self.db,
			state_db: &*self.state_db,
			overlay: &mut read_overlay,
		};

		let collect_all = || -> Result<_, Box<TrieError>> {
			let trie = TrieDB::new(&eph, &self.root)?;
			let mut v = Vec::new();
			for x in trie.iter()? {
				let (key, value) = x?;
				v.push((key.to_vec(), value.to_vec()));
			}

			Ok(v)
		};

		match collect_all() {
			Ok(v) => v,
			Err(e) => {
				debug!("Error extracting trie values: {}", e);
				Vec::new()
			}
		}
	}

	fn storage_root<I>(&self, delta: I) -> ([u8; 32], MemoryDB)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		let mut write_overlay = MemoryDB::default();
		let mut root = self.root;
		{
			let mut eph: Ephemeral<Block> = Ephemeral {
				backing: &*self.db,
				state_db: &*self.state_db,
				overlay: &mut write_overlay,
			};

			let mut trie = TrieDBMut::from_existing(&mut eph, &mut root).expect("prior state root to exist"); // TODO: handle gracefully
			for (key, change) in delta {
				let result = match change {
					Some(val) => trie.insert(&key, &val),
					None => trie.remove(&key), // TODO: archive mode
				};

				if let Err(e) = result {
					warn!("Failed to write to trie: {}", e);
				}
			}
		}

		(root.0.into(), write_overlay)
	}
}

/// Disk backend. Keeps data in a key-value store. In archive mode, trie nodes are kept from all blocks.
/// Otherwise, trie nodes are kept only from the most recent block.
pub struct Backend<Block: BlockT> {
	db: Arc<KeyValueDB>,
	state_db: Arc<StateDb<Block::Hash, H256>>,
	blockchain: BlockchainDb<Block>,
}

impl<Block: BlockT> Backend<Block> where <Block::Header as HeaderT>::Number: As<u32> {
	/// Create a new instance of database backend.
	pub fn new(config: &DatabaseSettings) -> Result<Self, client::error::Error> {
		let mut db_config = DatabaseConfig::with_columns(Some(columns::NUM_COLUMNS));
		db_config.memory_budget = config.cache_size;
		db_config.wal = true;
		let path = config.path.to_str().ok_or_else(|| client::error::ErrorKind::Backend("Invalid database path".into()))?;
		let db = Arc::new(Database::open(&db_config, &path).map_err(db_err)?);

		Backend::from_kvdb(db as Arc<_>, false)
	}

	#[cfg(test)]
	fn new_test() -> Self {
		let db = Arc::new(::kvdb_memorydb::create(columns::NUM_COLUMNS));

		Backend::from_kvdb(db as Arc<_>, false).expect("failed to create test-db")
	}

	fn from_kvdb(db: Arc<KeyValueDB>, archive: bool) -> Result<Self, client::error::Error> {
		let blockchain = BlockchainDb::new(db.clone())?;
		let pruning_mode = match archive {
			true => state_db::PruningMode::ArchiveAll,
			false => state_db::PruningMode::Constrained(state_db::Constraints {
				max_mem: None,
				max_blocks: Some(PRUNING_WINDOW),
			}),
		};
		let map_e = |e: state_db::Error<BackingStateDb>| ::client::error::Error::from(format!("State database error: {:?}", e));
		let state_db: StateDb<Block::Hash, H256> = StateDb::new(pruning_mode, &BackingStateDb(&*db)).map_err(map_e)?;

		Ok(Backend {
			db,
			state_db: Arc::new(state_db),
			blockchain,
		})
	}
}

fn apply_state_commit(transaction: &mut DBTransaction, commit: state_db::CommitSet<H256>) {
	for (key, val) in commit.data.inserted.into_iter() {
		transaction.put(columns::STATE, &key[..], &val);
	}
	for key in commit.data.deleted.into_iter() {
		transaction.delete(columns::STATE, &key[..]);
	}
	for (key, val) in commit.meta.inserted.into_iter() {
		transaction.put(columns::STATE_META, &key[..], &val);
	}
	for key in commit.meta.deleted.into_iter() {
		transaction.delete(columns::STATE_META, &key[..]);
	}
}

impl<Block: BlockT> client::backend::Backend<Block> for Backend<Block> where
	<Block::Header as HeaderT>::Number: As<u32>,
	Block::Hash: Into<[u8; 32]>, // TODO: remove when patricia_trie generic.
{
	type BlockImportOperation = BlockImportOperation<Block>;
	type Blockchain = BlockchainDb<Block>;
	type State = DbState<Block>;

	fn begin_operation(&self, block: BlockId<Block>) -> Result<Self::BlockImportOperation, client::error::Error> {
		let state = self.state_at(block)?;
		Ok(BlockImportOperation {
			pending_block: None,
			old_state: state,
			updates: MemoryDB::default(),
		})
	}

	fn commit_operation(&self, mut operation: Self::BlockImportOperation) -> Result<(), client::error::Error> {
		use client::blockchain::Backend;
		let mut transaction = DBTransaction::new();
		if let Some(pending_block) = operation.pending_block {
			let hash = pending_block.header.hash();
			let number = pending_block.header.number().clone();
			let key = number_to_db_key(pending_block.header.number().clone());
			transaction.put(columns::HEADER, &key, &pending_block.header.encode());
			if let Some(body) = pending_block.body {
				transaction.put(columns::BODY, &key, &body.encode());
			}
			if let Some(justification) = pending_block.justification {
				transaction.put(columns::JUSTIFICATION, &key, &justification.encode());
			}
			transaction.put(columns::BLOCK_INDEX, hash.as_ref(), &key);
			if pending_block.is_best {
				transaction.put(columns::META, meta::BEST_BLOCK, &key);
			}
			let mut changeset: state_db::ChangeSet<H256> = state_db::ChangeSet::default();
			for (key, (val, rc)) in operation.updates.drain() {
				if rc > 0 {
					changeset.inserted.push((key.0.into(), val.to_vec()));
				} else if rc < 0 {
					changeset.deleted.push(key.0.into());
				}
			}
			let number_u64 = number.as_().into();
			let commit = self.state_db.insert_block(&hash, number_u64, &pending_block.header.parent_hash(), changeset);
			apply_state_commit(&mut transaction, commit);

			//finalize an older block
			if number_u64 > FINALIZATION_WINDOW {
				if let Some(finalizing_hash) = self.blockchain.hash(As::sa((number_u64 - FINALIZATION_WINDOW) as u32))? {
					trace!("Finalizing block #{} ({:?})", number_u64 - FINALIZATION_WINDOW, finalizing_hash);
					let commit = self.state_db.finalize_block(&finalizing_hash);
					apply_state_commit(&mut transaction, commit);
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
		use client::blockchain::Backend as BcBackend;

		// special case for genesis initialization
		match block {
			BlockId::Hash(h) if h == Default::default() => {
				let mut root = TrieH256::default();
				let mut db = MemoryDB::default();
				TrieDBMut::new(&mut db, &mut root);

				return Ok(DbState::new(&h, self.db.clone(), self.state_db.clone(), root));
			}
			_ => {}
		}

		self.blockchain.header(block).and_then(|maybe_hdr| maybe_hdr.map(|hdr| {
			let root: [u8; 32] = hdr.state_root().clone().into();
			// TODO: reuse header hash
			DbState::new(&hdr.hash(), self.db.clone(), self.state_db.clone(), root.into())
		}).ok_or_else(|| client::error::ErrorKind::UnknownBlock(format!("{:?}", block)).into()))
	}
}

impl<Block: BlockT> client::backend::LocalBackend<Block> for Backend<Block> where
	<Block::Header as HeaderT>::Number: As<u32>,
	Block::Hash: Into<[u8; 32]>, // TODO: remove when patricia_trie generic.
{}

#[cfg(test)]
mod tests {
	use super::*;
	use client::backend::Backend as BTrait;
	use client::backend::BlockImportOperation as Op;
	use client::blockchain::Backend as BCTrait;
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
					parent_hash: if i == 0 {
						Default::default()
					} else {
						db.blockchain.hash(i - 1).unwrap().unwrap()
					},
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
	fn does_not_delete_when_negative_rc() {
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

			assert!(db.db.get(::columns::STATE, &key.0[..]).unwrap().is_some());
		}
	}
}
