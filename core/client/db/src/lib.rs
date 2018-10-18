// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

// tag::description[]
//! Client backend that uses RocksDB database as storage.
//!
//! # Canonicality vs. Finality
//!
//! Finality indicates that a block will not be reverted, according to the consensus algorithm,
//! while canonicality indicates that the block may be reverted, but we will be unable to do so,
//! having discarded heavy state that will allow a chain reorganization.
//!
//! Finality implies canonicality but not vice-versa.
//!
// end::description[]

extern crate substrate_client as client;
extern crate kvdb_rocksdb;
extern crate kvdb;
extern crate hash_db;
extern crate parking_lot;
extern crate substrate_state_machine as state_machine;
extern crate substrate_primitives as primitives;
extern crate sr_primitives as runtime_primitives;
extern crate parity_codec as codec;
extern crate substrate_executor as executor;
extern crate substrate_state_db as state_db;
extern crate substrate_trie as trie;

#[macro_use]
extern crate log;

#[macro_use]
extern crate parity_codec_derive;

#[cfg(test)]
extern crate substrate_test_client as test_client;

#[cfg(test)]
extern crate kvdb_memorydb;

pub mod light;

mod cache;
mod utils;

use std::sync::Arc;
use std::path::PathBuf;
use std::io;

use client::backend::NewBlockState;
use codec::{Decode, Encode};
use hash_db::Hasher;
use kvdb::{KeyValueDB, DBTransaction};
use trie::MemoryDB;
use parking_lot::RwLock;
use primitives::{H256, AuthorityId, Blake2Hasher, ChangesTrieConfiguration};
use primitives::storage::well_known_keys;
use runtime_primitives::{generic::BlockId, Justification};
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, As, NumberFor, Zero, Digest, DigestItem};
use runtime_primitives::BuildStorage;
use state_machine::backend::Backend as StateBackend;
use executor::RuntimeInfo;
use state_machine::{CodeExecutor, DBValue, ExecutionStrategy};
use utils::{Meta, db_err, meta_keys, open_database, read_db, block_id_to_lookup_key, read_meta};
use client::LeafSet;
use state_db::StateDb;
pub use state_db::PruningMode;

const CANONICALIZATION_DELAY: u64 = 256;
const MIN_BLOCKS_TO_KEEP_CHANGES_TRIES_FOR: u64 = 32768;

/// DB-backed patricia trie state, transaction type is an overlay of changes to commit.
pub type DbState = state_machine::TrieBackend<Arc<state_machine::Storage<Blake2Hasher>>, Blake2Hasher>;

/// Database settings.
pub struct DatabaseSettings {
	/// Cache size in bytes. If `None` default is used.
	pub cache_size: Option<usize>,
	/// Path to the database.
	pub path: PathBuf,
	/// Pruning mode.
	pub pruning: PruningMode,
}

/// Create an instance of db-backed client.
pub fn new_client<E, S, Block>(
	settings: DatabaseSettings,
	executor: E,
	genesis_storage: S,
	block_execution_strategy: ExecutionStrategy,
	api_execution_strategy: ExecutionStrategy,
) -> Result<client::Client<Backend<Block>, client::LocalCallExecutor<Backend<Block>, E>, Block>, client::error::Error>
	where
		Block: BlockT,
		E: CodeExecutor<Blake2Hasher> + RuntimeInfo,
		S: BuildStorage,
{
	let backend = Arc::new(Backend::new(settings, CANONICALIZATION_DELAY)?);
	let executor = client::LocalCallExecutor::new(backend.clone(), executor);
	Ok(client::Client::new(backend, executor, genesis_storage, block_execution_strategy, api_execution_strategy)?)
}

mod columns {
	pub const META: Option<u32> = ::utils::COLUMN_META;
	pub const STATE: Option<u32> = Some(1);
	pub const STATE_META: Option<u32> = Some(2);
	/// maps hashes to lookup keys
	pub const HASH_LOOKUP: Option<u32> = Some(3);
	pub const HEADER: Option<u32> = Some(4);
	pub const BODY: Option<u32> = Some(5);
	pub const JUSTIFICATION: Option<u32> = Some(6);
	pub const CHANGES_TRIE: Option<u32> = Some(7);
	pub const AUX: Option<u32> = Some(8);
}

struct PendingBlock<Block: BlockT> {
	header: Block::Header,
	justification: Option<Justification>,
	body: Option<Vec<Block::Extrinsic>>,
	leaf_state: NewBlockState,
}

// wrapper that implements trait required for state_db
struct StateMetaDb<'a>(&'a KeyValueDB);

impl<'a> state_db::MetaDb for StateMetaDb<'a> {
	type Error = io::Error;

	fn get_meta(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.get(columns::STATE_META, key).map(|r| r.map(|v| v.to_vec()))
	}
}

/// Block database
pub struct BlockchainDb<Block: BlockT> {
	db: Arc<KeyValueDB>,
	meta: RwLock<Meta<NumberFor<Block>, Block::Hash>>,
	leaves: RwLock<LeafSet<Block::Hash, NumberFor<Block>>>,
}

impl<Block: BlockT> BlockchainDb<Block> {
	fn new(db: Arc<KeyValueDB>) -> Result<Self, client::error::Error> {
		let meta = read_meta::<Block>(&*db, columns::META, columns::HEADER)?;
		let leaves = LeafSet::read_from_db(&*db, columns::META, meta_keys::LEAF_PREFIX)?;
		Ok(BlockchainDb {
			db,
			leaves: RwLock::new(leaves),
			meta: RwLock::new(meta),
		})
	}

	fn update_meta(
		&self,
		hash: Block::Hash,
		number: <Block::Header as HeaderT>::Number,
		is_best: bool,
		is_finalized: bool
	) {
		let mut meta = self.meta.write();
		if number == Zero::zero() {
			meta.genesis_hash = hash;
			meta.finalized_hash = hash;
		}

		if is_best {
			meta.best_number = number;
			meta.best_hash = hash;
		}

		if is_finalized {
			meta.finalized_number = number;
			meta.finalized_hash = hash;
		}
	}
}

impl<Block: BlockT> client::blockchain::HeaderBackend<Block> for BlockchainDb<Block> {
	fn header(&self, id: BlockId<Block>) -> Result<Option<Block::Header>, client::error::Error> {
		::utils::read_header(&*self.db, columns::HASH_LOOKUP, columns::HEADER, id)
	}

	fn info(&self) -> Result<client::blockchain::Info<Block>, client::error::Error> {
		let meta = self.meta.read();
		Ok(client::blockchain::Info {
			best_hash: meta.best_hash,
			best_number: meta.best_number,
			genesis_hash: meta.genesis_hash,
			finalized_hash: meta.finalized_hash,
			finalized_number: meta.finalized_number,
		})
	}

	fn status(&self, id: BlockId<Block>) -> Result<client::blockchain::BlockStatus, client::error::Error> {
		let exists = match id {
			BlockId::Hash(_) => read_db(
				&*self.db,
				columns::HASH_LOOKUP,
				columns::HEADER,
				id
			)?.is_some(),
			BlockId::Number(n) => n <= self.meta.read().best_number,
		};
		match exists {
			true => Ok(client::blockchain::BlockStatus::InChain),
			false => Ok(client::blockchain::BlockStatus::Unknown),
		}
	}

	fn number(&self, hash: Block::Hash) -> Result<Option<NumberFor<Block>>, client::error::Error> {
		if let Some(lookup_key) = block_id_to_lookup_key::<Block>(&*self.db, columns::HASH_LOOKUP, BlockId::Hash(hash))? {
			let number = utils::lookup_key_to_number(&lookup_key)?;
			Ok(Some(number))
		} else {
			Ok(None)
		}
	}

	fn hash(&self, number: NumberFor<Block>) -> Result<Option<Block::Hash>, client::error::Error> {
		self.header(BlockId::Number(number)).and_then(|maybe_header| match maybe_header {
			Some(header) => Ok(Some(header.hash().clone())),
			None => Ok(None),
		})
	}
}

impl<Block: BlockT> client::blockchain::Backend<Block> for BlockchainDb<Block> {
	fn body(&self, id: BlockId<Block>) -> Result<Option<Vec<Block::Extrinsic>>, client::error::Error> {
		match read_db(&*self.db, columns::HASH_LOOKUP, columns::BODY, id)? {
			Some(body) => match Decode::decode(&mut &body[..]) {
				Some(body) => Ok(Some(body)),
				None => return Err(client::error::ErrorKind::Backend("Error decoding body".into()).into()),
			}
			None => Ok(None),
		}
	}

	fn justification(&self, id: BlockId<Block>) -> Result<Option<Justification>, client::error::Error> {
		match read_db(&*self.db, columns::HASH_LOOKUP, columns::JUSTIFICATION, id)? {
			Some(justification) => match Decode::decode(&mut &justification[..]) {
				Some(justification) => Ok(Some(justification)),
				None => return Err(client::error::ErrorKind::Backend("Error decoding justification".into()).into()),
			}
			None => Ok(None),
		}
	}

	fn last_finalized(&self) -> Result<Block::Hash, client::error::Error> {
		Ok(self.meta.read().finalized_hash.clone())
	}

	fn cache(&self) -> Option<&client::blockchain::Cache<Block>> {
		None
	}

	fn leaves(&self) -> Result<Vec<Block::Hash>, client::error::Error> {
		Ok(self.leaves.read().hashes())
	}
}

/// Database transaction
pub struct BlockImportOperation<Block: BlockT, H: Hasher> {
	old_state: DbState,
	updates: MemoryDB<H>,
	changes_trie_updates: MemoryDB<H>,
	pending_block: Option<PendingBlock<Block>>,
}

impl<Block> client::backend::BlockImportOperation<Block, Blake2Hasher>
for BlockImportOperation<Block, Blake2Hasher>
where Block: BlockT,
{
	type State = DbState;

	fn state(&self) -> Result<Option<&Self::State>, client::error::Error> {
		Ok(Some(&self.old_state))
	}

	fn set_block_data(
		&mut self,
		header: Block::Header,
		body: Option<Vec<Block::Extrinsic>>,
		justification: Option<Justification>,
		leaf_state: NewBlockState,
	) -> Result<(), client::error::Error> {
		assert!(self.pending_block.is_none(), "Only one block per operation is allowed");
		self.pending_block = Some(PendingBlock {
			header,
			body,
			justification,
			leaf_state,
		});
		Ok(())
	}

	fn update_authorities(&mut self, _authorities: Vec<AuthorityId>) {
		// currently authorities are not cached on full nodes
	}

	fn update_storage(&mut self, update: MemoryDB<Blake2Hasher>) -> Result<(), client::error::Error> {
		self.updates = update;
		Ok(())
	}

	fn reset_storage<I: Iterator<Item=(Vec<u8>, Vec<u8>)>>(&mut self, iter: I) -> Result<(), client::error::Error> {
		// TODO: wipe out existing trie.
		let (_, update) = self.old_state.storage_root(iter.into_iter().map(|(k, v)| (k, Some(v))));
		self.updates = update;
		Ok(())
	}

	fn update_changes_trie(&mut self, update: MemoryDB<Blake2Hasher>) -> Result<(), client::error::Error> {
		self.changes_trie_updates = update;
		Ok(())
	}
}

struct StorageDb<Block: BlockT> {
	pub db: Arc<KeyValueDB>,
	pub state_db: StateDb<Block::Hash, H256>,
}

impl<Block: BlockT> state_machine::Storage<Blake2Hasher> for StorageDb<Block> {
	fn get(&self, key: &H256) -> Result<Option<DBValue>, String> {
		self.state_db.get(&key.0.into(), self).map(|r| r.map(|v| DBValue::from_slice(&v)))
			.map_err(|e| format!("Database backend error: {:?}", e))
	}
}

impl<Block: BlockT> state_db::HashDb for StorageDb<Block> {
	type Error = io::Error;
	type Hash = H256;

	fn get(&self, key: &H256) -> Result<Option<Vec<u8>>, Self::Error> {
		self.db.get(columns::STATE, &key[..]).map(|r| r.map(|v| v.to_vec()))
	}
}

struct DbGenesisStorage(pub H256);

impl DbGenesisStorage {
	pub fn new() -> Self {
		let mut root = H256::default();
		let mut mdb = MemoryDB::<Blake2Hasher>::default();	// TODO: use new() to make it more correct
		state_machine::TrieDBMut::<Blake2Hasher>::new(&mut mdb, &mut root);
		DbGenesisStorage(root)
	}
}

impl state_machine::Storage<Blake2Hasher> for DbGenesisStorage {
	fn get(&self, _key: &H256) -> Result<Option<DBValue>, String> {
		Ok(None)
	}
}

pub struct DbChangesTrieStorage<Block: BlockT> {
	db: Arc<KeyValueDB>,
	min_blocks_to_keep: Option<u64>,
	_phantom: ::std::marker::PhantomData<Block>,
}

impl<Block: BlockT> DbChangesTrieStorage<Block> {
	/// Commit new changes trie.
	pub fn commit(&self, tx: &mut DBTransaction, mut changes_trie: MemoryDB<Blake2Hasher>) {
		for (key, (val, _)) in changes_trie.drain() {
			tx.put(columns::CHANGES_TRIE, &key[..], &val);
		}
	}

	/// Prune obsolete changes tries.
	pub fn prune(&self, config: Option<ChangesTrieConfiguration>, tx: &mut DBTransaction, block: NumberFor<Block>) {
		// never prune on archive nodes
		let min_blocks_to_keep = match self.min_blocks_to_keep {
			Some(min_blocks_to_keep) => min_blocks_to_keep,
			None => return,
		};

		// read configuration from the database. it is OK to do it here (without checking tx for
		// modifications), since config can't change
		let config = match config {
			Some(config) => config,
			None => return,
		};

		state_machine::prune_changes_tries(
			&config,
			&*self,
			min_blocks_to_keep,
			block.as_(),
			|node| tx.delete(columns::CHANGES_TRIE, node.as_ref()));
	}
}

impl<Block: BlockT> state_machine::ChangesTrieRootsStorage<Blake2Hasher> for DbChangesTrieStorage<Block> {
	fn root(&self, block: u64) -> Result<Option<H256>, String> {
		Ok(read_db::<Block>(&*self.db, columns::HASH_LOOKUP, columns::HEADER, BlockId::Number(As::sa(block)))
			.map_err(|err| format!("{}", err))
			.and_then(|header| match header {
				Some(header) => Block::Header::decode(&mut &header[..])
					.ok_or_else(|| format!("Failed to parse header of block {}", block))
					.map(Some),
				None => Ok(None)
			})?
			.and_then(|header| header.digest().log(DigestItem::as_changes_trie_root)
				.map(|root| H256::from_slice(root.as_ref()))))
	}
}

impl<Block: BlockT> state_machine::ChangesTrieStorage<Blake2Hasher> for DbChangesTrieStorage<Block> {
	fn get(&self, key: &H256) -> Result<Option<DBValue>, String> {
		self.db.get(columns::CHANGES_TRIE, &key[..])
			.map_err(|err| format!("{}", err))
	}
}

/// Disk backend. Keeps data in a key-value store. In archive mode, trie nodes are kept from all blocks.
/// Otherwise, trie nodes are kept only from some recent blocks.
pub struct Backend<Block: BlockT> {
	storage: Arc<StorageDb<Block>>,
	changes_tries_storage: DbChangesTrieStorage<Block>,
	blockchain: BlockchainDb<Block>,
	canonicalization_delay: u64,
}

impl<Block: BlockT> Backend<Block> {
	/// Create a new instance of database backend.
	///
	/// The pruning window is how old a block must be before the state is pruned.
	pub fn new(config: DatabaseSettings, canonicalization_delay: u64) -> Result<Self, client::error::Error> {
		let db = open_database(&config, columns::META, "full")?;

		Backend::from_kvdb(db as Arc<_>, config.pruning, canonicalization_delay)
	}

	#[cfg(test)]
	fn new_test(keep_blocks: u32, canonicalization_delay: u64) -> Self {
		use utils::NUM_COLUMNS;

		let db = Arc::new(::kvdb_memorydb::create(NUM_COLUMNS));

		Backend::from_kvdb(
			db as Arc<_>,
			PruningMode::keep_blocks(keep_blocks),
			canonicalization_delay,
		).expect("failed to create test-db")
	}

	fn from_kvdb(db: Arc<KeyValueDB>, pruning: PruningMode, canonicalization_delay: u64) -> Result<Self, client::error::Error> {
		let is_archive_pruning = pruning.is_archive();
		let blockchain = BlockchainDb::new(db.clone())?;
		let map_e = |e: state_db::Error<io::Error>| ::client::error::Error::from(format!("State database error: {:?}", e));
		let state_db: StateDb<Block::Hash, H256> = StateDb::new(pruning, &StateMetaDb(&*db)).map_err(map_e)?;
		let storage_db = StorageDb {
			db: db.clone(),
			state_db,
		};
		let changes_tries_storage = DbChangesTrieStorage {
			db,
			min_blocks_to_keep: if is_archive_pruning { None } else { Some(MIN_BLOCKS_TO_KEEP_CHANGES_TRIES_FOR) },
			_phantom: Default::default(),
		};

		Ok(Backend {
			storage: Arc::new(storage_db),
			changes_tries_storage,
			blockchain,
			canonicalization_delay,
		})
	}

	// performs forced canonicaliziation with a delay after importning a non-finalized block.
	fn force_delayed_canonicalize(
		&self,
		transaction: &mut DBTransaction,
		hash: Block::Hash,
		number: NumberFor<Block>,
	)
		-> Result<(), client::error::Error>
	{
		let number_u64 = number.as_();
		if number_u64 > self.canonicalization_delay {
			let new_canonical = number_u64 - self.canonicalization_delay;

			if new_canonical <= self.storage.state_db.best_canonical() {
				return Ok(())
			}

			let hash = if new_canonical == number_u64 {
				hash
			} else {
				::client::blockchain::HeaderBackend::hash(&self.blockchain, As::sa(new_canonical))?
					.expect("existence of block with number `new_canonical` \
						implies existence of blocks with all numbers before it; qed")
			};

			trace!(target: "db", "Canonicalize block #{} ({:?})", new_canonical, hash);
			let commit = self.storage.state_db.canonicalize_block(&hash);
			apply_state_commit(transaction, commit);
		};

		Ok(())
	}

	// write stuff to a transaction after a new block is finalized.
	// this canonicalizes finalized blocks. Fails if called with a block which
	// was not a child of the last finalized block.
	fn note_finalized(
		&self,
		transaction: &mut DBTransaction,
		f_header: &Block::Header,
		f_hash: Block::Hash,
	) -> Result<(), client::error::Error> {
		let meta = self.blockchain.meta.read();
		let f_num = f_header.number().clone();

		if f_num.as_() > self.storage.state_db.best_canonical() {
			let parent_hash = f_header.parent_hash().clone();
			if meta.finalized_hash != parent_hash {
				return Err(::client::error::ErrorKind::NonSequentialFinalization(
					format!("Last finalized {:?} not parent of {:?}",
						meta.finalized_hash, f_hash),
				).into())
			}
			transaction.put(columns::META, meta_keys::FINALIZED_BLOCK, f_hash.as_ref());

			let commit = self.storage.state_db.canonicalize_block(&f_hash);
			apply_state_commit(transaction, commit);

			// read config from genesis, since it is readonly atm
			use client::backend::Backend;
			let changes_trie_config: Option<ChangesTrieConfiguration> = self.state_at(BlockId::Hash(parent_hash))?
				.storage(well_known_keys::CHANGES_TRIE_CONFIG)?
				.and_then(|v| Decode::decode(&mut &*v));
			self.changes_tries_storage.prune(changes_trie_config, transaction, f_num);
		}

		Ok(())
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

impl<Block> client::backend::Backend<Block, Blake2Hasher> for Backend<Block> where Block: BlockT {
	type BlockImportOperation = BlockImportOperation<Block, Blake2Hasher>;
	type Blockchain = BlockchainDb<Block>;
	type State = DbState;
	type ChangesTrieStorage = DbChangesTrieStorage<Block>;

	fn begin_operation(&self, block: BlockId<Block>) -> Result<Self::BlockImportOperation, client::error::Error> {
		let state = self.state_at(block)?;
		Ok(BlockImportOperation {
			pending_block: None,
			old_state: state,
			updates: MemoryDB::default(),
			changes_trie_updates: MemoryDB::default(),
		})
	}

	fn commit_operation(&self, mut operation: Self::BlockImportOperation)
		-> Result<(), client::error::Error>
	{
		let mut transaction = DBTransaction::new();
		if let Some(pending_block) = operation.pending_block {
			let hash = pending_block.header.hash();
			let parent_hash = *pending_block.header.parent_hash();
			let number = pending_block.header.number().clone();

			if pending_block.leaf_state.is_best() {
				let meta = self.blockchain.meta.read();

				// cannot find tree route with empty DB.
				if meta.best_hash != Default::default() {
					let tree_route = ::client::blockchain::tree_route(
						&self.blockchain,
						BlockId::Hash(meta.best_hash),
						BlockId::Hash(parent_hash),
					)?;

					// uncanonicalize
					for retracted in tree_route.retracted() {
						if retracted.hash == meta.finalized_hash {
							warn!("Potential safety failure: reverting finalized block {:?}",
								(&retracted.number, &retracted.hash));

							return Err(::client::error::ErrorKind::NotInFinalizedChain.into());
						}

						let prev_lookup_key = ::utils::number_to_lookup_key(retracted.number);
						let new_lookup_key = ::utils::number_and_hash_to_lookup_key(retracted.number, retracted.hash);

						// change mapping from `number -> header`
						// to `number + hash -> header`
						let retracted_header = if let Some(header) = ::client::blockchain::HeaderBackend::<Block>::header(&self.blockchain, BlockId::Number(retracted.number))? {
							header
						} else {
							return Err(client::error::ErrorKind::UnknownBlock(format!("retracted {:?}", retracted)).into());
						};
						transaction.delete(columns::HEADER, &prev_lookup_key);
						transaction.put(columns::HEADER, &new_lookup_key, &retracted_header.encode());

						// if body is stored
						// change mapping from `number -> body`
						// to `number + hash -> body`
						if let Some(retracted_body) = ::client::blockchain::Backend::<Block>::body(&self.blockchain, BlockId::Number(retracted.number))? {
							transaction.delete(columns::BODY, &prev_lookup_key);
							transaction.put(columns::BODY, &new_lookup_key, &retracted_body.encode());
						}

						// if justification is stored
						// change mapping from `number -> justification`
						// to `number + hash -> justification`
						if let Some(retracted_justification) = ::client::blockchain::Backend::<Block>::justification(&self.blockchain, BlockId::Number(retracted.number))? {
							transaction.delete(columns::JUSTIFICATION, &prev_lookup_key);
							transaction.put(columns::JUSTIFICATION, &new_lookup_key, &retracted_justification.encode());
						}

						transaction.put(columns::HASH_LOOKUP, retracted.hash.as_ref(), &new_lookup_key);
					}

					// canonicalize
					for enacted in tree_route.enacted() {
						let prev_lookup_key = ::utils::number_and_hash_to_lookup_key(enacted.number, enacted.hash);
						let new_lookup_key = ::utils::number_to_lookup_key(enacted.number);

						// change mapping from `number + hash -> header`
						// to `number -> header`
						let enacted_header = if let Some(header) = ::client::blockchain::HeaderBackend::<Block>::header(&self.blockchain, BlockId::Number(enacted.number))? {
							header
						} else {
							return Err(client::error::ErrorKind::UnknownBlock(format!("enacted {:?}", enacted)).into());
						};
						transaction.delete(columns::HEADER, &prev_lookup_key);
						transaction.put(columns::HEADER, &new_lookup_key, &enacted_header.encode());

						// if body is stored
						// change mapping from `number + hash -> body`
						// to `number -> body`
						if let Some(enacted_body) = ::client::blockchain::Backend::<Block>::body(&self.blockchain, BlockId::Number(enacted.number))? {
							transaction.delete(columns::BODY, &prev_lookup_key);
							transaction.put(columns::BODY, &new_lookup_key, &enacted_body.encode());
						}

						// if justification is stored
						// change mapping from `number -> justification`
						// to `number + hash -> justification`
						if let Some(enacted_justification) = ::client::blockchain::Backend::<Block>::justification(&self.blockchain, BlockId::Number(enacted.number))? {
							transaction.delete(columns::JUSTIFICATION, &prev_lookup_key);
							transaction.put(columns::JUSTIFICATION, &new_lookup_key, &enacted_justification.encode());
						}

						transaction.put(columns::HASH_LOOKUP, enacted.hash.as_ref(), &new_lookup_key);
					}
				}

				transaction.put(columns::META, meta_keys::BEST_BLOCK, hash.as_ref());
			}

			// blocks in longest chain are keyed by number
			let lookup_key = if pending_block.leaf_state.is_best() {
				::utils::number_to_lookup_key(number).to_vec()
			} else {
			// other blocks are keyed by number + hash
				::utils::number_and_hash_to_lookup_key(number, hash)
			};

			transaction.put(columns::HEADER, &lookup_key, &pending_block.header.encode());
			if let Some(body) = pending_block.body {
				transaction.put(columns::BODY, &lookup_key, &body.encode());
			}
			if let Some(justification) = pending_block.justification {
				transaction.put(columns::JUSTIFICATION, &lookup_key, &justification.encode());
			}

			transaction.put(columns::HASH_LOOKUP, hash.as_ref(), &lookup_key);

			if number == Zero::zero() {
				transaction.put(columns::META, meta_keys::FINALIZED_BLOCK, hash.as_ref());
				transaction.put(columns::META, meta_keys::GENESIS_HASH, hash.as_ref());
			}

			let mut changeset: state_db::ChangeSet<H256> = state_db::ChangeSet::default();
			for (key, (val, rc)) in operation.updates.drain() {
				if rc > 0 {
					changeset.inserted.push((key.0.into(), val.to_vec()));
				} else if rc < 0 {
					changeset.deleted.push(key.0.into());
				}
			}
			let number_u64 = number.as_();
			let commit = self.storage.state_db.insert_block(&hash, number_u64, &pending_block.header.parent_hash(), changeset)
				.map_err(|e: state_db::Error<io::Error>| client::error::Error::from(format!("State database error: {:?}", e)))?;
			apply_state_commit(&mut transaction, commit);
			self.changes_tries_storage.commit(&mut transaction, operation.changes_trie_updates);

			let finalized = match pending_block.leaf_state {
				NewBlockState::Final => true,
				_ => false,
			};

			if finalized {
				// TODO: ensure best chain contains this block.
				self.note_finalized(&mut transaction, &pending_block.header, hash)?;
			} else {
				// canonicalize blocks which are old enough, regardless of finality.
				self.force_delayed_canonicalize(&mut transaction, hash, *pending_block.header.number())?
			}

			debug!(target: "db", "DB Commit {:?} ({}), best = {}", hash, number,
				pending_block.leaf_state.is_best());

			{
				let mut leaves = self.blockchain.leaves.write();
				let displaced_leaf = leaves.import(hash, number, parent_hash);
				leaves.prepare_transaction(&mut transaction, columns::META, meta_keys::LEAF_PREFIX);

				let write_result = self.storage.db.write(transaction).map_err(db_err);
				if let Err(e) = write_result {
					// revert leaves set update, if there was one.
					if let Some(displaced_leaf) = displaced_leaf {
						leaves.undo(displaced_leaf);
					}
					return Err(e);
				}
				drop(leaves);
			}

			self.blockchain.update_meta(
				hash.clone(),
				number.clone(),
				pending_block.leaf_state.is_best(),
				finalized,
			);
		}
		Ok(())
	}

	fn finalize_block(&self, block: BlockId<Block>) -> Result<(), client::error::Error> {
		use runtime_primitives::traits::Header;

		if let Some(header) = ::client::blockchain::HeaderBackend::header(&self.blockchain, block)? {
			let mut transaction = DBTransaction::new();
			// TODO: ensure best chain contains this block.
			let hash = header.hash();
			self.note_finalized(&mut transaction, &header, hash.clone())?;
			self.storage.db.write(transaction).map_err(db_err)?;
			self.blockchain.update_meta(hash, header.number().clone(), false, true);
			Ok(())
		} else {
			Err(client::error::ErrorKind::UnknownBlock(format!("Cannot finalize block {:?}", block)).into())
		}
	}

	fn changes_trie_storage(&self) -> Option<&Self::ChangesTrieStorage> {
		Some(&self.changes_tries_storage)
	}

	fn revert(&self, n: NumberFor<Block>) -> Result<NumberFor<Block>, client::error::Error> {
		use client::blockchain::HeaderBackend;
		let mut best = self.blockchain.info()?.best_number;
		for c in 0 .. n.as_() {
			if best == As::sa(0) {
				return Ok(As::sa(c))
			}
			let mut transaction = DBTransaction::new();
			match self.storage.state_db.revert_one() {
				Some(commit) => {
					apply_state_commit(&mut transaction, commit);
					let removed = best.clone();
					best -= As::sa(1);
					let header = self.blockchain.header(BlockId::Number(best))?.ok_or_else(
						|| client::error::ErrorKind::UnknownBlock(
							format!("Error reverting to {}. Block header not found.", best)))?;

					transaction.put(columns::META, meta_keys::BEST_BLOCK, header.hash().as_ref());
					transaction.delete(columns::HASH_LOOKUP, header.hash().as_ref());
					self.storage.db.write(transaction).map_err(db_err)?;
					self.blockchain.update_meta(header.hash().clone(), best.clone(), true, false);
					self.blockchain.leaves.write().revert(header.hash().clone(), header.number().clone(), header.parent_hash().clone());
				}
				None => return Ok(As::sa(c))
			}
		}
		Ok(n)
	}

	fn blockchain(&self) -> &BlockchainDb<Block> {
		&self.blockchain
	}

	fn state_at(&self, block: BlockId<Block>) -> Result<Self::State, client::error::Error> {
		use client::blockchain::HeaderBackend as BcHeaderBackend;

		// special case for genesis initialization
		match block {
			BlockId::Hash(h) if h == Default::default() => {
				let genesis_storage = DbGenesisStorage::new();
				let root = genesis_storage.0.clone();
				return Ok(DbState::new(Arc::new(genesis_storage), root));
			},
			_ => {}
		}

		match self.blockchain.header(block) {
			Ok(Some(ref hdr)) if !self.storage.state_db.is_pruned(hdr.number().as_()) => {
				let root = H256::from_slice(hdr.state_root().as_ref());
				Ok(DbState::new(self.storage.clone(), root))
			},
			Err(e) => Err(e),
			_ => Err(client::error::ErrorKind::UnknownBlock(format!("{:?}", block)).into()),
		}
	}

	fn insert_aux<'a, 'b: 'a, 'c: 'a, I: IntoIterator<Item=&'a (&'c [u8], &'c [u8])>, D: IntoIterator<Item=&'a &'b [u8]>>
		(&self, insert: I, delete: D) -> Result<(), client::error::Error>
	{
		let mut transaction = DBTransaction::new();
		for (k, v) in insert {
			transaction.put(columns::AUX, k, v);
		}
		for k in delete {
			transaction.delete(columns::AUX, k);
		}
		self.storage.db.write(transaction).map_err(db_err)?;
		Ok(())
	}

	fn get_aux(&self, key: &[u8]) -> Result<Option<Vec<u8>>, client::error::Error> {
		Ok(self.storage.db.get(columns::AUX, key).map(|r| r.map(|v| v.to_vec())).map_err(db_err)?)
	}
}

impl<Block> client::backend::LocalBackend<Block, Blake2Hasher> for Backend<Block>
where Block: BlockT {}

#[cfg(test)]
mod tests {
	use hash_db::HashDB;
	use super::*;
	use client::backend::Backend as BTrait;
	use client::backend::BlockImportOperation as Op;
	use client::blockchain::HeaderBackend as BlockchainHeaderBackend;
	use runtime_primitives::testing::{Header, Block as RawBlock};
	use state_machine::{TrieMut, TrieDBMut, ChangesTrieRootsStorage, ChangesTrieStorage};
	use test_client;

	type Block = RawBlock<u64>;

	fn prepare_changes(changes: Vec<(Vec<u8>, Vec<u8>)>) -> (H256, MemoryDB<Blake2Hasher>) {
		let mut changes_root = H256::default();
		let mut changes_trie_update = MemoryDB::<Blake2Hasher>::default();		// TODO: change to new() to make more correct
		{
			let mut trie = TrieDBMut::<Blake2Hasher>::new(
				&mut changes_trie_update,
				&mut changes_root
			);
			for (key, value) in changes {
				trie.insert(&key, &value).unwrap();
			}
		}

		(changes_root, changes_trie_update)
	}

	fn insert_header(
		backend: &Backend<Block>,
		number: u64,
		parent_hash: H256,
		changes: Vec<(Vec<u8>, Vec<u8>)>,
		extrinsics_root: H256,
	) -> H256 {
		use runtime_primitives::generic::DigestItem;
		use runtime_primitives::testing::Digest;

		let (changes_root, changes_trie_update) = prepare_changes(changes);
		let digest = Digest {
			logs: vec![
				DigestItem::ChangesTrieRoot(changes_root),
			],
		};
		let header = Header {
			number,
			parent_hash,
			state_root: Default::default(),
			digest,
			extrinsics_root,
		};
		let header_hash = header.hash();

		let block_id = if number == 0 {
			BlockId::Hash(Default::default())
		} else {
			BlockId::Number(number - 1)
		};
		let mut op = backend.begin_operation(block_id).unwrap();
		op.set_block_data(header, None, None, NewBlockState::Best).unwrap();
		op.update_changes_trie(changes_trie_update).unwrap();
		backend.commit_operation(op).unwrap();

		header_hash
	}

	#[test]
	fn block_hash_inserted_correctly() {
		let db = Backend::<Block>::new_test(1, 0);
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
					NewBlockState::Best,
				).unwrap();
				db.commit_operation(op).unwrap();
			}

			assert!(db.blockchain().hash(i).unwrap().is_some())
		}
	}

	#[test]
	fn set_state_data() {
		let db = Backend::<Block>::new_test(2, 0);
		let hash = {
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
			let hash = header.hash();

			op.reset_storage(storage.iter().cloned()).unwrap();
			op.set_block_data(
				header.clone(),
				Some(vec![]),
				None,
				NewBlockState::Best,
			).unwrap();

			db.commit_operation(op).unwrap();

			let state = db.state_at(BlockId::Number(0)).unwrap();

			assert_eq!(state.storage(&[1, 3, 5]).unwrap(), Some(vec![2, 4, 6]));
			assert_eq!(state.storage(&[1, 2, 3]).unwrap(), Some(vec![9, 9, 9]));
			assert_eq!(state.storage(&[5, 5, 5]).unwrap(), None);

			hash
		};

		{
			let mut op = db.begin_operation(BlockId::Number(0)).unwrap();
			let mut header = Header {
				number: 1,
				parent_hash: hash,
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
				NewBlockState::Best,
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
		let backend = Backend::<Block>::new_test(0, 0);

		let hash = {
			let mut op = backend.begin_operation(BlockId::Hash(Default::default())).unwrap();
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
			let hash = header.hash();

			op.reset_storage(storage.iter().cloned()).unwrap();

			key = op.updates.insert(b"hello");
			op.set_block_data(
				header,
				Some(vec![]),
				None,
				NewBlockState::Best,
			).unwrap();

			backend.commit_operation(op).unwrap();

			assert_eq!(backend.storage.db.get(::columns::STATE, &key.0[..]).unwrap().unwrap(), &b"hello"[..]);
			hash
		};

		let hash = {
			let mut op = backend.begin_operation(BlockId::Number(0)).unwrap();
			let mut header = Header {
				number: 1,
				parent_hash: hash,
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
			let hash = header.hash();

			op.updates.insert(b"hello");
			op.updates.remove(&key);
			op.set_block_data(
				header,
				Some(vec![]),
				None,
				NewBlockState::Best,
			).unwrap();

			backend.commit_operation(op).unwrap();

			assert_eq!(backend.storage.db.get(::columns::STATE, &key.0[..]).unwrap().unwrap(), &b"hello"[..]);
			hash
		};

		{
			let mut op = backend.begin_operation(BlockId::Number(1)).unwrap();
			let mut header = Header {
				number: 2,
				parent_hash: hash,
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
				NewBlockState::Best,
			).unwrap();

			backend.commit_operation(op).unwrap();

			assert!(backend.storage.db.get(::columns::STATE, &key.0[..]).unwrap().is_none());
		}

		backend.finalize_block(BlockId::Number(1)).unwrap();
		backend.finalize_block(BlockId::Number(2)).unwrap();
		assert!(backend.storage.db.get(::columns::STATE, &key.0[..]).unwrap().is_none());
	}

	#[test]
	fn changes_trie_storage_works() {
		let backend = Backend::<Block>::new_test(1000, 100);

		let check_changes = |backend: &Backend<Block>, block: u64, changes: Vec<(Vec<u8>, Vec<u8>)>| {
			let (changes_root, mut changes_trie_update) = prepare_changes(changes);
			assert_eq!(backend.changes_tries_storage.root(block), Ok(Some(changes_root)));

			for (key, (val, _)) in changes_trie_update.drain() {
				assert_eq!(backend.changes_trie_storage().unwrap().get(&key), Ok(Some(val)));
			}
		};

		let changes0 = vec![(b"key_at_0".to_vec(), b"val_at_0".to_vec())];
		let changes1 = vec![
			(b"key_at_1".to_vec(), b"val_at_1".to_vec()),
			(b"another_key_at_1".to_vec(), b"another_val_at_1".to_vec()),
		];
		let changes2 = vec![(b"key_at_2".to_vec(), b"val_at_2".to_vec())];

		let block0 = insert_header(&backend, 0, Default::default(), changes0.clone(), Default::default());
		let block1 = insert_header(&backend, 1, block0, changes1.clone(), Default::default());
		let _ = insert_header(&backend, 2, block1, changes2.clone(), Default::default());

		// check that the storage contains tries for all blocks
		check_changes(&backend, 0, changes0);
		check_changes(&backend, 1, changes1);
		check_changes(&backend, 2, changes2);
	}

	#[test]
	fn changes_tries_are_pruned_on_finalization() {
		let mut backend = Backend::<Block>::new_test(1000, 100);
		backend.changes_tries_storage.min_blocks_to_keep = Some(8);
		let config = ChangesTrieConfiguration {
			digest_interval: 2,
			digest_levels: 2,
		};

		// insert some blocks
		let block0 = insert_header(&backend, 0, Default::default(), vec![(b"key_at_0".to_vec(), b"val_at_0".to_vec())], Default::default());
		let block1 = insert_header(&backend, 1, block0, vec![(b"key_at_1".to_vec(), b"val_at_1".to_vec())], Default::default());
		let block2 = insert_header(&backend, 2, block1, vec![(b"key_at_2".to_vec(), b"val_at_2".to_vec())], Default::default());
		let block3 = insert_header(&backend, 3, block2, vec![(b"key_at_3".to_vec(), b"val_at_3".to_vec())], Default::default());
		let block4 = insert_header(&backend, 4, block3, vec![(b"key_at_4".to_vec(), b"val_at_4".to_vec())], Default::default());
		let block5 = insert_header(&backend, 5, block4, vec![(b"key_at_5".to_vec(), b"val_at_5".to_vec())], Default::default());
		let block6 = insert_header(&backend, 6, block5, vec![(b"key_at_6".to_vec(), b"val_at_6".to_vec())], Default::default());
		let block7 = insert_header(&backend, 7, block6, vec![(b"key_at_7".to_vec(), b"val_at_7".to_vec())], Default::default());
		let block8 = insert_header(&backend, 8, block7, vec![(b"key_at_8".to_vec(), b"val_at_8".to_vec())], Default::default());
		let block9 = insert_header(&backend, 9, block8, vec![(b"key_at_9".to_vec(), b"val_at_9".to_vec())], Default::default());
		let block10 = insert_header(&backend, 10, block9, vec![(b"key_at_10".to_vec(), b"val_at_10".to_vec())], Default::default());
		let block11 = insert_header(&backend, 11, block10, vec![(b"key_at_11".to_vec(), b"val_at_11".to_vec())], Default::default());
		let _ = insert_header(&backend, 12, block11, vec![(b"key_at_12".to_vec(), b"val_at_12".to_vec())], Default::default());

		// check that roots of all tries are in the columns::CHANGES_TRIE
		fn read_changes_trie_root(backend: &Backend<Block>, num: u64) -> H256 {
			backend.blockchain().header(BlockId::Number(num)).unwrap().unwrap().digest().logs().iter()
				.find(|i| i.as_changes_trie_root().is_some()).unwrap().as_changes_trie_root().unwrap().clone()
		}
		let root1 = read_changes_trie_root(&backend, 1); assert_eq!(backend.changes_tries_storage.root(1).unwrap(), Some(root1));
		let root2 = read_changes_trie_root(&backend, 2); assert_eq!(backend.changes_tries_storage.root(2).unwrap(), Some(root2));
		let root3 = read_changes_trie_root(&backend, 3); assert_eq!(backend.changes_tries_storage.root(3).unwrap(), Some(root3));
		let root4 = read_changes_trie_root(&backend, 4); assert_eq!(backend.changes_tries_storage.root(4).unwrap(), Some(root4));
		let root5 = read_changes_trie_root(&backend, 5); assert_eq!(backend.changes_tries_storage.root(5).unwrap(), Some(root5));
		let root6 = read_changes_trie_root(&backend, 6); assert_eq!(backend.changes_tries_storage.root(6).unwrap(), Some(root6));
		let root7 = read_changes_trie_root(&backend, 7); assert_eq!(backend.changes_tries_storage.root(7).unwrap(), Some(root7));
		let root8 = read_changes_trie_root(&backend, 8); assert_eq!(backend.changes_tries_storage.root(8).unwrap(), Some(root8));
		let root9 = read_changes_trie_root(&backend, 9); assert_eq!(backend.changes_tries_storage.root(9).unwrap(), Some(root9));
		let root10 = read_changes_trie_root(&backend, 10); assert_eq!(backend.changes_tries_storage.root(10).unwrap(), Some(root10));
		let root11 = read_changes_trie_root(&backend, 11); assert_eq!(backend.changes_tries_storage.root(11).unwrap(), Some(root11));
		let root12 = read_changes_trie_root(&backend, 12); assert_eq!(backend.changes_tries_storage.root(12).unwrap(), Some(root12));

		// now simulate finalization of block#12, causing prune of tries at #1..#4
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(Some(config.clone()), &mut tx, 12);
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root1).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root2).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root3).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root4).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root5).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root6).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root7).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root8).unwrap().is_some());

		// now simulate finalization of block#16, causing prune of tries at #5..#8
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(Some(config.clone()), &mut tx, 16);
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root5).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root6).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root7).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root8).unwrap().is_none());

		// now "change" pruning mode to archive && simulate finalization of block#20
		// => no changes tries are pruned, because we never prune in archive mode
		backend.changes_tries_storage.min_blocks_to_keep = None;
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(Some(config), &mut tx, 20);
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root9).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root10).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root11).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root12).unwrap().is_some());
	}

	#[test]
	fn tree_route_works() {
		let backend = Backend::<Block>::new_test(1000, 100);
		let block0 = insert_header(&backend, 0, Default::default(), Vec::new(), Default::default());

		// fork from genesis: 3 prong.
		let a1 = insert_header(&backend, 1, block0, Vec::new(), Default::default());
		let a2 = insert_header(&backend, 2, a1, Vec::new(), Default::default());
		let a3 = insert_header(&backend, 3, a2, Vec::new(), Default::default());

		// fork from genesis: 2 prong.
		let b1 = insert_header(&backend, 1, block0, Vec::new(), H256::from([1; 32]));
		let b2 = insert_header(&backend, 2, b1, Vec::new(), Default::default());

		{
			let tree_route = ::client::blockchain::tree_route(
				backend.blockchain(),
				BlockId::Hash(a3),
				BlockId::Hash(b2)
			).unwrap();

			assert_eq!(tree_route.common_block().hash, block0);
			assert_eq!(tree_route.retracted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![a3, a2, a1]);
			assert_eq!(tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![b1, b2]);
		}

		{
			let tree_route = ::client::blockchain::tree_route(
				backend.blockchain(),
				BlockId::Hash(a1),
				BlockId::Hash(a3),
			).unwrap();

			assert_eq!(tree_route.common_block().hash, a1);
			assert!(tree_route.retracted().is_empty());
			assert_eq!(tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![a2, a3]);
		}

		{
			let tree_route = ::client::blockchain::tree_route(
				backend.blockchain(),
				BlockId::Hash(a3),
				BlockId::Hash(a1),
			).unwrap();

			assert_eq!(tree_route.common_block().hash, a1);
			assert_eq!(tree_route.retracted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![a3, a2]);
			assert!(tree_route.enacted().is_empty());
		}

		{
			let tree_route = ::client::blockchain::tree_route(
				backend.blockchain(),
				BlockId::Hash(a2),
				BlockId::Hash(a2),
			).unwrap();

			assert_eq!(tree_route.common_block().hash, a2);
			assert!(tree_route.retracted().is_empty());
			assert!(tree_route.enacted().is_empty());
		}
	}

	#[test]
	fn test_leaves_with_complex_block_tree() {
		let backend: Arc<Backend<test_client::runtime::Block>> = Arc::new(Backend::new_test(20, 20));
		test_client::trait_tests::test_leaves_for_backend(backend);
	}

	#[test]
	fn test_blockchain_query_by_number_gets_canonical() {
		let backend: Arc<Backend<test_client::runtime::Block>> = Arc::new(Backend::new_test(20, 20));
		test_client::trait_tests::test_blockchain_query_by_number_gets_canonical(backend);
	}

	#[test]
	fn test_aux() {
		let backend: Backend<test_client::runtime::Block> = Backend::new_test(0, 0);
		assert!(backend.get_aux(b"test").unwrap().is_none());
		backend.insert_aux(&[(&b"test"[..], &b"hello"[..])], &[]).unwrap();
		assert_eq!(b"hello", &backend.get_aux(b"test").unwrap().unwrap()[..]);
		backend.insert_aux(&[], &[&b"test"[..]]).unwrap();
		assert!(backend.get_aux(b"test").unwrap().is_none());
	}
}
