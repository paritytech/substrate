// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Client backend that is backed by a database.
//!
//! # Canonicality vs. Finality
//!
//! Finality indicates that a block will not be reverted, according to the consensus algorithm,
//! while canonicality indicates that the block may be reverted, but we will be unable to do so,
//! having discarded heavy state that will allow a chain reorganization.
//!
//! Finality implies canonicality but not vice-versa.

#![warn(missing_docs)]

pub mod offchain;

pub mod bench;

mod children;
mod parity_db;
mod record_stats_state;
mod stats;
#[cfg(any(feature = "rocksdb", test))]
mod upgrade;
mod utils;

use linked_hash_map::LinkedHashMap;
use log::{debug, trace, warn};
use parking_lot::{Mutex, RwLock};
use std::{
	collections::{HashMap, HashSet},
	io,
	path::{Path, PathBuf},
	sync::Arc,
};

use crate::{
	record_stats_state::RecordStatsState,
	stats::StateUsageStats,
	utils::{meta_keys, read_db, read_meta, DatabaseType, Meta},
};
use codec::{Decode, Encode};
use hash_db::Prefix;
use sc_client_api::{
	backend::NewBlockState,
	leaves::{FinalizationOutcome, LeafSet},
	utils::is_descendent_of,
	IoInfo, MemoryInfo, MemorySize, UsageInfo,
};
use sc_state_db::{IsPruned, StateDb};
use sp_arithmetic::traits::Saturating;
use sp_blockchain::{
	well_known_cache_keys, Backend as _, CachedHeaderMetadata, Error as ClientError, HeaderBackend,
	HeaderMetadata, HeaderMetadataCache, Result as ClientResult,
};
use sp_core::{
	offchain::OffchainOverlayedChange,
	storage::{well_known_keys, ChildInfo},
};
use sp_database::Transaction;
use sp_runtime::{
	generic::BlockId,
	traits::{
		Block as BlockT, Hash, HashFor, Header as HeaderT, NumberFor, One, SaturatedConversion,
		Zero,
	},
	Justification, Justifications, StateVersion, Storage,
};
use sp_state_machine::{
	backend::{AsTrieBackend, Backend as StateBackend},
	ChildStorageCollection, DBValue, IndexOperation, OffchainChangesCollection, StateMachineStats,
	StorageCollection, UsageInfo as StateUsageInfo,
};
use sp_trie::{cache::SharedTrieCache, prefixed_key, MemoryDB, PrefixedMemoryDB};

// Re-export the Database trait so that one can pass an implementation of it.
pub use sc_state_db::PruningMode;
pub use sp_database::Database;

pub use bench::BenchmarkingState;

const CACHE_HEADERS: usize = 8;

/// DB-backed patricia trie state, transaction type is an overlay of changes to commit.
pub type DbState<B> =
	sp_state_machine::TrieBackend<Arc<dyn sp_state_machine::Storage<HashFor<B>>>, HashFor<B>>;

/// Builder for [`DbState`].
pub type DbStateBuilder<B> = sp_state_machine::TrieBackendBuilder<
	Arc<dyn sp_state_machine::Storage<HashFor<B>>>,
	HashFor<B>,
>;

/// Length of a [`DbHash`].
const DB_HASH_LEN: usize = 32;

/// Hash type that this backend uses for the database.
pub type DbHash = sp_core::H256;

/// An extrinsic entry in the database.
#[derive(Debug, Encode, Decode)]
enum DbExtrinsic<B: BlockT> {
	/// Extrinsic that contains indexed data.
	Indexed {
		/// Hash of the indexed part.
		hash: DbHash,
		/// Extrinsic header.
		header: Vec<u8>,
	},
	/// Complete extrinsic data.
	Full(B::Extrinsic),
}

/// A reference tracking state.
///
/// It makes sure that the hash we are using stays pinned in storage
/// until this structure is dropped.
pub struct RefTrackingState<Block: BlockT> {
	state: DbState<Block>,
	storage: Arc<StorageDb<Block>>,
	parent_hash: Option<Block::Hash>,
}

impl<B: BlockT> RefTrackingState<B> {
	fn new(state: DbState<B>, storage: Arc<StorageDb<B>>, parent_hash: Option<B::Hash>) -> Self {
		RefTrackingState { state, parent_hash, storage }
	}
}

impl<B: BlockT> Drop for RefTrackingState<B> {
	fn drop(&mut self) {
		if let Some(hash) = &self.parent_hash {
			self.storage.state_db.unpin(hash);
		}
	}
}

impl<Block: BlockT> std::fmt::Debug for RefTrackingState<Block> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "Block {:?}", self.parent_hash)
	}
}

impl<B: BlockT> StateBackend<HashFor<B>> for RefTrackingState<B> {
	type Error = <DbState<B> as StateBackend<HashFor<B>>>::Error;
	type Transaction = <DbState<B> as StateBackend<HashFor<B>>>::Transaction;
	type TrieBackendStorage = <DbState<B> as StateBackend<HashFor<B>>>::TrieBackendStorage;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.storage(key)
	}

	fn storage_hash(&self, key: &[u8]) -> Result<Option<B::Hash>, Self::Error> {
		self.state.storage_hash(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.child_storage(child_info, key)
	}

	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<B::Hash>, Self::Error> {
		self.state.child_storage_hash(child_info, key)
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		self.state.exists_storage(key)
	}

	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<bool, Self::Error> {
		self.state.exists_child_storage(child_info, key)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.next_child_storage_key(child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.state.for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.state.for_key_values_with_prefix(prefix, f)
	}

	fn apply_to_key_values_while<F: FnMut(Vec<u8>, Vec<u8>) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		f: F,
		allow_missing: bool,
	) -> Result<bool, Self::Error> {
		self.state
			.apply_to_key_values_while(child_info, prefix, start_at, f, allow_missing)
	}

	fn apply_to_keys_while<F: FnMut(&[u8]) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		f: F,
	) {
		self.state.apply_to_keys_while(child_info, prefix, start_at, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		self.state.for_child_keys_with_prefix(child_info, prefix, f)
	}

	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (B::Hash, Self::Transaction)
	where
		B::Hash: Ord,
	{
		self.state.storage_root(delta, state_version)
	}

	fn child_storage_root<'a>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (B::Hash, bool, Self::Transaction)
	where
		B::Hash: Ord,
	{
		self.state.child_storage_root(child_info, delta, state_version)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.state.pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.state.keys(prefix)
	}

	fn child_keys(&self, child_info: &ChildInfo, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.state.child_keys(child_info, prefix)
	}

	fn register_overlay_stats(&self, stats: &StateMachineStats) {
		self.state.register_overlay_stats(stats);
	}

	fn usage_info(&self) -> StateUsageInfo {
		self.state.usage_info()
	}
}

impl<B: BlockT> AsTrieBackend<HashFor<B>> for RefTrackingState<B> {
	type TrieBackendStorage = <DbState<B> as StateBackend<HashFor<B>>>::TrieBackendStorage;

	fn as_trie_backend(
		&self,
	) -> &sp_state_machine::TrieBackend<Self::TrieBackendStorage, HashFor<B>> {
		&self.state.as_trie_backend()
	}
}

/// Database settings.
pub struct DatabaseSettings {
	/// The maximum trie cache size in bytes.
	///
	/// If `None` is given, the cache is disabled.
	pub trie_cache_maximum_size: Option<usize>,
	/// Requested state pruning mode.
	pub state_pruning: Option<PruningMode>,
	/// Where to find the database.
	pub source: DatabaseSource,
	/// Block pruning mode.
	///
	/// NOTE: only finalized blocks are subject for removal!
	pub blocks_pruning: BlocksPruning,
}

/// Block pruning settings.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BlocksPruning {
	/// Keep full block history, of every block that was ever imported.
	KeepAll,
	/// Keep full finalized block history.
	KeepFinalized,
	/// Keep N recent finalized blocks.
	Some(u32),
}

/// Where to find the database..
#[derive(Debug, Clone)]
pub enum DatabaseSource {
	/// Check given path, and see if there is an existing database there. If it's either `RocksDb`
	/// or `ParityDb`, use it. If there is none, create a new instance of `ParityDb`.
	Auto {
		/// Path to the paritydb database.
		paritydb_path: PathBuf,
		/// Path to the rocksdb database.
		rocksdb_path: PathBuf,
		/// Cache size in MiB. Used only by `RocksDb` variant of `DatabaseSource`.
		cache_size: usize,
	},
	/// Load a RocksDB database from a given path. Recommended for most uses.
	#[cfg(feature = "rocksdb")]
	RocksDb {
		/// Path to the database.
		path: PathBuf,
		/// Cache size in MiB.
		cache_size: usize,
	},

	/// Load a ParityDb database from a given path.
	ParityDb {
		/// Path to the database.
		path: PathBuf,
	},

	/// Use a custom already-open database.
	Custom {
		/// the handle to the custom storage
		db: Arc<dyn Database<DbHash>>,

		/// if set, the `create` flag will be required to open such datasource
		require_create_flag: bool,
	},
}

impl DatabaseSource {
	/// Return path for databases that are stored on disk.
	pub fn path(&self) -> Option<&Path> {
		match self {
			// as per https://github.com/paritytech/substrate/pull/9500#discussion_r684312550
			//
			// IIUC this is needed for polkadot to create its own dbs, so until it can use parity db
			// I would think rocksdb, but later parity-db.
			DatabaseSource::Auto { paritydb_path, .. } => Some(paritydb_path),
			#[cfg(feature = "rocksdb")]
			DatabaseSource::RocksDb { path, .. } => Some(path),
			DatabaseSource::ParityDb { path } => Some(path),
			DatabaseSource::Custom { .. } => None,
		}
	}

	/// Set path for databases that are stored on disk.
	pub fn set_path(&mut self, p: &Path) -> bool {
		match self {
			DatabaseSource::Auto { ref mut paritydb_path, .. } => {
				*paritydb_path = p.into();
				true
			},
			#[cfg(feature = "rocksdb")]
			DatabaseSource::RocksDb { ref mut path, .. } => {
				*path = p.into();
				true
			},
			DatabaseSource::ParityDb { ref mut path } => {
				*path = p.into();
				true
			},
			DatabaseSource::Custom { .. } => false,
		}
	}
}

impl std::fmt::Display for DatabaseSource {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let name = match self {
			DatabaseSource::Auto { .. } => "Auto",
			#[cfg(feature = "rocksdb")]
			DatabaseSource::RocksDb { .. } => "RocksDb",
			DatabaseSource::ParityDb { .. } => "ParityDb",
			DatabaseSource::Custom { .. } => "Custom",
		};
		write!(f, "{}", name)
	}
}

pub(crate) mod columns {
	pub const META: u32 = crate::utils::COLUMN_META;
	pub const STATE: u32 = 1;
	pub const STATE_META: u32 = 2;
	/// maps hashes to lookup keys and numbers to canon hashes.
	pub const KEY_LOOKUP: u32 = 3;
	pub const HEADER: u32 = 4;
	pub const BODY: u32 = 5;
	pub const JUSTIFICATIONS: u32 = 6;
	pub const AUX: u32 = 8;
	/// Offchain workers local storage
	pub const OFFCHAIN: u32 = 9;
	/// Transactions
	pub const TRANSACTION: u32 = 11;
	pub const BODY_INDEX: u32 = 12;
}

struct PendingBlock<Block: BlockT> {
	header: Block::Header,
	justifications: Option<Justifications>,
	body: Option<Vec<Block::Extrinsic>>,
	indexed_body: Option<Vec<Vec<u8>>>,
	leaf_state: NewBlockState,
}

// wrapper that implements trait required for state_db
#[derive(Clone)]
struct StateMetaDb(Arc<dyn Database<DbHash>>);

impl sc_state_db::MetaDb for StateMetaDb {
	type Error = sp_database::error::DatabaseError;

	fn get_meta(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		Ok(self.0.get(columns::STATE_META, key))
	}
}

struct MetaUpdate<Block: BlockT> {
	pub hash: Block::Hash,
	pub number: NumberFor<Block>,
	pub is_best: bool,
	pub is_finalized: bool,
	pub with_state: bool,
}

fn cache_header<Hash: std::cmp::Eq + std::hash::Hash, Header>(
	cache: &mut LinkedHashMap<Hash, Option<Header>>,
	hash: Hash,
	header: Option<Header>,
) {
	cache.insert(hash, header);
	while cache.len() > CACHE_HEADERS {
		cache.pop_front();
	}
}

/// Block database
pub struct BlockchainDb<Block: BlockT> {
	db: Arc<dyn Database<DbHash>>,
	meta: Arc<RwLock<Meta<NumberFor<Block>, Block::Hash>>>,
	leaves: RwLock<LeafSet<Block::Hash, NumberFor<Block>>>,
	header_metadata_cache: Arc<HeaderMetadataCache<Block>>,
	header_cache: Mutex<LinkedHashMap<Block::Hash, Option<Block::Header>>>,
}

impl<Block: BlockT> BlockchainDb<Block> {
	fn new(db: Arc<dyn Database<DbHash>>) -> ClientResult<Self> {
		let meta = read_meta::<Block>(&*db, columns::HEADER)?;
		let leaves = LeafSet::read_from_db(&*db, columns::META, meta_keys::LEAF_PREFIX)?;
		Ok(BlockchainDb {
			db,
			leaves: RwLock::new(leaves),
			meta: Arc::new(RwLock::new(meta)),
			header_metadata_cache: Arc::new(HeaderMetadataCache::default()),
			header_cache: Default::default(),
		})
	}

	fn update_meta(&self, update: MetaUpdate<Block>) {
		let MetaUpdate { hash, number, is_best, is_finalized, with_state } = update;
		let mut meta = self.meta.write();
		if number.is_zero() {
			meta.genesis_hash = hash;
		}

		if is_best {
			meta.best_number = number;
			meta.best_hash = hash;
		}

		if is_finalized {
			if with_state {
				meta.finalized_state = Some((hash, number));
			}
			meta.finalized_number = number;
			meta.finalized_hash = hash;
		}
	}

	fn update_block_gap(&self, gap: Option<(NumberFor<Block>, NumberFor<Block>)>) {
		let mut meta = self.meta.write();
		meta.block_gap = gap;
	}
}

impl<Block: BlockT> sc_client_api::blockchain::HeaderBackend<Block> for BlockchainDb<Block> {
	fn header(&self, id: BlockId<Block>) -> ClientResult<Option<Block::Header>> {
		match &id {
			BlockId::Hash(h) => {
				let mut cache = self.header_cache.lock();
				if let Some(result) = cache.get_refresh(h) {
					return Ok(result.clone())
				}
				let header =
					utils::read_header(&*self.db, columns::KEY_LOOKUP, columns::HEADER, id)?;
				cache_header(&mut cache, *h, header.clone());
				Ok(header)
			},
			BlockId::Number(_) =>
				utils::read_header(&*self.db, columns::KEY_LOOKUP, columns::HEADER, id),
		}
	}

	fn info(&self) -> sc_client_api::blockchain::Info<Block> {
		let meta = self.meta.read();
		sc_client_api::blockchain::Info {
			best_hash: meta.best_hash,
			best_number: meta.best_number,
			genesis_hash: meta.genesis_hash,
			finalized_hash: meta.finalized_hash,
			finalized_number: meta.finalized_number,
			finalized_state: meta.finalized_state,
			number_leaves: self.leaves.read().count(),
			block_gap: meta.block_gap,
		}
	}

	fn status(&self, id: BlockId<Block>) -> ClientResult<sc_client_api::blockchain::BlockStatus> {
		let exists = match id {
			BlockId::Hash(_) => self.header(id)?.is_some(),
			BlockId::Number(n) => n <= self.meta.read().best_number,
		};
		match exists {
			true => Ok(sc_client_api::blockchain::BlockStatus::InChain),
			false => Ok(sc_client_api::blockchain::BlockStatus::Unknown),
		}
	}

	fn number(&self, hash: Block::Hash) -> ClientResult<Option<NumberFor<Block>>> {
		Ok(self.header_metadata(hash).ok().map(|header_metadata| header_metadata.number))
	}

	fn hash(&self, number: NumberFor<Block>) -> ClientResult<Option<Block::Hash>> {
		self.header(BlockId::Number(number))
			.map(|maybe_header| maybe_header.map(|header| header.hash()))
	}
}

impl<Block: BlockT> sc_client_api::blockchain::Backend<Block> for BlockchainDb<Block> {
	fn body(&self, hash: Block::Hash) -> ClientResult<Option<Vec<Block::Extrinsic>>> {
		if let Some(body) =
			read_db(&*self.db, columns::KEY_LOOKUP, columns::BODY, BlockId::Hash::<Block>(hash))?
		{
			// Plain body
			match Decode::decode(&mut &body[..]) {
				Ok(body) => return Ok(Some(body)),
				Err(err) =>
					return Err(sp_blockchain::Error::Backend(format!(
						"Error decoding body: {}",
						err
					))),
			}
		}

		if let Some(index) = read_db(
			&*self.db,
			columns::KEY_LOOKUP,
			columns::BODY_INDEX,
			BlockId::Hash::<Block>(hash),
		)? {
			match Vec::<DbExtrinsic<Block>>::decode(&mut &index[..]) {
				Ok(index) => {
					let mut body = Vec::new();
					for ex in index {
						match ex {
							DbExtrinsic::Indexed { hash, header } => {
								match self.db.get(columns::TRANSACTION, hash.as_ref()) {
									Some(t) => {
										let mut input =
											utils::join_input(header.as_ref(), t.as_ref());
										let ex = Block::Extrinsic::decode(&mut input).map_err(
											|err| {
												sp_blockchain::Error::Backend(format!(
													"Error decoding indexed extrinsic: {}",
													err
												))
											},
										)?;
										body.push(ex);
									},
									None =>
										return Err(sp_blockchain::Error::Backend(format!(
											"Missing indexed transaction {:?}",
											hash
										))),
								};
							},
							DbExtrinsic::Full(ex) => {
								body.push(ex);
							},
						}
					}
					return Ok(Some(body))
				},
				Err(err) =>
					return Err(sp_blockchain::Error::Backend(format!(
						"Error decoding body list: {}",
						err
					))),
			}
		}
		Ok(None)
	}

	fn justifications(&self, hash: Block::Hash) -> ClientResult<Option<Justifications>> {
		match read_db(
			&*self.db,
			columns::KEY_LOOKUP,
			columns::JUSTIFICATIONS,
			BlockId::<Block>::Hash(hash),
		)? {
			Some(justifications) => match Decode::decode(&mut &justifications[..]) {
				Ok(justifications) => Ok(Some(justifications)),
				Err(err) =>
					return Err(sp_blockchain::Error::Backend(format!(
						"Error decoding justifications: {}",
						err
					))),
			},
			None => Ok(None),
		}
	}

	fn last_finalized(&self) -> ClientResult<Block::Hash> {
		Ok(self.meta.read().finalized_hash)
	}

	fn leaves(&self) -> ClientResult<Vec<Block::Hash>> {
		Ok(self.leaves.read().hashes())
	}

	fn displaced_leaves_after_finalizing(
		&self,
		block_number: NumberFor<Block>,
	) -> ClientResult<Vec<Block::Hash>> {
		Ok(self
			.leaves
			.read()
			.displaced_by_finalize_height(block_number)
			.leaves()
			.cloned()
			.collect::<Vec<_>>())
	}

	fn children(&self, parent_hash: Block::Hash) -> ClientResult<Vec<Block::Hash>> {
		children::read_children(&*self.db, columns::META, meta_keys::CHILDREN_PREFIX, parent_hash)
	}

	fn indexed_transaction(&self, hash: Block::Hash) -> ClientResult<Option<Vec<u8>>> {
		Ok(self.db.get(columns::TRANSACTION, hash.as_ref()))
	}

	fn has_indexed_transaction(&self, hash: Block::Hash) -> ClientResult<bool> {
		Ok(self.db.contains(columns::TRANSACTION, hash.as_ref()))
	}

	fn block_indexed_body(&self, hash: Block::Hash) -> ClientResult<Option<Vec<Vec<u8>>>> {
		let body = match read_db(
			&*self.db,
			columns::KEY_LOOKUP,
			columns::BODY_INDEX,
			BlockId::<Block>::Hash(hash),
		)? {
			Some(body) => body,
			None => return Ok(None),
		};
		match Vec::<DbExtrinsic<Block>>::decode(&mut &body[..]) {
			Ok(index) => {
				let mut transactions = Vec::new();
				for ex in index.into_iter() {
					if let DbExtrinsic::Indexed { hash, .. } = ex {
						match self.db.get(columns::TRANSACTION, hash.as_ref()) {
							Some(t) => transactions.push(t),
							None =>
								return Err(sp_blockchain::Error::Backend(format!(
									"Missing indexed transaction {:?}",
									hash
								))),
						}
					}
				}
				Ok(Some(transactions))
			},
			Err(err) =>
				Err(sp_blockchain::Error::Backend(format!("Error decoding body list: {}", err))),
		}
	}
}

impl<Block: BlockT> HeaderMetadata<Block> for BlockchainDb<Block> {
	type Error = sp_blockchain::Error;

	fn header_metadata(
		&self,
		hash: Block::Hash,
	) -> Result<CachedHeaderMetadata<Block>, Self::Error> {
		self.header_metadata_cache.header_metadata(hash).map_or_else(
			|| {
				self.header(BlockId::hash(hash))?
					.map(|header| {
						let header_metadata = CachedHeaderMetadata::from(&header);
						self.header_metadata_cache
							.insert_header_metadata(header_metadata.hash, header_metadata.clone());
						header_metadata
					})
					.ok_or_else(|| {
						ClientError::UnknownBlock(format!(
							"Header was not found in the database: {:?}",
							hash
						))
					})
			},
			Ok,
		)
	}

	fn insert_header_metadata(&self, hash: Block::Hash, metadata: CachedHeaderMetadata<Block>) {
		self.header_metadata_cache.insert_header_metadata(hash, metadata)
	}

	fn remove_header_metadata(&self, hash: Block::Hash) {
		self.header_cache.lock().remove(&hash);
		self.header_metadata_cache.remove_header_metadata(hash);
	}
}

/// Database transaction
pub struct BlockImportOperation<Block: BlockT> {
	old_state: RecordStatsState<RefTrackingState<Block>, Block>,
	db_updates: PrefixedMemoryDB<HashFor<Block>>,
	storage_updates: StorageCollection,
	child_storage_updates: ChildStorageCollection,
	offchain_storage_updates: OffchainChangesCollection,
	pending_block: Option<PendingBlock<Block>>,
	aux_ops: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	finalized_blocks: Vec<(Block::Hash, Option<Justification>)>,
	set_head: Option<Block::Hash>,
	commit_state: bool,
	index_ops: Vec<IndexOperation>,
}

impl<Block: BlockT> BlockImportOperation<Block> {
	fn apply_offchain(&mut self, transaction: &mut Transaction<DbHash>) {
		let mut count = 0;
		for ((prefix, key), value_operation) in self.offchain_storage_updates.drain(..) {
			count += 1;
			let key = crate::offchain::concatenate_prefix_and_key(&prefix, &key);
			match value_operation {
				OffchainOverlayedChange::SetValue(val) =>
					transaction.set_from_vec(columns::OFFCHAIN, &key, val),
				OffchainOverlayedChange::Remove => transaction.remove(columns::OFFCHAIN, &key),
			}
		}

		if count > 0 {
			log::debug!(target: "sc_offchain", "Applied {} offchain indexing changes.", count);
		}
	}

	fn apply_aux(&mut self, transaction: &mut Transaction<DbHash>) {
		for (key, maybe_val) in self.aux_ops.drain(..) {
			match maybe_val {
				Some(val) => transaction.set_from_vec(columns::AUX, &key, val),
				None => transaction.remove(columns::AUX, &key),
			}
		}
	}

	fn apply_new_state(
		&mut self,
		storage: Storage,
		state_version: StateVersion,
	) -> ClientResult<Block::Hash> {
		if storage.top.keys().any(|k| well_known_keys::is_child_storage_key(k)) {
			return Err(sp_blockchain::Error::InvalidState)
		}

		let child_delta = storage.children_default.values().map(|child_content| {
			(
				&child_content.child_info,
				child_content.data.iter().map(|(k, v)| (&k[..], Some(&v[..]))),
			)
		});

		let (root, transaction) = self.old_state.full_storage_root(
			storage.top.iter().map(|(k, v)| (&k[..], Some(&v[..]))),
			child_delta,
			state_version,
		);

		self.db_updates = transaction;
		Ok(root)
	}
}

impl<Block: BlockT> sc_client_api::backend::BlockImportOperation<Block>
	for BlockImportOperation<Block>
{
	type State = RecordStatsState<RefTrackingState<Block>, Block>;

	fn state(&self) -> ClientResult<Option<&Self::State>> {
		Ok(Some(&self.old_state))
	}

	fn set_block_data(
		&mut self,
		header: Block::Header,
		body: Option<Vec<Block::Extrinsic>>,
		indexed_body: Option<Vec<Vec<u8>>>,
		justifications: Option<Justifications>,
		leaf_state: NewBlockState,
	) -> ClientResult<()> {
		assert!(self.pending_block.is_none(), "Only one block per operation is allowed");
		self.pending_block =
			Some(PendingBlock { header, body, indexed_body, justifications, leaf_state });
		Ok(())
	}

	fn update_cache(&mut self, _cache: HashMap<well_known_cache_keys::Id, Vec<u8>>) {
		// Currently cache isn't implemented on full nodes.
	}

	fn update_db_storage(&mut self, update: PrefixedMemoryDB<HashFor<Block>>) -> ClientResult<()> {
		self.db_updates = update;
		Ok(())
	}

	fn reset_storage(
		&mut self,
		storage: Storage,
		state_version: StateVersion,
	) -> ClientResult<Block::Hash> {
		let root = self.apply_new_state(storage, state_version)?;
		self.commit_state = true;
		Ok(root)
	}

	fn set_genesis_state(
		&mut self,
		storage: Storage,
		commit: bool,
		state_version: StateVersion,
	) -> ClientResult<Block::Hash> {
		let root = self.apply_new_state(storage, state_version)?;
		self.commit_state = commit;
		Ok(root)
	}

	fn insert_aux<I>(&mut self, ops: I) -> ClientResult<()>
	where
		I: IntoIterator<Item = (Vec<u8>, Option<Vec<u8>>)>,
	{
		self.aux_ops.append(&mut ops.into_iter().collect());
		Ok(())
	}

	fn update_storage(
		&mut self,
		update: StorageCollection,
		child_update: ChildStorageCollection,
	) -> ClientResult<()> {
		self.storage_updates = update;
		self.child_storage_updates = child_update;
		Ok(())
	}

	fn update_offchain_storage(
		&mut self,
		offchain_update: OffchainChangesCollection,
	) -> ClientResult<()> {
		self.offchain_storage_updates = offchain_update;
		Ok(())
	}

	fn mark_finalized(
		&mut self,
		block: Block::Hash,
		justification: Option<Justification>,
	) -> ClientResult<()> {
		self.finalized_blocks.push((block, justification));
		Ok(())
	}

	fn mark_head(&mut self, hash: Block::Hash) -> ClientResult<()> {
		assert!(self.set_head.is_none(), "Only one set head per operation is allowed");
		self.set_head = Some(hash);
		Ok(())
	}

	fn update_transaction_index(&mut self, index_ops: Vec<IndexOperation>) -> ClientResult<()> {
		self.index_ops = index_ops;
		Ok(())
	}
}

struct StorageDb<Block: BlockT> {
	pub db: Arc<dyn Database<DbHash>>,
	pub state_db: StateDb<Block::Hash, Vec<u8>, StateMetaDb>,
	prefix_keys: bool,
}

impl<Block: BlockT> sp_state_machine::Storage<HashFor<Block>> for StorageDb<Block> {
	fn get(&self, key: &Block::Hash, prefix: Prefix) -> Result<Option<DBValue>, String> {
		if self.prefix_keys {
			let key = prefixed_key::<HashFor<Block>>(key, prefix);
			self.state_db.get(&key, self)
		} else {
			self.state_db.get(key.as_ref(), self)
		}
		.map_err(|e| format!("Database backend error: {:?}", e))
	}
}

impl<Block: BlockT> sc_state_db::NodeDb for StorageDb<Block> {
	type Error = io::Error;
	type Key = [u8];

	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		Ok(self.db.get(columns::STATE, key))
	}
}

struct DbGenesisStorage<Block: BlockT> {
	root: Block::Hash,
	storage: PrefixedMemoryDB<HashFor<Block>>,
}

impl<Block: BlockT> DbGenesisStorage<Block> {
	pub fn new(root: Block::Hash, storage: PrefixedMemoryDB<HashFor<Block>>) -> Self {
		DbGenesisStorage { root, storage }
	}
}

impl<Block: BlockT> sp_state_machine::Storage<HashFor<Block>> for DbGenesisStorage<Block> {
	fn get(&self, key: &Block::Hash, prefix: Prefix) -> Result<Option<DBValue>, String> {
		use hash_db::HashDB;
		Ok(self.storage.get(key, prefix))
	}
}

struct EmptyStorage<Block: BlockT>(pub Block::Hash);

impl<Block: BlockT> EmptyStorage<Block> {
	pub fn new() -> Self {
		let mut root = Block::Hash::default();
		let mut mdb = MemoryDB::<HashFor<Block>>::default();
		// both triedbmut are the same on empty storage.
		sp_trie::trie_types::TrieDBMutBuilderV1::<HashFor<Block>>::new(&mut mdb, &mut root).build();
		EmptyStorage(root)
	}
}

impl<Block: BlockT> sp_state_machine::Storage<HashFor<Block>> for EmptyStorage<Block> {
	fn get(&self, _key: &Block::Hash, _prefix: Prefix) -> Result<Option<DBValue>, String> {
		Ok(None)
	}
}

/// Frozen `value` at time `at`.
///
/// Used as inner structure under lock in `FrozenForDuration`.
struct Frozen<T: Clone> {
	at: std::time::Instant,
	value: Option<T>,
}

/// Some value frozen for period of time.
///
/// If time `duration` not passed since the value was instantiated,
/// current frozen value is returned. Otherwise, you have to provide
/// a new value which will be again frozen for `duration`.
pub(crate) struct FrozenForDuration<T: Clone> {
	duration: std::time::Duration,
	value: parking_lot::Mutex<Frozen<T>>,
}

impl<T: Clone> FrozenForDuration<T> {
	fn new(duration: std::time::Duration) -> Self {
		Self { duration, value: Frozen { at: std::time::Instant::now(), value: None }.into() }
	}

	fn take_or_else<F>(&self, f: F) -> T
	where
		F: FnOnce() -> T,
	{
		let mut lock = self.value.lock();
		let now = std::time::Instant::now();
		if now.saturating_duration_since(lock.at) > self.duration || lock.value.is_none() {
			let new_value = f();
			lock.at = now;
			lock.value = Some(new_value.clone());
			new_value
		} else {
			lock.value.as_ref().expect("Checked with in branch above; qed").clone()
		}
	}
}

/// Disk backend.
///
/// Disk backend keeps data in a key-value store. In archive mode, trie nodes are kept from all
/// blocks. Otherwise, trie nodes are kept only from some recent blocks.
pub struct Backend<Block: BlockT> {
	storage: Arc<StorageDb<Block>>,
	offchain_storage: offchain::LocalStorage,
	blockchain: BlockchainDb<Block>,
	canonicalization_delay: u64,
	import_lock: Arc<RwLock<()>>,
	is_archive: bool,
	blocks_pruning: BlocksPruning,
	io_stats: FrozenForDuration<(kvdb::IoStats, StateUsageInfo)>,
	state_usage: Arc<StateUsageStats>,
	genesis_state: RwLock<Option<Arc<DbGenesisStorage<Block>>>>,
	shared_trie_cache: Option<sp_trie::cache::SharedTrieCache<HashFor<Block>>>,
}

impl<Block: BlockT> Backend<Block> {
	/// Create a new instance of database backend.
	///
	/// The pruning window is how old a block must be before the state is pruned.
	pub fn new(db_config: DatabaseSettings, canonicalization_delay: u64) -> ClientResult<Self> {
		use utils::OpenDbError;

		let db_source = &db_config.source;

		let (needs_init, db) =
			match crate::utils::open_database::<Block>(db_source, DatabaseType::Full, false) {
				Ok(db) => (false, db),
				Err(OpenDbError::DoesNotExist) => {
					let db =
						crate::utils::open_database::<Block>(db_source, DatabaseType::Full, true)?;
					(true, db)
				},
				Err(as_is) => return Err(as_is.into()),
			};

		Self::from_database(db as Arc<_>, canonicalization_delay, &db_config, needs_init)
	}

	/// Create new memory-backed client backend for tests.
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn new_test(blocks_pruning: u32, canonicalization_delay: u64) -> Self {
		Self::new_test_with_tx_storage(BlocksPruning::Some(blocks_pruning), canonicalization_delay)
	}

	/// Create new memory-backed client backend for tests.
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn new_test_with_tx_storage(
		blocks_pruning: BlocksPruning,
		canonicalization_delay: u64,
	) -> Self {
		let db = kvdb_memorydb::create(crate::utils::NUM_COLUMNS);
		let db = sp_database::as_database(db);
		let state_pruning = match blocks_pruning {
			BlocksPruning::KeepAll => PruningMode::ArchiveAll,
			BlocksPruning::KeepFinalized => PruningMode::ArchiveCanonical,
			BlocksPruning::Some(n) => PruningMode::blocks_pruning(n),
		};
		let db_setting = DatabaseSettings {
			trie_cache_maximum_size: Some(16 * 1024 * 1024),
			state_pruning: Some(state_pruning),
			source: DatabaseSource::Custom { db, require_create_flag: true },
			blocks_pruning,
		};

		Self::new(db_setting, canonicalization_delay).expect("failed to create test-db")
	}

	/// Expose the Database that is used by this backend.
	/// The second argument is the Column that stores the State.
	///
	/// Should only be needed for benchmarking.
	#[cfg(any(feature = "runtime-benchmarks"))]
	pub fn expose_db(&self) -> (Arc<dyn sp_database::Database<DbHash>>, sp_database::ColumnId) {
		(self.storage.db.clone(), columns::STATE)
	}

	/// Expose the Storage that is used by this backend.
	///
	/// Should only be needed for benchmarking.
	#[cfg(any(feature = "runtime-benchmarks"))]
	pub fn expose_storage(&self) -> Arc<dyn sp_state_machine::Storage<HashFor<Block>>> {
		self.storage.clone()
	}

	fn from_database(
		db: Arc<dyn Database<DbHash>>,
		canonicalization_delay: u64,
		config: &DatabaseSettings,
		should_init: bool,
	) -> ClientResult<Self> {
		let mut db_init_transaction = Transaction::new();

		let requested_state_pruning = config.state_pruning.clone();
		let state_meta_db = StateMetaDb(db.clone());
		let map_e = sp_blockchain::Error::from_state_db;

		let (state_db_init_commit_set, state_db) = StateDb::open(
			state_meta_db,
			requested_state_pruning,
			!db.supports_ref_counting(),
			should_init,
		)
		.map_err(map_e)?;

		apply_state_commit(&mut db_init_transaction, state_db_init_commit_set);

		let state_pruning_used = state_db.pruning_mode();
		let is_archive_pruning = state_pruning_used.is_archive();
		let blockchain = BlockchainDb::new(db.clone())?;

		let storage_db =
			StorageDb { db: db.clone(), state_db, prefix_keys: !db.supports_ref_counting() };

		let offchain_storage = offchain::LocalStorage::new(db.clone());

		let backend = Backend {
			storage: Arc::new(storage_db),
			offchain_storage,
			blockchain,
			canonicalization_delay,
			import_lock: Default::default(),
			is_archive: is_archive_pruning,
			io_stats: FrozenForDuration::new(std::time::Duration::from_secs(1)),
			state_usage: Arc::new(StateUsageStats::new()),
			blocks_pruning: config.blocks_pruning,
			genesis_state: RwLock::new(None),
			shared_trie_cache: config.trie_cache_maximum_size.map(|maximum_size| {
				SharedTrieCache::new(sp_trie::cache::CacheSize::Maximum(maximum_size))
			}),
		};

		// Older DB versions have no last state key. Check if the state is available and set it.
		let info = backend.blockchain.info();
		if info.finalized_state.is_none() &&
			info.finalized_hash != Default::default() &&
			sc_client_api::Backend::have_state_at(
				&backend,
				info.finalized_hash,
				info.finalized_number,
			) {
			backend.blockchain.update_meta(MetaUpdate {
				hash: info.finalized_hash,
				number: info.finalized_number,
				is_best: info.finalized_hash == info.best_hash,
				is_finalized: true,
				with_state: true,
			});
		}

		db.commit(db_init_transaction)?;

		Ok(backend)
	}

	/// Handle setting head within a transaction. `route_to` should be the last
	/// block that existed in the database. `best_to` should be the best block
	/// to be set.
	///
	/// In the case where the new best block is a block to be imported, `route_to`
	/// should be the parent of `best_to`. In the case where we set an existing block
	/// to be best, `route_to` should equal to `best_to`.
	fn set_head_with_transaction(
		&self,
		transaction: &mut Transaction<DbHash>,
		route_to: Block::Hash,
		best_to: (NumberFor<Block>, Block::Hash),
	) -> ClientResult<(Vec<Block::Hash>, Vec<Block::Hash>)> {
		let mut enacted = Vec::default();
		let mut retracted = Vec::default();

		let (best_number, best_hash) = best_to;

		let meta = self.blockchain.meta.read();

		if meta.best_number > best_number &&
			(meta.best_number - best_number).saturated_into::<u64>() >
				self.canonicalization_delay
		{
			return Err(sp_blockchain::Error::SetHeadTooOld)
		}

		let parent_exists =
			self.blockchain.status(BlockId::Hash(route_to))? == sp_blockchain::BlockStatus::InChain;

		// Cannot find tree route with empty DB or when imported a detached block.
		if meta.best_hash != Default::default() && parent_exists {
			let tree_route = sp_blockchain::tree_route(&self.blockchain, meta.best_hash, route_to)?;

			// uncanonicalize: check safety violations and ensure the numbers no longer
			// point to these block hashes in the key mapping.
			for r in tree_route.retracted() {
				if r.hash == meta.finalized_hash {
					warn!(
						"Potential safety failure: reverting finalized block {:?}",
						(&r.number, &r.hash)
					);

					return Err(sp_blockchain::Error::NotInFinalizedChain)
				}

				retracted.push(r.hash);
				utils::remove_number_to_key_mapping(transaction, columns::KEY_LOOKUP, r.number)?;
			}

			// canonicalize: set the number lookup to map to this block's hash.
			for e in tree_route.enacted() {
				enacted.push(e.hash);
				utils::insert_number_to_key_mapping(
					transaction,
					columns::KEY_LOOKUP,
					e.number,
					e.hash,
				)?;
			}
		}

		let lookup_key = utils::number_and_hash_to_lookup_key(best_number, &best_hash)?;
		transaction.set_from_vec(columns::META, meta_keys::BEST_BLOCK, lookup_key);
		utils::insert_number_to_key_mapping(
			transaction,
			columns::KEY_LOOKUP,
			best_number,
			best_hash,
		)?;

		Ok((enacted, retracted))
	}

	fn ensure_sequential_finalization(
		&self,
		header: &Block::Header,
		last_finalized: Option<Block::Hash>,
	) -> ClientResult<()> {
		let last_finalized =
			last_finalized.unwrap_or_else(|| self.blockchain.meta.read().finalized_hash);
		if last_finalized != self.blockchain.meta.read().genesis_hash &&
			*header.parent_hash() != last_finalized
		{
			return Err(sp_blockchain::Error::NonSequentialFinalization(format!(
				"Last finalized {:?} not parent of {:?}",
				last_finalized,
				header.hash()
			)))
		}
		Ok(())
	}

	fn finalize_block_with_transaction(
		&self,
		transaction: &mut Transaction<DbHash>,
		hash: Block::Hash,
		header: &Block::Header,
		last_finalized: Option<Block::Hash>,
		justification: Option<Justification>,
		finalization_displaced: &mut Option<FinalizationOutcome<Block::Hash, NumberFor<Block>>>,
	) -> ClientResult<MetaUpdate<Block>> {
		// TODO: ensure best chain contains this block.
		let number = *header.number();
		self.ensure_sequential_finalization(header, last_finalized)?;
		let with_state = sc_client_api::Backend::have_state_at(self, hash, number);

		self.note_finalized(transaction, header, hash, finalization_displaced, with_state)?;

		if let Some(justification) = justification {
			transaction.set_from_vec(
				columns::JUSTIFICATIONS,
				&utils::number_and_hash_to_lookup_key(number, hash)?,
				Justifications::from(justification).encode(),
			);
		}
		Ok(MetaUpdate { hash, number, is_best: false, is_finalized: true, with_state })
	}

	// performs forced canonicalization with a delay after importing a non-finalized block.
	fn force_delayed_canonicalize(
		&self,
		transaction: &mut Transaction<DbHash>,
		hash: Block::Hash,
		number: NumberFor<Block>,
	) -> ClientResult<()> {
		let number_u64 = number.saturated_into::<u64>();
		if number_u64 > self.canonicalization_delay {
			let new_canonical = number_u64 - self.canonicalization_delay;

			if new_canonical <= self.storage.state_db.best_canonical().unwrap_or(0) {
				return Ok(())
			}
			let hash = if new_canonical == number_u64 {
				hash
			} else {
				sc_client_api::blockchain::HeaderBackend::hash(
					&self.blockchain,
					new_canonical.saturated_into(),
				)?
				.ok_or_else(|| {
					sp_blockchain::Error::Backend(format!(
						"Can't canonicalize missing block number #{} when importing {:?} (#{})",
						new_canonical, hash, number,
					))
				})?
			};
			if !sc_client_api::Backend::have_state_at(self, hash, new_canonical.saturated_into()) {
				return Ok(())
			}

			trace!(target: "db", "Canonicalize block #{} ({:?})", new_canonical, hash);
			let commit = self.storage.state_db.canonicalize_block(&hash).map_err(
				sp_blockchain::Error::from_state_db::<
					sc_state_db::Error<sp_database::error::DatabaseError>,
				>,
			)?;
			apply_state_commit(transaction, commit);
		}
		Ok(())
	}

	fn try_commit_operation(&self, mut operation: BlockImportOperation<Block>) -> ClientResult<()> {
		let mut transaction = Transaction::new();
		let mut finalization_displaced_leaves = None;

		operation.apply_aux(&mut transaction);
		operation.apply_offchain(&mut transaction);

		let mut meta_updates = Vec::with_capacity(operation.finalized_blocks.len());
		let (best_num, mut last_finalized_hash, mut last_finalized_num, mut block_gap) = {
			let meta = self.blockchain.meta.read();
			(meta.best_number, meta.finalized_hash, meta.finalized_number, meta.block_gap)
		};

		for (block_hash, justification) in operation.finalized_blocks {
			let block_header = self.blockchain.expect_header(BlockId::Hash(block_hash))?;
			meta_updates.push(self.finalize_block_with_transaction(
				&mut transaction,
				block_hash,
				&block_header,
				Some(last_finalized_hash),
				justification,
				&mut finalization_displaced_leaves,
			)?);
			last_finalized_hash = block_hash;
			last_finalized_num = *block_header.number();
		}

		let imported = if let Some(pending_block) = operation.pending_block {
			let hash = pending_block.header.hash();

			let parent_hash = *pending_block.header.parent_hash();
			let number = *pending_block.header.number();
			let highest_leaf = self
				.blockchain
				.leaves
				.read()
				.highest_leaf()
				.map(|(n, _)| n)
				.unwrap_or(Zero::zero());
			let existing_header =
				number <= highest_leaf && self.blockchain.header(BlockId::hash(hash))?.is_some();

			// blocks are keyed by number + hash.
			let lookup_key = utils::number_and_hash_to_lookup_key(number, hash)?;

			if pending_block.leaf_state.is_best() {
				self.set_head_with_transaction(&mut transaction, parent_hash, (number, hash))?;
			};

			utils::insert_hash_to_key_mapping(&mut transaction, columns::KEY_LOOKUP, number, hash)?;

			transaction.set_from_vec(columns::HEADER, &lookup_key, pending_block.header.encode());
			if let Some(body) = pending_block.body {
				// If we have any index operations we save block in the new format with indexed
				// extrinsic headers Otherwise we save the body as a single blob.
				if operation.index_ops.is_empty() {
					transaction.set_from_vec(columns::BODY, &lookup_key, body.encode());
				} else {
					let body =
						apply_index_ops::<Block>(&mut transaction, body, operation.index_ops);
					transaction.set_from_vec(columns::BODY_INDEX, &lookup_key, body);
				}
			}
			if let Some(body) = pending_block.indexed_body {
				apply_indexed_body::<Block>(&mut transaction, body);
			}
			if let Some(justifications) = pending_block.justifications {
				transaction.set_from_vec(
					columns::JUSTIFICATIONS,
					&lookup_key,
					justifications.encode(),
				);
			}

			if number.is_zero() {
				transaction.set(columns::META, meta_keys::GENESIS_HASH, hash.as_ref());

				if operation.commit_state {
					transaction.set_from_vec(columns::META, meta_keys::FINALIZED_STATE, lookup_key);
				} else {
					// When we don't want to commit the genesis state, we still preserve it in
					// memory to bootstrap consensus. It is queried for an initial list of
					// authorities, etc.
					*self.genesis_state.write() = Some(Arc::new(DbGenesisStorage::new(
						*pending_block.header.state_root(),
						operation.db_updates.clone(),
					)));
				}
			}

			let finalized = if operation.commit_state {
				let mut changeset: sc_state_db::ChangeSet<Vec<u8>> =
					sc_state_db::ChangeSet::default();
				let mut ops: u64 = 0;
				let mut bytes: u64 = 0;
				let mut removal: u64 = 0;
				let mut bytes_removal: u64 = 0;
				for (mut key, (val, rc)) in operation.db_updates.drain() {
					self.storage.db.sanitize_key(&mut key);
					if rc > 0 {
						ops += 1;
						bytes += key.len() as u64 + val.len() as u64;
						if rc == 1 {
							changeset.inserted.push((key, val.to_vec()));
						} else {
							changeset.inserted.push((key.clone(), val.to_vec()));
							for _ in 0..rc - 1 {
								changeset.inserted.push((key.clone(), Default::default()));
							}
						}
					} else if rc < 0 {
						removal += 1;
						bytes_removal += key.len() as u64;
						if rc == -1 {
							changeset.deleted.push(key);
						} else {
							for _ in 0..-rc {
								changeset.deleted.push(key.clone());
							}
						}
					}
				}
				self.state_usage.tally_writes_nodes(ops, bytes);
				self.state_usage.tally_removed_nodes(removal, bytes_removal);

				let mut ops: u64 = 0;
				let mut bytes: u64 = 0;
				for (key, value) in operation
					.storage_updates
					.iter()
					.chain(operation.child_storage_updates.iter().flat_map(|(_, s)| s.iter()))
				{
					ops += 1;
					bytes += key.len() as u64;
					if let Some(v) = value.as_ref() {
						bytes += v.len() as u64;
					}
				}
				self.state_usage.tally_writes(ops, bytes);
				let number_u64 = number.saturated_into::<u64>();
				let commit = self
					.storage
					.state_db
					.insert_block(&hash, number_u64, pending_block.header.parent_hash(), changeset)
					.map_err(|e: sc_state_db::Error<sp_database::error::DatabaseError>| {
						sp_blockchain::Error::from_state_db(e)
					})?;
				apply_state_commit(&mut transaction, commit);
				if number <= last_finalized_num {
					// Canonicalize in the db when re-importing existing blocks with state.
					let commit = self.storage.state_db.canonicalize_block(&hash).map_err(
						sp_blockchain::Error::from_state_db::<
							sc_state_db::Error<sp_database::error::DatabaseError>,
						>,
					)?;
					apply_state_commit(&mut transaction, commit);
					meta_updates.push(MetaUpdate {
						hash,
						number,
						is_best: false,
						is_finalized: true,
						with_state: true,
					});
				}

				// Check if need to finalize. Genesis is always finalized instantly.
				let finalized = number_u64 == 0 || pending_block.leaf_state.is_final();
				finalized
			} else {
				(number.is_zero() && last_finalized_num.is_zero()) ||
					pending_block.leaf_state.is_final()
			};

			let header = &pending_block.header;
			let is_best = pending_block.leaf_state.is_best();
			debug!(
				target: "db",
				"DB Commit {:?} ({}), best={}, state={}, existing={}, finalized={}",
				hash,
				number,
				is_best,
				operation.commit_state,
				existing_header,
				finalized,
			);

			self.state_usage.merge_sm(operation.old_state.usage_info());

			// release state reference so that it can be finalized
			// VERY IMPORTANT
			drop(operation.old_state);

			if finalized {
				// TODO: ensure best chain contains this block.
				self.ensure_sequential_finalization(header, Some(last_finalized_hash))?;
				self.note_finalized(
					&mut transaction,
					header,
					hash,
					&mut finalization_displaced_leaves,
					operation.commit_state,
				)?;
			} else {
				// canonicalize blocks which are old enough, regardless of finality.
				self.force_delayed_canonicalize(&mut transaction, hash, *header.number())?
			}

			if !existing_header {
				// Add a new leaf if the block has the potential to be finalized.
				if number > last_finalized_num || last_finalized_num.is_zero() {
					let mut leaves = self.blockchain.leaves.write();
					leaves.import(hash, number, parent_hash);
					leaves.prepare_transaction(
						&mut transaction,
						columns::META,
						meta_keys::LEAF_PREFIX,
					);
				}

				let mut children = children::read_children(
					&*self.storage.db,
					columns::META,
					meta_keys::CHILDREN_PREFIX,
					parent_hash,
				)?;
				if !children.contains(&hash) {
					children.push(hash);
					children::write_children(
						&mut transaction,
						columns::META,
						meta_keys::CHILDREN_PREFIX,
						parent_hash,
						children,
					);
				}

				if let Some((mut start, end)) = block_gap {
					if number == start {
						start += One::one();
						utils::insert_number_to_key_mapping(
							&mut transaction,
							columns::KEY_LOOKUP,
							number,
							hash,
						)?;
					}
					if start > end {
						transaction.remove(columns::META, meta_keys::BLOCK_GAP);
						block_gap = None;
						debug!(target: "db", "Removed block gap.");
					} else {
						block_gap = Some((start, end));
						debug!(target: "db", "Update block gap. {:?}", block_gap);
						transaction.set(
							columns::META,
							meta_keys::BLOCK_GAP,
							&(start, end).encode(),
						);
					}
				} else if number > best_num + One::one() &&
					number > One::one() && self
					.blockchain
					.header(BlockId::hash(parent_hash))?
					.is_none()
				{
					let gap = (best_num + One::one(), number - One::one());
					transaction.set(columns::META, meta_keys::BLOCK_GAP, &gap.encode());
					block_gap = Some(gap);
					debug!(target: "db", "Detected block gap {:?}", block_gap);
				}
			}

			meta_updates.push(MetaUpdate {
				hash,
				number,
				is_best: pending_block.leaf_state.is_best(),
				is_finalized: finalized,
				with_state: operation.commit_state,
			});
			Some((pending_block.header, hash))
		} else {
			None
		};

		if let Some(set_head) = operation.set_head {
			if let Some(header) = sc_client_api::blockchain::HeaderBackend::header(
				&self.blockchain,
				BlockId::Hash(set_head),
			)? {
				let number = header.number();
				let hash = header.hash();

				self.set_head_with_transaction(&mut transaction, hash, (*number, hash))?;

				meta_updates.push(MetaUpdate {
					hash,
					number: *number,
					is_best: true,
					is_finalized: false,
					with_state: false,
				});
			} else {
				return Err(sp_blockchain::Error::UnknownBlock(format!(
					"Cannot set head {:?}",
					set_head
				)))
			}
		}

		self.storage.db.commit(transaction)?;

		// Apply all in-memory state changes.
		// Code beyond this point can't fail.

		if let Some((header, hash)) = imported {
			trace!(target: "db", "DB Commit done {:?}", hash);
			let header_metadata = CachedHeaderMetadata::from(&header);
			self.blockchain.insert_header_metadata(header_metadata.hash, header_metadata);
			cache_header(&mut self.blockchain.header_cache.lock(), hash, Some(header));
		}

		for m in meta_updates {
			self.blockchain.update_meta(m);
		}
		self.blockchain.update_block_gap(block_gap);

		Ok(())
	}

	// write stuff to a transaction after a new block is finalized.
	// this canonicalizes finalized blocks. Fails if called with a block which
	// was not a child of the last finalized block.
	fn note_finalized(
		&self,
		transaction: &mut Transaction<DbHash>,
		f_header: &Block::Header,
		f_hash: Block::Hash,
		displaced: &mut Option<FinalizationOutcome<Block::Hash, NumberFor<Block>>>,
		with_state: bool,
	) -> ClientResult<()> {
		let f_num = *f_header.number();

		let lookup_key = utils::number_and_hash_to_lookup_key(f_num, f_hash)?;
		if with_state {
			transaction.set_from_vec(columns::META, meta_keys::FINALIZED_STATE, lookup_key.clone());
		}
		transaction.set_from_vec(columns::META, meta_keys::FINALIZED_BLOCK, lookup_key);

		if sc_client_api::Backend::have_state_at(self, f_hash, f_num) &&
			self.storage
				.state_db
				.best_canonical()
				.map(|c| f_num.saturated_into::<u64>() > c)
				.unwrap_or(true)
		{
			let commit = self.storage.state_db.canonicalize_block(&f_hash).map_err(
				sp_blockchain::Error::from_state_db::<
					sc_state_db::Error<sp_database::error::DatabaseError>,
				>,
			)?;
			apply_state_commit(transaction, commit);
		}

		let new_displaced = self.blockchain.leaves.write().finalize_height(f_num);
		self.prune_blocks(transaction, f_num, &new_displaced)?;
		match displaced {
			x @ &mut None => *x = Some(new_displaced),
			&mut Some(ref mut displaced) => displaced.merge(new_displaced),
		}

		Ok(())
	}

	fn prune_blocks(
		&self,
		transaction: &mut Transaction<DbHash>,
		finalized: NumberFor<Block>,
		displaced: &FinalizationOutcome<Block::Hash, NumberFor<Block>>,
	) -> ClientResult<()> {
		match self.blocks_pruning {
			BlocksPruning::KeepAll => {},
			BlocksPruning::Some(blocks_pruning) => {
				// Always keep the last finalized block
				let keep = std::cmp::max(blocks_pruning, 1);
				if finalized >= keep.into() {
					let number = finalized.saturating_sub(keep.into());
					self.prune_block(transaction, BlockId::<Block>::number(number))?;
				}
				self.prune_displaced_branches(transaction, finalized, displaced)?;
			},
			BlocksPruning::KeepFinalized => {
				self.prune_displaced_branches(transaction, finalized, displaced)?;
			},
		}
		Ok(())
	}

	fn prune_displaced_branches(
		&self,
		transaction: &mut Transaction<DbHash>,
		finalized: NumberFor<Block>,
		displaced: &FinalizationOutcome<Block::Hash, NumberFor<Block>>,
	) -> ClientResult<()> {
		// Discard all blocks from displaced branches
		for h in displaced.leaves() {
			let mut number = finalized;
			let mut hash = *h;
			// Follow displaced chains back until we reach a finalized block.
			// Since leaves are discarded due to finality, they can't have parents
			// that are canonical, but not yet finalized. So we stop deleting as soon as
			// we reach canonical chain.
			while self.blockchain.hash(number)? != Some(hash) {
				let id = BlockId::<Block>::hash(hash);
				match self.blockchain.header(id)? {
					Some(header) => {
						self.prune_block(transaction, id)?;
						number = header.number().saturating_sub(One::one());
						hash = *header.parent_hash();
					},
					None => break,
				}
			}
		}
		Ok(())
	}

	fn prune_block(
		&self,
		transaction: &mut Transaction<DbHash>,
		id: BlockId<Block>,
	) -> ClientResult<()> {
		debug!(target: "db", "Removing block #{}", id);
		utils::remove_from_db(
			transaction,
			&*self.storage.db,
			columns::KEY_LOOKUP,
			columns::BODY,
			id,
		)?;
		utils::remove_from_db(
			transaction,
			&*self.storage.db,
			columns::KEY_LOOKUP,
			columns::JUSTIFICATIONS,
			id,
		)?;
		if let Some(index) =
			read_db(&*self.storage.db, columns::KEY_LOOKUP, columns::BODY_INDEX, id)?
		{
			utils::remove_from_db(
				transaction,
				&*self.storage.db,
				columns::KEY_LOOKUP,
				columns::BODY_INDEX,
				id,
			)?;
			match Vec::<DbExtrinsic<Block>>::decode(&mut &index[..]) {
				Ok(index) =>
					for ex in index {
						if let DbExtrinsic::Indexed { hash, .. } = ex {
							transaction.release(columns::TRANSACTION, hash);
						}
					},
				Err(err) =>
					return Err(sp_blockchain::Error::Backend(format!(
						"Error decoding body list: {}",
						err
					))),
			}
		}
		Ok(())
	}

	fn empty_state(&self) -> ClientResult<RecordStatsState<RefTrackingState<Block>, Block>> {
		let root = EmptyStorage::<Block>::new().0; // Empty trie
		let db_state = DbStateBuilder::<Block>::new(self.storage.clone(), root)
			.with_optional_cache(self.shared_trie_cache.as_ref().map(|c| c.local_cache()))
			.build();
		let state = RefTrackingState::new(db_state, self.storage.clone(), None);
		Ok(RecordStatsState::new(state, None, self.state_usage.clone()))
	}
}

fn apply_state_commit(
	transaction: &mut Transaction<DbHash>,
	commit: sc_state_db::CommitSet<Vec<u8>>,
) {
	for (key, val) in commit.data.inserted.into_iter() {
		transaction.set_from_vec(columns::STATE, &key[..], val);
	}
	for key in commit.data.deleted.into_iter() {
		transaction.remove(columns::STATE, &key[..]);
	}
	for (key, val) in commit.meta.inserted.into_iter() {
		transaction.set_from_vec(columns::STATE_META, &key[..], val);
	}
	for key in commit.meta.deleted.into_iter() {
		transaction.remove(columns::STATE_META, &key[..]);
	}
}

fn apply_index_ops<Block: BlockT>(
	transaction: &mut Transaction<DbHash>,
	body: Vec<Block::Extrinsic>,
	ops: Vec<IndexOperation>,
) -> Vec<u8> {
	let mut extrinsic_index: Vec<DbExtrinsic<Block>> = Vec::with_capacity(body.len());
	let mut index_map = HashMap::new();
	let mut renewed_map = HashMap::new();
	for op in ops {
		match op {
			IndexOperation::Insert { extrinsic, hash, size } => {
				index_map.insert(extrinsic, (hash, size));
			},
			IndexOperation::Renew { extrinsic, hash } => {
				renewed_map.insert(extrinsic, DbHash::from_slice(hash.as_ref()));
			},
		}
	}
	for (index, extrinsic) in body.into_iter().enumerate() {
		let db_extrinsic = if let Some(hash) = renewed_map.get(&(index as u32)) {
			// Bump ref counter
			let extrinsic = extrinsic.encode();
			transaction.reference(columns::TRANSACTION, DbHash::from_slice(hash.as_ref()));
			DbExtrinsic::Indexed { hash: *hash, header: extrinsic }
		} else {
			match index_map.get(&(index as u32)) {
				Some((hash, size)) => {
					let encoded = extrinsic.encode();
					if *size as usize <= encoded.len() {
						let offset = encoded.len() - *size as usize;
						transaction.store(
							columns::TRANSACTION,
							DbHash::from_slice(hash.as_ref()),
							encoded[offset..].to_vec(),
						);
						DbExtrinsic::Indexed {
							hash: DbHash::from_slice(hash.as_ref()),
							header: encoded[..offset].to_vec(),
						}
					} else {
						// Invalid indexed slice. Just store full data and don't index anything.
						DbExtrinsic::Full(extrinsic)
					}
				},
				_ => DbExtrinsic::Full(extrinsic),
			}
		};
		extrinsic_index.push(db_extrinsic);
	}
	debug!(
		target: "db",
		"DB transaction index: {} inserted, {} renewed, {} full",
		index_map.len(),
		renewed_map.len(),
		extrinsic_index.len() - index_map.len() - renewed_map.len(),
	);
	extrinsic_index.encode()
}

fn apply_indexed_body<Block: BlockT>(transaction: &mut Transaction<DbHash>, body: Vec<Vec<u8>>) {
	for extrinsic in body {
		let hash = sp_runtime::traits::BlakeTwo256::hash(&extrinsic);
		transaction.store(columns::TRANSACTION, DbHash::from_slice(hash.as_ref()), extrinsic);
	}
}

impl<Block> sc_client_api::backend::AuxStore for Backend<Block>
where
	Block: BlockT,
{
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item = &'a (&'c [u8], &'c [u8])>,
		D: IntoIterator<Item = &'a &'b [u8]>,
	>(
		&self,
		insert: I,
		delete: D,
	) -> ClientResult<()> {
		let mut transaction = Transaction::new();
		for (k, v) in insert {
			transaction.set(columns::AUX, k, v);
		}
		for k in delete {
			transaction.remove(columns::AUX, k);
		}
		self.storage.db.commit(transaction)?;
		Ok(())
	}

	fn get_aux(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		Ok(self.storage.db.get(columns::AUX, key))
	}
}

impl<Block: BlockT> sc_client_api::backend::Backend<Block> for Backend<Block> {
	type BlockImportOperation = BlockImportOperation<Block>;
	type Blockchain = BlockchainDb<Block>;
	type State = RecordStatsState<RefTrackingState<Block>, Block>;
	type OffchainStorage = offchain::LocalStorage;

	fn begin_operation(&self) -> ClientResult<Self::BlockImportOperation> {
		Ok(BlockImportOperation {
			pending_block: None,
			old_state: self.empty_state()?,
			db_updates: PrefixedMemoryDB::default(),
			storage_updates: Default::default(),
			child_storage_updates: Default::default(),
			offchain_storage_updates: Default::default(),
			aux_ops: Vec::new(),
			finalized_blocks: Vec::new(),
			set_head: None,
			commit_state: false,
			index_ops: Default::default(),
		})
	}

	fn begin_state_operation(
		&self,
		operation: &mut Self::BlockImportOperation,
		block: Block::Hash,
	) -> ClientResult<()> {
		if block == Default::default() {
			operation.old_state = self.empty_state()?;
		} else {
			operation.old_state = self.state_at(block)?;
		}

		operation.commit_state = true;
		Ok(())
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation) -> ClientResult<()> {
		let usage = operation.old_state.usage_info();
		self.state_usage.merge_sm(usage);

		if let Err(e) = self.try_commit_operation(operation) {
			let state_meta_db = StateMetaDb(self.storage.db.clone());
			self.storage
				.state_db
				.reset(state_meta_db)
				.map_err(sp_blockchain::Error::from_state_db)?;
			Err(e)
		} else {
			Ok(())
		}
	}

	fn finalize_block(
		&self,
		hash: Block::Hash,
		justification: Option<Justification>,
	) -> ClientResult<()> {
		let mut transaction = Transaction::new();
		let header = self.blockchain.expect_header(BlockId::Hash(hash))?;
		let mut displaced = None;

		let m = self.finalize_block_with_transaction(
			&mut transaction,
			hash,
			&header,
			None,
			justification,
			&mut displaced,
		)?;
		self.storage.db.commit(transaction)?;
		self.blockchain.update_meta(m);
		Ok(())
	}

	fn append_justification(
		&self,
		hash: Block::Hash,
		justification: Justification,
	) -> ClientResult<()> {
		let mut transaction: Transaction<DbHash> = Transaction::new();
		let header = self.blockchain.expect_header(BlockId::Hash(hash))?;
		let number = *header.number();

		// Check if the block is finalized first.
		let is_descendent_of = is_descendent_of(&self.blockchain, None);
		let last_finalized = self.blockchain.last_finalized()?;

		// We can do a quick check first, before doing a proper but more expensive check
		if number > self.blockchain.info().finalized_number ||
			(hash != last_finalized && !is_descendent_of(&hash, &last_finalized)?)
		{
			return Err(ClientError::NotInFinalizedChain)
		}

		let justifications = if let Some(mut stored_justifications) =
			self.blockchain.justifications(hash)?
		{
			if !stored_justifications.append(justification) {
				return Err(ClientError::BadJustification("Duplicate consensus engine ID".into()))
			}
			stored_justifications
		} else {
			Justifications::from(justification)
		};

		transaction.set_from_vec(
			columns::JUSTIFICATIONS,
			&utils::number_and_hash_to_lookup_key(number, hash)?,
			justifications.encode(),
		);

		self.storage.db.commit(transaction)?;

		Ok(())
	}

	fn offchain_storage(&self) -> Option<Self::OffchainStorage> {
		Some(self.offchain_storage.clone())
	}

	fn usage_info(&self) -> Option<UsageInfo> {
		let (io_stats, state_stats) = self.io_stats.take_or_else(|| {
			(
				// TODO: implement DB stats and cache size retrieval
				kvdb::IoStats::empty(),
				self.state_usage.take(),
			)
		});
		let database_cache = MemorySize::from_bytes(0);
		let state_cache = MemorySize::from_bytes(
			self.shared_trie_cache.as_ref().map_or(0, |c| c.used_memory_size()),
		);
		let state_db = self.storage.state_db.memory_info();

		Some(UsageInfo {
			memory: MemoryInfo { state_cache, database_cache, state_db },
			io: IoInfo {
				transactions: io_stats.transactions,
				bytes_read: io_stats.bytes_read,
				bytes_written: io_stats.bytes_written,
				writes: io_stats.writes,
				reads: io_stats.reads,
				average_transaction_size: io_stats.avg_transaction_size() as u64,
				state_reads: state_stats.reads.ops,
				state_writes: state_stats.writes.ops,
				state_writes_cache: state_stats.overlay_writes.ops,
				state_reads_cache: state_stats.cache_reads.ops,
				state_writes_nodes: state_stats.nodes_writes.ops,
			},
		})
	}

	fn revert(
		&self,
		n: NumberFor<Block>,
		revert_finalized: bool,
	) -> ClientResult<(NumberFor<Block>, HashSet<Block::Hash>)> {
		let mut reverted_finalized = HashSet::new();

		let info = self.blockchain.info();

		let highest_leaf = self
			.blockchain
			.leaves
			.read()
			.highest_leaf()
			.and_then(|(n, h)| h.last().map(|h| (n, *h)));

		let best_number = info.best_number;
		let best_hash = info.best_hash;

		let finalized = info.finalized_number;

		let revertible = best_number - finalized;
		let n = if !revert_finalized && revertible < n { revertible } else { n };

		let (n, mut number_to_revert, mut hash_to_revert) = match highest_leaf {
			Some((l_n, l_h)) => (n + (l_n - best_number), l_n, l_h),
			None => (n, best_number, best_hash),
		};

		let mut revert_blocks = || -> ClientResult<NumberFor<Block>> {
			for c in 0..n.saturated_into::<u64>() {
				if number_to_revert.is_zero() {
					return Ok(c.saturated_into::<NumberFor<Block>>())
				}
				let mut transaction = Transaction::new();
				let removed =
					self.blockchain.header(BlockId::Hash(hash_to_revert))?.ok_or_else(|| {
						sp_blockchain::Error::UnknownBlock(format!(
							"Error reverting to {}. Block header not found.",
							hash_to_revert,
						))
					})?;
				let removed_hash = removed.hash();

				let prev_number = number_to_revert.saturating_sub(One::one());
				let prev_hash =
					if prev_number == best_number { best_hash } else { *removed.parent_hash() };

				if !self.have_state_at(prev_hash, prev_number) {
					return Ok(c.saturated_into::<NumberFor<Block>>())
				}

				match self.storage.state_db.revert_one() {
					Some(commit) => {
						apply_state_commit(&mut transaction, commit);

						number_to_revert = prev_number;
						hash_to_revert = prev_hash;

						let update_finalized = number_to_revert < finalized;

						let key = utils::number_and_hash_to_lookup_key(
							number_to_revert,
							&hash_to_revert,
						)?;
						if update_finalized {
							transaction.set_from_vec(
								columns::META,
								meta_keys::FINALIZED_BLOCK,
								key.clone(),
							);

							reverted_finalized.insert(removed_hash);
							if let Some((hash, _)) = self.blockchain.info().finalized_state {
								if hash == hash_to_revert {
									if !number_to_revert.is_zero() &&
										self.have_state_at(
											prev_hash,
											number_to_revert - One::one(),
										) {
										let lookup_key = utils::number_and_hash_to_lookup_key(
											number_to_revert - One::one(),
											prev_hash,
										)?;
										transaction.set_from_vec(
											columns::META,
											meta_keys::FINALIZED_STATE,
											lookup_key,
										);
									} else {
										transaction
											.remove(columns::META, meta_keys::FINALIZED_STATE);
									}
								}
							}
						}
						transaction.set_from_vec(columns::META, meta_keys::BEST_BLOCK, key);
						transaction.remove(columns::KEY_LOOKUP, removed.hash().as_ref());
						children::remove_children(
							&mut transaction,
							columns::META,
							meta_keys::CHILDREN_PREFIX,
							hash_to_revert,
						);
						self.storage.db.commit(transaction)?;

						let is_best = number_to_revert < best_number;

						self.blockchain.update_meta(MetaUpdate {
							hash: hash_to_revert,
							number: number_to_revert,
							is_best,
							is_finalized: update_finalized,
							with_state: false,
						});
					},
					None => return Ok(c.saturated_into::<NumberFor<Block>>()),
				}
			}

			Ok(n)
		};

		let reverted = revert_blocks()?;

		let revert_leaves = || -> ClientResult<()> {
			let mut transaction = Transaction::new();
			let mut leaves = self.blockchain.leaves.write();

			leaves.revert(hash_to_revert, number_to_revert);
			leaves.prepare_transaction(&mut transaction, columns::META, meta_keys::LEAF_PREFIX);
			self.storage.db.commit(transaction)?;

			Ok(())
		};

		revert_leaves()?;

		Ok((reverted, reverted_finalized))
	}

	fn remove_leaf_block(&self, hash: Block::Hash) -> ClientResult<()> {
		let best_hash = self.blockchain.info().best_hash;

		if best_hash == hash {
			return Err(sp_blockchain::Error::Backend(format!("Can't remove best block {:?}", hash)))
		}

		let hdr = self.blockchain.header_metadata(hash)?;
		if !self.have_state_at(hash, hdr.number) {
			return Err(sp_blockchain::Error::UnknownBlock(format!(
				"State already discarded for {:?}",
				hash
			)))
		}

		let mut leaves = self.blockchain.leaves.write();
		if !leaves.contains(hdr.number, hash) {
			return Err(sp_blockchain::Error::Backend(format!(
				"Can't remove non-leaf block {:?}",
				hash
			)))
		}

		let mut transaction = Transaction::new();
		if let Some(commit) = self.storage.state_db.remove(&hash) {
			apply_state_commit(&mut transaction, commit);
		}
		transaction.remove(columns::KEY_LOOKUP, hash.as_ref());

		let children: Vec<_> = self
			.blockchain()
			.children(hdr.parent)?
			.into_iter()
			.filter(|child_hash| *child_hash != hash)
			.collect();
		let parent_leaf = if children.is_empty() {
			children::remove_children(
				&mut transaction,
				columns::META,
				meta_keys::CHILDREN_PREFIX,
				hdr.parent,
			);
			Some(hdr.parent)
		} else {
			children::write_children(
				&mut transaction,
				columns::META,
				meta_keys::CHILDREN_PREFIX,
				hdr.parent,
				children,
			);
			None
		};

		let remove_outcome = leaves.remove(hash, hdr.number, parent_leaf);
		leaves.prepare_transaction(&mut transaction, columns::META, meta_keys::LEAF_PREFIX);
		if let Err(e) = self.storage.db.commit(transaction) {
			if let Some(outcome) = remove_outcome {
				leaves.undo().undo_remove(outcome);
			}
			return Err(e.into())
		}
		self.blockchain().remove_header_metadata(hash);
		Ok(())
	}

	fn blockchain(&self) -> &BlockchainDb<Block> {
		&self.blockchain
	}

	fn state_at(&self, hash: Block::Hash) -> ClientResult<Self::State> {
		if hash == self.blockchain.meta.read().genesis_hash {
			if let Some(genesis_state) = &*self.genesis_state.read() {
				let root = genesis_state.root;
				let db_state = DbStateBuilder::<Block>::new(genesis_state.clone(), root)
					.with_optional_cache(self.shared_trie_cache.as_ref().map(|c| c.local_cache()))
					.build();

				let state = RefTrackingState::new(db_state, self.storage.clone(), None);
				return Ok(RecordStatsState::new(state, None, self.state_usage.clone()))
			}
		}

		match self.blockchain.header_metadata(hash) {
			Ok(ref hdr) => {
				let hint = || {
					sc_state_db::NodeDb::get(self.storage.as_ref(), hdr.state_root.as_ref())
						.unwrap_or(None)
						.is_some()
				};
				if let Ok(()) =
					self.storage.state_db.pin(&hash, hdr.number.saturated_into::<u64>(), hint)
				{
					let root = hdr.state_root;
					let db_state = DbStateBuilder::<Block>::new(self.storage.clone(), root)
						.with_optional_cache(
							self.shared_trie_cache.as_ref().map(|c| c.local_cache()),
						)
						.build();
					let state = RefTrackingState::new(db_state, self.storage.clone(), Some(hash));
					Ok(RecordStatsState::new(state, Some(hash), self.state_usage.clone()))
				} else {
					Err(sp_blockchain::Error::UnknownBlock(format!(
						"State already discarded for {:?}",
						hash
					)))
				}
			},
			Err(e) => Err(e),
		}
	}

	fn have_state_at(&self, hash: Block::Hash, number: NumberFor<Block>) -> bool {
		if self.is_archive {
			match self.blockchain.header_metadata(hash) {
				Ok(header) => sp_state_machine::Storage::get(
					self.storage.as_ref(),
					&header.state_root,
					(&[], None),
				)
				.unwrap_or(None)
				.is_some(),
				_ => false,
			}
		} else {
			match self.storage.state_db.is_pruned(&hash, number.saturated_into::<u64>()) {
				IsPruned::Pruned => false,
				IsPruned::NotPruned => true,
				IsPruned::MaybePruned => match self.blockchain.header_metadata(hash) {
					Ok(header) => sp_state_machine::Storage::get(
						self.storage.as_ref(),
						&header.state_root,
						(&[], None),
					)
					.unwrap_or(None)
					.is_some(),
					_ => false,
				},
			}
		}
	}

	fn get_import_lock(&self) -> &RwLock<()> {
		&self.import_lock
	}

	fn requires_full_sync(&self) -> bool {
		matches!(
			self.storage.state_db.pruning_mode(),
			PruningMode::ArchiveAll | PruningMode::ArchiveCanonical
		)
	}
}

impl<Block: BlockT> sc_client_api::backend::LocalBackend<Block> for Backend<Block> {}

#[cfg(test)]
pub(crate) mod tests {
	use super::*;
	use crate::columns;
	use hash_db::{HashDB, EMPTY_PREFIX};
	use sc_client_api::{
		backend::{Backend as BTrait, BlockImportOperation as Op},
		blockchain::Backend as BLBTrait,
	};
	use sp_blockchain::{lowest_common_ancestor, tree_route};
	use sp_core::H256;
	use sp_runtime::{
		testing::{Block as RawBlock, ExtrinsicWrapper, Header},
		traits::{BlakeTwo256, Hash},
		ConsensusEngineId, StateVersion,
	};

	const CONS0_ENGINE_ID: ConsensusEngineId = *b"CON0";
	const CONS1_ENGINE_ID: ConsensusEngineId = *b"CON1";

	pub(crate) type Block = RawBlock<ExtrinsicWrapper<u64>>;

	pub fn insert_header(
		backend: &Backend<Block>,
		number: u64,
		parent_hash: H256,
		changes: Option<Vec<(Vec<u8>, Vec<u8>)>>,
		extrinsics_root: H256,
	) -> H256 {
		insert_block(backend, number, parent_hash, changes, extrinsics_root, Vec::new(), None)
			.unwrap()
	}

	pub fn insert_block(
		backend: &Backend<Block>,
		number: u64,
		parent_hash: H256,
		_changes: Option<Vec<(Vec<u8>, Vec<u8>)>>,
		extrinsics_root: H256,
		body: Vec<ExtrinsicWrapper<u64>>,
		transaction_index: Option<Vec<IndexOperation>>,
	) -> Result<H256, sp_blockchain::Error> {
		use sp_runtime::testing::Digest;

		let digest = Digest::default();
		let header = Header {
			number,
			parent_hash,
			state_root: BlakeTwo256::trie_root(Vec::new(), StateVersion::V1),
			digest,
			extrinsics_root,
		};
		let header_hash = header.hash();

		let block_hash = if number == 0 { Default::default() } else { parent_hash };
		let mut op = backend.begin_operation().unwrap();
		backend.begin_state_operation(&mut op, block_hash).unwrap();
		op.set_block_data(header, Some(body), None, None, NewBlockState::Best).unwrap();
		if let Some(index) = transaction_index {
			op.update_transaction_index(index).unwrap();
		}
		backend.commit_operation(op)?;

		Ok(header_hash)
	}

	pub fn insert_header_no_head(
		backend: &Backend<Block>,
		number: u64,
		parent_hash: H256,
		extrinsics_root: H256,
	) -> H256 {
		use sp_runtime::testing::Digest;

		let digest = Digest::default();
		let header = Header {
			number,
			parent_hash,
			state_root: BlakeTwo256::trie_root(Vec::new(), StateVersion::V1),
			digest,
			extrinsics_root,
		};
		let header_hash = header.hash();
		let mut op = backend.begin_operation().unwrap();
		op.set_block_data(header, None, None, None, NewBlockState::Normal).unwrap();
		backend.commit_operation(op).unwrap();
		header_hash
	}

	#[test]
	fn block_hash_inserted_correctly() {
		let backing = {
			let db = Backend::<Block>::new_test(1, 0);
			for i in 0..10 {
				assert!(db.blockchain().hash(i).unwrap().is_none());

				{
					let hash = if i == 0 {
						Default::default()
					} else {
						db.blockchain.hash(i - 1).unwrap().unwrap()
					};

					let mut op = db.begin_operation().unwrap();
					db.begin_state_operation(&mut op, hash).unwrap();
					let header = Header {
						number: i,
						parent_hash: hash,
						state_root: Default::default(),
						digest: Default::default(),
						extrinsics_root: Default::default(),
					};

					op.set_block_data(header, Some(vec![]), None, None, NewBlockState::Best)
						.unwrap();
					db.commit_operation(op).unwrap();
				}

				assert!(db.blockchain().hash(i).unwrap().is_some())
			}
			db.storage.db.clone()
		};

		let backend = Backend::<Block>::new(
			DatabaseSettings {
				trie_cache_maximum_size: Some(16 * 1024 * 1024),
				state_pruning: Some(PruningMode::blocks_pruning(1)),
				source: DatabaseSource::Custom { db: backing, require_create_flag: false },
				blocks_pruning: BlocksPruning::KeepFinalized,
			},
			0,
		)
		.unwrap();
		assert_eq!(backend.blockchain().info().best_number, 9);
		for i in 0..10 {
			assert!(backend.blockchain().hash(i).unwrap().is_some())
		}
	}

	#[test]
	fn set_state_data() {
		set_state_data_inner(StateVersion::V0);
		set_state_data_inner(StateVersion::V1);
	}
	fn set_state_data_inner(state_version: StateVersion) {
		let db = Backend::<Block>::new_test(2, 0);
		let hash = {
			let mut op = db.begin_operation().unwrap();
			let mut header = Header {
				number: 0,
				parent_hash: Default::default(),
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage = vec![(vec![1, 3, 5], vec![2, 4, 6]), (vec![1, 2, 3], vec![9, 9, 9])];

			header.state_root = op
				.old_state
				.storage_root(storage.iter().map(|(x, y)| (&x[..], Some(&y[..]))), state_version)
				.0
				.into();
			let hash = header.hash();

			op.reset_storage(
				Storage {
					top: storage.into_iter().collect(),
					children_default: Default::default(),
				},
				state_version,
			)
			.unwrap();
			op.set_block_data(header.clone(), Some(vec![]), None, None, NewBlockState::Best)
				.unwrap();

			db.commit_operation(op).unwrap();

			let state = db.state_at(hash).unwrap();

			assert_eq!(state.storage(&[1, 3, 5]).unwrap(), Some(vec![2, 4, 6]));
			assert_eq!(state.storage(&[1, 2, 3]).unwrap(), Some(vec![9, 9, 9]));
			assert_eq!(state.storage(&[5, 5, 5]).unwrap(), None);

			hash
		};

		{
			let mut op = db.begin_operation().unwrap();
			db.begin_state_operation(&mut op, hash).unwrap();
			let mut header = Header {
				number: 1,
				parent_hash: hash,
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage = vec![(vec![1, 3, 5], None), (vec![5, 5, 5], Some(vec![4, 5, 6]))];

			let (root, overlay) = op.old_state.storage_root(
				storage.iter().map(|(k, v)| (k.as_slice(), v.as_ref().map(|v| &v[..]))),
				state_version,
			);
			op.update_db_storage(overlay).unwrap();
			header.state_root = root.into();

			op.update_storage(storage, Vec::new()).unwrap();
			op.set_block_data(header.clone(), Some(vec![]), None, None, NewBlockState::Best)
				.unwrap();

			db.commit_operation(op).unwrap();

			let state = db.state_at(header.hash()).unwrap();

			assert_eq!(state.storage(&[1, 3, 5]).unwrap(), None);
			assert_eq!(state.storage(&[1, 2, 3]).unwrap(), Some(vec![9, 9, 9]));
			assert_eq!(state.storage(&[5, 5, 5]).unwrap(), Some(vec![4, 5, 6]));
		}
	}

	#[test]
	fn delete_only_when_negative_rc() {
		sp_tracing::try_init_simple();
		let state_version = StateVersion::default();
		let key;
		let backend = Backend::<Block>::new_test(1, 0);

		let hash = {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, Default::default()).unwrap();
			let mut header = Header {
				number: 0,
				parent_hash: Default::default(),
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			header.state_root =
				op.old_state.storage_root(std::iter::empty(), state_version).0.into();
			let hash = header.hash();

			op.reset_storage(
				Storage { top: Default::default(), children_default: Default::default() },
				state_version,
			)
			.unwrap();

			key = op.db_updates.insert(EMPTY_PREFIX, b"hello");
			op.set_block_data(header, Some(vec![]), None, None, NewBlockState::Best)
				.unwrap();

			backend.commit_operation(op).unwrap();
			assert_eq!(
				backend
					.storage
					.db
					.get(columns::STATE, &sp_trie::prefixed_key::<BlakeTwo256>(&key, EMPTY_PREFIX))
					.unwrap(),
				&b"hello"[..]
			);
			hash
		};

		let hashof1 = {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, hash).unwrap();
			let mut header = Header {
				number: 1,
				parent_hash: hash,
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage: Vec<(_, _)> = vec![];

			header.state_root = op
				.old_state
				.storage_root(storage.iter().cloned().map(|(x, y)| (x, Some(y))), state_version)
				.0
				.into();
			let hash = header.hash();

			op.db_updates.insert(EMPTY_PREFIX, b"hello");
			op.db_updates.remove(&key, EMPTY_PREFIX);
			op.set_block_data(header, Some(vec![]), None, None, NewBlockState::Best)
				.unwrap();

			backend.commit_operation(op).unwrap();
			assert_eq!(
				backend
					.storage
					.db
					.get(columns::STATE, &sp_trie::prefixed_key::<BlakeTwo256>(&key, EMPTY_PREFIX))
					.unwrap(),
				&b"hello"[..]
			);
			hash
		};

		let hashof2 = {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, hashof1).unwrap();
			let mut header = Header {
				number: 2,
				parent_hash: hashof1,
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage: Vec<(_, _)> = vec![];

			header.state_root = op
				.old_state
				.storage_root(storage.iter().cloned().map(|(x, y)| (x, Some(y))), state_version)
				.0
				.into();
			let hash = header.hash();

			op.db_updates.remove(&key, EMPTY_PREFIX);
			op.set_block_data(header, Some(vec![]), None, None, NewBlockState::Best)
				.unwrap();

			backend.commit_operation(op).unwrap();

			assert!(backend
				.storage
				.db
				.get(columns::STATE, &sp_trie::prefixed_key::<BlakeTwo256>(&key, EMPTY_PREFIX))
				.is_some());
			hash
		};

		let hashof3 = {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, hashof2).unwrap();
			let mut header = Header {
				number: 3,
				parent_hash: hashof2,
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage: Vec<(_, _)> = vec![];

			header.state_root = op
				.old_state
				.storage_root(storage.iter().cloned().map(|(x, y)| (x, Some(y))), state_version)
				.0
				.into();
			let hash = header.hash();

			op.set_block_data(header, Some(vec![]), None, None, NewBlockState::Best)
				.unwrap();

			backend.commit_operation(op).unwrap();
			assert!(backend
				.storage
				.db
				.get(columns::STATE, &sp_trie::prefixed_key::<BlakeTwo256>(&key, EMPTY_PREFIX))
				.is_none());
			hash
		};

		backend.finalize_block(hashof1, None).unwrap();
		backend.finalize_block(hashof2, None).unwrap();
		backend.finalize_block(hashof3, None).unwrap();
		assert!(backend
			.storage
			.db
			.get(columns::STATE, &sp_trie::prefixed_key::<BlakeTwo256>(&key, EMPTY_PREFIX))
			.is_none());
	}

	#[test]
	fn tree_route_works() {
		let backend = Backend::<Block>::new_test(1000, 100);
		let blockchain = backend.blockchain();
		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());

		// fork from genesis: 3 prong.
		let a1 = insert_header(&backend, 1, block0, None, Default::default());
		let a2 = insert_header(&backend, 2, a1, None, Default::default());
		let a3 = insert_header(&backend, 3, a2, None, Default::default());

		// fork from genesis: 2 prong.
		let b1 = insert_header(&backend, 1, block0, None, H256::from([1; 32]));
		let b2 = insert_header(&backend, 2, b1, None, Default::default());

		{
			let tree_route = tree_route(blockchain, a1, a1).unwrap();

			assert_eq!(tree_route.common_block().hash, a1);
			assert!(tree_route.retracted().is_empty());
			assert!(tree_route.enacted().is_empty());
		}

		{
			let tree_route = tree_route(blockchain, a3, b2).unwrap();

			assert_eq!(tree_route.common_block().hash, block0);
			assert_eq!(
				tree_route.retracted().iter().map(|r| r.hash).collect::<Vec<_>>(),
				vec![a3, a2, a1]
			);
			assert_eq!(
				tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(),
				vec![b1, b2]
			);
		}

		{
			let tree_route = tree_route(blockchain, a1, a3).unwrap();

			assert_eq!(tree_route.common_block().hash, a1);
			assert!(tree_route.retracted().is_empty());
			assert_eq!(
				tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(),
				vec![a2, a3]
			);
		}

		{
			let tree_route = tree_route(blockchain, a3, a1).unwrap();

			assert_eq!(tree_route.common_block().hash, a1);
			assert_eq!(
				tree_route.retracted().iter().map(|r| r.hash).collect::<Vec<_>>(),
				vec![a3, a2]
			);
			assert!(tree_route.enacted().is_empty());
		}

		{
			let tree_route = tree_route(blockchain, a2, a2).unwrap();

			assert_eq!(tree_route.common_block().hash, a2);
			assert!(tree_route.retracted().is_empty());
			assert!(tree_route.enacted().is_empty());
		}
	}

	#[test]
	fn tree_route_child() {
		let backend = Backend::<Block>::new_test(1000, 100);
		let blockchain = backend.blockchain();

		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let block1 = insert_header(&backend, 1, block0, None, Default::default());

		{
			let tree_route = tree_route(blockchain, block0, block1).unwrap();

			assert_eq!(tree_route.common_block().hash, block0);
			assert!(tree_route.retracted().is_empty());
			assert_eq!(
				tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(),
				vec![block1]
			);
		}
	}

	#[test]
	fn lowest_common_ancestor_works() {
		let backend = Backend::<Block>::new_test(1000, 100);
		let blockchain = backend.blockchain();
		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());

		// fork from genesis: 3 prong.
		let a1 = insert_header(&backend, 1, block0, None, Default::default());
		let a2 = insert_header(&backend, 2, a1, None, Default::default());
		let a3 = insert_header(&backend, 3, a2, None, Default::default());

		// fork from genesis: 2 prong.
		let b1 = insert_header(&backend, 1, block0, None, H256::from([1; 32]));
		let b2 = insert_header(&backend, 2, b1, None, Default::default());

		{
			let lca = lowest_common_ancestor(blockchain, a3, b2).unwrap();

			assert_eq!(lca.hash, block0);
			assert_eq!(lca.number, 0);
		}

		{
			let lca = lowest_common_ancestor(blockchain, a1, a3).unwrap();

			assert_eq!(lca.hash, a1);
			assert_eq!(lca.number, 1);
		}

		{
			let lca = lowest_common_ancestor(blockchain, a3, a1).unwrap();

			assert_eq!(lca.hash, a1);
			assert_eq!(lca.number, 1);
		}

		{
			let lca = lowest_common_ancestor(blockchain, a2, a3).unwrap();

			assert_eq!(lca.hash, a2);
			assert_eq!(lca.number, 2);
		}

		{
			let lca = lowest_common_ancestor(blockchain, a2, a1).unwrap();

			assert_eq!(lca.hash, a1);
			assert_eq!(lca.number, 1);
		}

		{
			let lca = lowest_common_ancestor(blockchain, a2, a2).unwrap();

			assert_eq!(lca.hash, a2);
			assert_eq!(lca.number, 2);
		}
	}

	#[test]
	fn test_tree_route_regression() {
		// NOTE: this is a test for a regression introduced in #3665, the result
		// of tree_route would be erroneously computed, since it was taking into
		// account the `ancestor` in `CachedHeaderMetadata` for the comparison.
		// in this test we simulate the same behavior with the side-effect
		// triggering the issue being eviction of a previously fetched record
		// from the cache, therefore this test is dependent on the LRU cache
		// size for header metadata, which is currently set to 5000 elements.
		let backend = Backend::<Block>::new_test(10000, 10000);
		let blockchain = backend.blockchain();

		let genesis = insert_header(&backend, 0, Default::default(), None, Default::default());

		let block100 = (1..=100).fold(genesis, |parent, n| {
			insert_header(&backend, n, parent, None, Default::default())
		});

		let block7000 = (101..=7000).fold(block100, |parent, n| {
			insert_header(&backend, n, parent, None, Default::default())
		});

		// This will cause the ancestor of `block100` to be set to `genesis` as a side-effect.
		lowest_common_ancestor(blockchain, genesis, block100).unwrap();

		// While traversing the tree we will have to do 6900 calls to
		// `header_metadata`, which will make sure we will exhaust our cache
		// which only takes 5000 elements. In particular, the `CachedHeaderMetadata` struct for
		// block #100 will be evicted and will get a new value (with ancestor set to its parent).
		let tree_route = tree_route(blockchain, block100, block7000).unwrap();

		assert!(tree_route.retracted().is_empty());
	}

	#[test]
	fn test_leaves_with_complex_block_tree() {
		let backend: Arc<Backend<substrate_test_runtime_client::runtime::Block>> =
			Arc::new(Backend::new_test(20, 20));
		substrate_test_runtime_client::trait_tests::test_leaves_for_backend(backend);
	}

	#[test]
	fn test_children_with_complex_block_tree() {
		let backend: Arc<Backend<substrate_test_runtime_client::runtime::Block>> =
			Arc::new(Backend::new_test(20, 20));
		substrate_test_runtime_client::trait_tests::test_children_for_backend(backend);
	}

	#[test]
	fn test_blockchain_query_by_number_gets_canonical() {
		let backend: Arc<Backend<substrate_test_runtime_client::runtime::Block>> =
			Arc::new(Backend::new_test(20, 20));
		substrate_test_runtime_client::trait_tests::test_blockchain_query_by_number_gets_canonical(
			backend,
		);
	}

	#[test]
	fn test_leaves_pruned_on_finality() {
		let backend: Backend<Block> = Backend::new_test(10, 10);
		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());

		let block1_a = insert_header(&backend, 1, block0, None, Default::default());
		let block1_b = insert_header(&backend, 1, block0, None, [1; 32].into());
		let block1_c = insert_header(&backend, 1, block0, None, [2; 32].into());

		assert_eq!(backend.blockchain().leaves().unwrap(), vec![block1_a, block1_b, block1_c]);

		let block2_a = insert_header(&backend, 2, block1_a, None, Default::default());
		let block2_b = insert_header(&backend, 2, block1_b, None, Default::default());
		let block2_c = insert_header(&backend, 2, block1_b, None, [1; 32].into());

		assert_eq!(
			backend.blockchain().leaves().unwrap(),
			vec![block2_a, block2_b, block2_c, block1_c]
		);

		backend.finalize_block(block1_a, None).unwrap();
		backend.finalize_block(block2_a, None).unwrap();

		// leaves at same height stay. Leaves at lower heights pruned.
		assert_eq!(backend.blockchain().leaves().unwrap(), vec![block2_a, block2_b, block2_c]);
	}

	#[test]
	fn test_aux() {
		let backend: Backend<substrate_test_runtime_client::runtime::Block> =
			Backend::new_test(0, 0);
		assert!(backend.get_aux(b"test").unwrap().is_none());
		backend.insert_aux(&[(&b"test"[..], &b"hello"[..])], &[]).unwrap();
		assert_eq!(b"hello", &backend.get_aux(b"test").unwrap().unwrap()[..]);
		backend.insert_aux(&[], &[&b"test"[..]]).unwrap();
		assert!(backend.get_aux(b"test").unwrap().is_none());
	}

	#[test]
	fn test_finalize_block_with_justification() {
		use sc_client_api::blockchain::Backend as BlockChainBackend;

		let backend = Backend::<Block>::new_test(10, 10);

		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let block1 = insert_header(&backend, 1, block0, None, Default::default());

		let justification = Some((CONS0_ENGINE_ID, vec![1, 2, 3]));
		backend.finalize_block(block1, justification.clone()).unwrap();

		assert_eq!(
			backend.blockchain().justifications(block1).unwrap(),
			justification.map(Justifications::from),
		);
	}

	#[test]
	fn test_append_justification_to_finalized_block() {
		use sc_client_api::blockchain::Backend as BlockChainBackend;

		let backend = Backend::<Block>::new_test(10, 10);

		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let block1 = insert_header(&backend, 1, block0, None, Default::default());

		let just0 = (CONS0_ENGINE_ID, vec![1, 2, 3]);
		backend.finalize_block(block1, Some(just0.clone().into())).unwrap();

		let just1 = (CONS1_ENGINE_ID, vec![4, 5]);
		backend.append_justification(block1, just1.clone()).unwrap();

		let just2 = (CONS1_ENGINE_ID, vec![6, 7]);
		assert!(matches!(
			backend.append_justification(block1, just2),
			Err(ClientError::BadJustification(_))
		));

		let justifications = {
			let mut just = Justifications::from(just0);
			just.append(just1);
			just
		};
		assert_eq!(backend.blockchain().justifications(block1).unwrap(), Some(justifications),);
	}

	#[test]
	fn test_finalize_multiple_blocks_in_single_op() {
		let backend = Backend::<Block>::new_test(10, 10);

		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let block1 = insert_header(&backend, 1, block0, None, Default::default());
		let block2 = insert_header(&backend, 2, block1, None, Default::default());
		let block3 = insert_header(&backend, 3, block2, None, Default::default());
		let block4 = insert_header(&backend, 4, block3, None, Default::default());
		{
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, block0).unwrap();
			op.mark_finalized(block1, None).unwrap();
			op.mark_finalized(block2, None).unwrap();
			backend.commit_operation(op).unwrap();
		}
		{
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, block2).unwrap();
			op.mark_finalized(block3, None).unwrap();
			op.mark_finalized(block4, None).unwrap();
			backend.commit_operation(op).unwrap();
		}
	}

	#[test]
	fn storage_hash_is_cached_correctly() {
		let state_version = StateVersion::default();
		let backend = Backend::<Block>::new_test(10, 10);

		let hash0 = {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, Default::default()).unwrap();
			let mut header = Header {
				number: 0,
				parent_hash: Default::default(),
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage = vec![(b"test".to_vec(), b"test".to_vec())];

			header.state_root = op
				.old_state
				.storage_root(storage.iter().map(|(x, y)| (&x[..], Some(&y[..]))), state_version)
				.0
				.into();
			let hash = header.hash();

			op.reset_storage(
				Storage {
					top: storage.into_iter().collect(),
					children_default: Default::default(),
				},
				state_version,
			)
			.unwrap();
			op.set_block_data(header.clone(), Some(vec![]), None, None, NewBlockState::Best)
				.unwrap();

			backend.commit_operation(op).unwrap();

			hash
		};

		let block0_hash = backend.state_at(hash0).unwrap().storage_hash(&b"test"[..]).unwrap();

		let hash1 = {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, hash0).unwrap();
			let mut header = Header {
				number: 1,
				parent_hash: hash0,
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage = vec![(b"test".to_vec(), Some(b"test2".to_vec()))];

			let (root, overlay) = op.old_state.storage_root(
				storage.iter().map(|(k, v)| (k.as_slice(), v.as_ref().map(|v| &v[..]))),
				state_version,
			);
			op.update_db_storage(overlay).unwrap();
			header.state_root = root.into();
			let hash = header.hash();

			op.update_storage(storage, Vec::new()).unwrap();
			op.set_block_data(header, Some(vec![]), None, None, NewBlockState::Normal)
				.unwrap();

			backend.commit_operation(op).unwrap();

			hash
		};

		{
			let header = backend.blockchain().header(BlockId::Hash(hash1)).unwrap().unwrap();
			let mut op = backend.begin_operation().unwrap();
			op.set_block_data(header, None, None, None, NewBlockState::Best).unwrap();
			backend.commit_operation(op).unwrap();
		}

		let block1_hash = backend.state_at(hash1).unwrap().storage_hash(&b"test"[..]).unwrap();

		assert_ne!(block0_hash, block1_hash);
	}

	#[test]
	fn test_finalize_non_sequential() {
		let backend = Backend::<Block>::new_test(10, 10);

		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let block1 = insert_header(&backend, 1, block0, None, Default::default());
		let block2 = insert_header(&backend, 2, block1, None, Default::default());
		{
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, block0).unwrap();
			op.mark_finalized(block2, None).unwrap();
			backend.commit_operation(op).unwrap_err();
		}
	}

	#[test]
	fn prune_blocks_on_finalize() {
		let backend = Backend::<Block>::new_test_with_tx_storage(BlocksPruning::Some(2), 0);
		let mut blocks = Vec::new();
		let mut prev_hash = Default::default();
		for i in 0..5 {
			let hash = insert_block(
				&backend,
				i,
				prev_hash,
				None,
				Default::default(),
				vec![i.into()],
				None,
			)
			.unwrap();
			blocks.push(hash);
			prev_hash = hash;
		}

		{
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, blocks[4]).unwrap();
			for i in 1..5 {
				op.mark_finalized(blocks[i], None).unwrap();
			}
			backend.commit_operation(op).unwrap();
		}
		let bc = backend.blockchain();
		assert_eq!(None, bc.body(blocks[0]).unwrap());
		assert_eq!(None, bc.body(blocks[1]).unwrap());
		assert_eq!(None, bc.body(blocks[2]).unwrap());
		assert_eq!(Some(vec![3.into()]), bc.body(blocks[3]).unwrap());
		assert_eq!(Some(vec![4.into()]), bc.body(blocks[4]).unwrap());
	}

	#[test]
	fn prune_blocks_on_finalize_in_keep_all() {
		let backend = Backend::<Block>::new_test_with_tx_storage(BlocksPruning::KeepAll, 0);
		let mut blocks = Vec::new();
		let mut prev_hash = Default::default();
		for i in 0..5 {
			let hash = insert_block(
				&backend,
				i,
				prev_hash,
				None,
				Default::default(),
				vec![i.into()],
				None,
			)
			.unwrap();
			blocks.push(hash);
			prev_hash = hash;
		}

		let mut op = backend.begin_operation().unwrap();
		backend.begin_state_operation(&mut op, blocks[4]).unwrap();
		for i in 1..3 {
			op.mark_finalized(blocks[i], None).unwrap();
		}
		backend.commit_operation(op).unwrap();

		let bc = backend.blockchain();
		assert_eq!(Some(vec![0.into()]), bc.body(blocks[0]).unwrap());
		assert_eq!(Some(vec![1.into()]), bc.body(blocks[1]).unwrap());
		assert_eq!(Some(vec![2.into()]), bc.body(blocks[2]).unwrap());
		assert_eq!(Some(vec![3.into()]), bc.body(blocks[3]).unwrap());
		assert_eq!(Some(vec![4.into()]), bc.body(blocks[4]).unwrap());
	}

	#[test]
	fn prune_blocks_on_finalize_with_fork_in_keep_all() {
		let backend = Backend::<Block>::new_test_with_tx_storage(BlocksPruning::KeepAll, 10);
		let mut blocks = Vec::new();
		let mut prev_hash = Default::default();
		for i in 0..5 {
			let hash = insert_block(
				&backend,
				i,
				prev_hash,
				None,
				Default::default(),
				vec![i.into()],
				None,
			)
			.unwrap();
			blocks.push(hash);
			prev_hash = hash;
		}

		// insert a fork at block 2
		let fork_hash_root = insert_block(
			&backend,
			2,
			blocks[1],
			None,
			sp_core::H256::random(),
			vec![2.into()],
			None,
		)
		.unwrap();
		insert_block(
			&backend,
			3,
			fork_hash_root,
			None,
			H256::random(),
			vec![3.into(), 11.into()],
			None,
		)
		.unwrap();

		let mut op = backend.begin_operation().unwrap();
		backend.begin_state_operation(&mut op, blocks[4]).unwrap();
		op.mark_head(blocks[4]).unwrap();
		backend.commit_operation(op).unwrap();

		let bc = backend.blockchain();
		assert_eq!(Some(vec![2.into()]), bc.body(fork_hash_root).unwrap());

		for i in 1..5 {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, blocks[i]).unwrap();
			op.mark_finalized(blocks[i], None).unwrap();
			backend.commit_operation(op).unwrap();
		}

		assert_eq!(Some(vec![0.into()]), bc.body(blocks[0]).unwrap());
		assert_eq!(Some(vec![1.into()]), bc.body(blocks[1]).unwrap());
		assert_eq!(Some(vec![2.into()]), bc.body(blocks[2]).unwrap());
		assert_eq!(Some(vec![3.into()]), bc.body(blocks[3]).unwrap());
		assert_eq!(Some(vec![4.into()]), bc.body(blocks[4]).unwrap());

		assert_eq!(Some(vec![2.into()]), bc.body(fork_hash_root).unwrap());
		assert_eq!(bc.info().best_number, 4);
		for i in 0..5 {
			assert!(bc.hash(i).unwrap().is_some());
		}
	}

	#[test]
	fn prune_blocks_on_finalize_with_fork() {
		let backend = Backend::<Block>::new_test_with_tx_storage(BlocksPruning::Some(2), 10);
		let mut blocks = Vec::new();
		let mut prev_hash = Default::default();
		for i in 0..5 {
			let hash = insert_block(
				&backend,
				i,
				prev_hash,
				None,
				Default::default(),
				vec![i.into()],
				None,
			)
			.unwrap();
			blocks.push(hash);
			prev_hash = hash;
		}

		// insert a fork at block 2
		let fork_hash_root = insert_block(
			&backend,
			2,
			blocks[1],
			None,
			sp_core::H256::random(),
			vec![2.into()],
			None,
		)
		.unwrap();
		insert_block(
			&backend,
			3,
			fork_hash_root,
			None,
			H256::random(),
			vec![3.into(), 11.into()],
			None,
		)
		.unwrap();
		let mut op = backend.begin_operation().unwrap();
		backend.begin_state_operation(&mut op, blocks[4]).unwrap();
		op.mark_head(blocks[4]).unwrap();
		backend.commit_operation(op).unwrap();

		for i in 1..5 {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, blocks[4]).unwrap();
			op.mark_finalized(blocks[i], None).unwrap();
			backend.commit_operation(op).unwrap();
		}

		let bc = backend.blockchain();
		assert_eq!(None, bc.body(blocks[0]).unwrap());
		assert_eq!(None, bc.body(blocks[1]).unwrap());
		assert_eq!(None, bc.body(blocks[2]).unwrap());
		assert_eq!(Some(vec![3.into()]), bc.body(blocks[3]).unwrap());
		assert_eq!(Some(vec![4.into()]), bc.body(blocks[4]).unwrap());
	}

	#[test]
	fn indexed_data_block_body() {
		let backend = Backend::<Block>::new_test_with_tx_storage(BlocksPruning::Some(1), 10);

		let x0 = ExtrinsicWrapper::from(0u64).encode();
		let x1 = ExtrinsicWrapper::from(1u64).encode();
		let x0_hash = <HashFor<Block> as sp_core::Hasher>::hash(&x0[1..]);
		let x1_hash = <HashFor<Block> as sp_core::Hasher>::hash(&x1[1..]);
		let index = vec![
			IndexOperation::Insert {
				extrinsic: 0,
				hash: x0_hash.as_ref().to_vec(),
				size: (x0.len() - 1) as u32,
			},
			IndexOperation::Insert {
				extrinsic: 1,
				hash: x1_hash.as_ref().to_vec(),
				size: (x1.len() - 1) as u32,
			},
		];
		let hash = insert_block(
			&backend,
			0,
			Default::default(),
			None,
			Default::default(),
			vec![0u64.into(), 1u64.into()],
			Some(index),
		)
		.unwrap();
		let bc = backend.blockchain();
		assert_eq!(bc.indexed_transaction(x0_hash).unwrap().unwrap(), &x0[1..]);
		assert_eq!(bc.indexed_transaction(x1_hash).unwrap().unwrap(), &x1[1..]);

		let hashof0 = bc.info().genesis_hash;
		// Push one more blocks and make sure block is pruned and transaction index is cleared.
		let block1 =
			insert_block(&backend, 1, hash, None, Default::default(), vec![], None).unwrap();
		backend.finalize_block(block1, None).unwrap();
		assert_eq!(bc.body(hashof0).unwrap(), None);
		assert_eq!(bc.indexed_transaction(x0_hash).unwrap(), None);
		assert_eq!(bc.indexed_transaction(x1_hash).unwrap(), None);
	}

	#[test]
	fn index_invalid_size() {
		let backend = Backend::<Block>::new_test_with_tx_storage(BlocksPruning::Some(1), 10);

		let x0 = ExtrinsicWrapper::from(0u64).encode();
		let x1 = ExtrinsicWrapper::from(1u64).encode();
		let x0_hash = <HashFor<Block> as sp_core::Hasher>::hash(&x0[..]);
		let x1_hash = <HashFor<Block> as sp_core::Hasher>::hash(&x1[..]);
		let index = vec![
			IndexOperation::Insert {
				extrinsic: 0,
				hash: x0_hash.as_ref().to_vec(),
				size: (x0.len()) as u32,
			},
			IndexOperation::Insert {
				extrinsic: 1,
				hash: x1_hash.as_ref().to_vec(),
				size: (x1.len() + 1) as u32,
			},
		];
		insert_block(
			&backend,
			0,
			Default::default(),
			None,
			Default::default(),
			vec![0u64.into(), 1u64.into()],
			Some(index),
		)
		.unwrap();
		let bc = backend.blockchain();
		assert_eq!(bc.indexed_transaction(x0_hash).unwrap().unwrap(), &x0[..]);
		assert_eq!(bc.indexed_transaction(x1_hash).unwrap(), None);
	}

	#[test]
	fn renew_transaction_storage() {
		let backend = Backend::<Block>::new_test_with_tx_storage(BlocksPruning::Some(2), 10);
		let mut blocks = Vec::new();
		let mut prev_hash = Default::default();
		let x1 = ExtrinsicWrapper::from(0u64).encode();
		let x1_hash = <HashFor<Block> as sp_core::Hasher>::hash(&x1[1..]);
		for i in 0..10 {
			let mut index = Vec::new();
			if i == 0 {
				index.push(IndexOperation::Insert {
					extrinsic: 0,
					hash: x1_hash.as_ref().to_vec(),
					size: (x1.len() - 1) as u32,
				});
			} else if i < 5 {
				// keep renewing 1st
				index.push(IndexOperation::Renew { extrinsic: 0, hash: x1_hash.as_ref().to_vec() });
			} // else stop renewing
			let hash = insert_block(
				&backend,
				i,
				prev_hash,
				None,
				Default::default(),
				vec![i.into()],
				Some(index),
			)
			.unwrap();
			blocks.push(hash);
			prev_hash = hash;
		}

		for i in 1..10 {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, blocks[4]).unwrap();
			op.mark_finalized(blocks[i], None).unwrap();
			backend.commit_operation(op).unwrap();
			let bc = backend.blockchain();
			if i < 6 {
				assert!(bc.indexed_transaction(x1_hash).unwrap().is_some());
			} else {
				assert!(bc.indexed_transaction(x1_hash).unwrap().is_none());
			}
		}
	}

	#[test]
	fn remove_leaf_block_works() {
		let backend = Backend::<Block>::new_test_with_tx_storage(BlocksPruning::Some(2), 10);
		let mut blocks = Vec::new();
		let mut prev_hash = Default::default();
		for i in 0..2 {
			let hash = insert_block(
				&backend,
				i,
				prev_hash,
				None,
				Default::default(),
				vec![i.into()],
				None,
			)
			.unwrap();
			blocks.push(hash);
			prev_hash = hash;
		}

		for i in 0..2 {
			let hash = insert_block(
				&backend,
				2,
				blocks[1],
				None,
				sp_core::H256::random(),
				vec![i.into()],
				None,
			)
			.unwrap();
			blocks.push(hash);
		}

		// insert a fork at block 1, which becomes best block
		let best_hash = insert_block(
			&backend,
			1,
			blocks[0],
			None,
			sp_core::H256::random(),
			vec![42.into()],
			None,
		)
		.unwrap();

		assert_eq!(backend.blockchain().info().best_hash, best_hash);
		assert!(backend.remove_leaf_block(best_hash).is_err());

		assert_eq!(backend.blockchain().leaves().unwrap(), vec![blocks[2], blocks[3], best_hash]);
		assert_eq!(backend.blockchain().children(blocks[1]).unwrap(), vec![blocks[2], blocks[3]]);

		assert!(backend.have_state_at(blocks[3], 2));
		assert!(backend.blockchain().header(BlockId::hash(blocks[3])).unwrap().is_some());
		backend.remove_leaf_block(blocks[3]).unwrap();
		assert!(!backend.have_state_at(blocks[3], 2));
		assert!(backend.blockchain().header(BlockId::hash(blocks[3])).unwrap().is_none());
		assert_eq!(backend.blockchain().leaves().unwrap(), vec![blocks[2], best_hash]);
		assert_eq!(backend.blockchain().children(blocks[1]).unwrap(), vec![blocks[2]]);

		assert!(backend.have_state_at(blocks[2], 2));
		assert!(backend.blockchain().header(BlockId::hash(blocks[2])).unwrap().is_some());
		backend.remove_leaf_block(blocks[2]).unwrap();
		assert!(!backend.have_state_at(blocks[2], 2));
		assert!(backend.blockchain().header(BlockId::hash(blocks[2])).unwrap().is_none());
		assert_eq!(backend.blockchain().leaves().unwrap(), vec![best_hash, blocks[1]]);
		assert_eq!(backend.blockchain().children(blocks[1]).unwrap(), vec![]);

		assert!(backend.have_state_at(blocks[1], 1));
		assert!(backend.blockchain().header(BlockId::hash(blocks[1])).unwrap().is_some());
		backend.remove_leaf_block(blocks[1]).unwrap();
		assert!(!backend.have_state_at(blocks[1], 1));
		assert!(backend.blockchain().header(BlockId::hash(blocks[1])).unwrap().is_none());
		assert_eq!(backend.blockchain().leaves().unwrap(), vec![best_hash]);
		assert_eq!(backend.blockchain().children(blocks[0]).unwrap(), vec![best_hash]);
	}

	#[test]
	fn test_import_existing_block_as_new_head() {
		let backend: Backend<Block> = Backend::new_test(10, 3);
		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let block1 = insert_header(&backend, 1, block0, None, Default::default());
		let block2 = insert_header(&backend, 2, block1, None, Default::default());
		let block3 = insert_header(&backend, 3, block2, None, Default::default());
		let block4 = insert_header(&backend, 4, block3, None, Default::default());
		let block5 = insert_header(&backend, 5, block4, None, Default::default());
		assert_eq!(backend.blockchain().info().best_hash, block5);

		// Insert 1 as best again. This should fail because canonicalization_delay == 3 and best ==
		// 5
		let header = Header {
			number: 1,
			parent_hash: block0,
			state_root: BlakeTwo256::trie_root(Vec::new(), StateVersion::V1),
			digest: Default::default(),
			extrinsics_root: Default::default(),
		};
		let mut op = backend.begin_operation().unwrap();
		op.set_block_data(header, None, None, None, NewBlockState::Best).unwrap();
		assert!(matches!(backend.commit_operation(op), Err(sp_blockchain::Error::SetHeadTooOld)));

		// Insert 2 as best again.
		let header = Header {
			number: 2,
			parent_hash: block1,
			state_root: BlakeTwo256::trie_root(Vec::new(), StateVersion::V1),
			digest: Default::default(),
			extrinsics_root: Default::default(),
		};
		let mut op = backend.begin_operation().unwrap();
		op.set_block_data(header, None, None, None, NewBlockState::Best).unwrap();
		backend.commit_operation(op).unwrap();
		assert_eq!(backend.blockchain().info().best_hash, block2);
	}

	#[test]
	fn test_import_existing_block_as_final() {
		let backend: Backend<Block> = Backend::new_test(10, 10);
		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let block1 = insert_header(&backend, 1, block0, None, Default::default());
		let _block2 = insert_header(&backend, 2, block1, None, Default::default());
		// Genesis is auto finalized, the rest are not.
		assert_eq!(backend.blockchain().info().finalized_hash, block0);

		// Insert 1 as final again.
		let header = Header {
			number: 1,
			parent_hash: block0,
			state_root: BlakeTwo256::trie_root(Vec::new(), StateVersion::V1),
			digest: Default::default(),
			extrinsics_root: Default::default(),
		};

		let mut op = backend.begin_operation().unwrap();
		op.set_block_data(header, None, None, None, NewBlockState::Final).unwrap();
		backend.commit_operation(op).unwrap();

		assert_eq!(backend.blockchain().info().finalized_hash, block1);
	}

	#[test]
	fn test_import_existing_state_fails() {
		let backend: Backend<Block> = Backend::new_test(10, 10);
		let genesis =
			insert_block(&backend, 0, Default::default(), None, Default::default(), vec![], None)
				.unwrap();

		insert_block(&backend, 1, genesis, None, Default::default(), vec![], None).unwrap();
		let err = insert_block(&backend, 1, genesis, None, Default::default(), vec![], None)
			.err()
			.unwrap();
		match err {
			sp_blockchain::Error::StateDatabase(m) if m == "Block already exists" => (),
			e @ _ => panic!("Unexpected error {:?}", e),
		}
	}

	#[test]
	fn test_leaves_not_created_for_ancient_blocks() {
		let backend: Backend<Block> = Backend::new_test(10, 10);
		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());

		let block1_a = insert_header(&backend, 1, block0, None, Default::default());
		let block2_a = insert_header(&backend, 2, block1_a, None, Default::default());
		backend.finalize_block(block1_a, None).unwrap();
		assert_eq!(backend.blockchain().leaves().unwrap(), vec![block2_a]);

		// Insert a fork prior to finalization point. Leave should not be created.
		insert_header_no_head(&backend, 1, block0, [1; 32].into());
		assert_eq!(backend.blockchain().leaves().unwrap(), vec![block2_a]);
	}

	#[test]
	fn revert_non_best_blocks() {
		let backend = Backend::<Block>::new_test(10, 10);

		let genesis =
			insert_block(&backend, 0, Default::default(), None, Default::default(), vec![], None)
				.unwrap();

		let block1 =
			insert_block(&backend, 1, genesis, None, Default::default(), vec![], None).unwrap();

		let block2 =
			insert_block(&backend, 2, block1, None, Default::default(), vec![], None).unwrap();

		let block3 = {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, block1).unwrap();
			let header = Header {
				number: 3,
				parent_hash: block2,
				state_root: BlakeTwo256::trie_root(Vec::new(), StateVersion::V1),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			op.set_block_data(header.clone(), Some(Vec::new()), None, None, NewBlockState::Normal)
				.unwrap();

			backend.commit_operation(op).unwrap();

			header.hash()
		};

		let block4 = {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, block2).unwrap();
			let header = Header {
				number: 4,
				parent_hash: block3,
				state_root: BlakeTwo256::trie_root(Vec::new(), StateVersion::V1),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			op.set_block_data(header.clone(), Some(Vec::new()), None, None, NewBlockState::Normal)
				.unwrap();

			backend.commit_operation(op).unwrap();

			header.hash()
		};

		let block3_fork = {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, block2).unwrap();
			let header = Header {
				number: 3,
				parent_hash: block2,
				state_root: BlakeTwo256::trie_root(Vec::new(), StateVersion::V1),
				digest: Default::default(),
				extrinsics_root: H256::from_low_u64_le(42),
			};

			op.set_block_data(header.clone(), Some(Vec::new()), None, None, NewBlockState::Normal)
				.unwrap();

			backend.commit_operation(op).unwrap();

			header.hash()
		};

		assert!(backend.have_state_at(block1, 1));
		assert!(backend.have_state_at(block2, 2));
		assert!(backend.have_state_at(block3, 3));
		assert!(backend.have_state_at(block4, 4));
		assert!(backend.have_state_at(block3_fork, 3));

		assert_eq!(backend.blockchain.leaves().unwrap(), vec![block4, block3_fork]);
		assert_eq!(4, backend.blockchain.leaves.read().highest_leaf().unwrap().0);

		assert_eq!(3, backend.revert(1, false).unwrap().0);

		assert!(backend.have_state_at(block1, 1));
		assert!(!backend.have_state_at(block2, 2));
		assert!(!backend.have_state_at(block3, 3));
		assert!(!backend.have_state_at(block4, 4));
		assert!(!backend.have_state_at(block3_fork, 3));

		assert_eq!(backend.blockchain.leaves().unwrap(), vec![block1]);
		assert_eq!(1, backend.blockchain.leaves.read().highest_leaf().unwrap().0);
	}

	#[test]
	fn test_no_duplicated_leaves_allowed() {
		let backend: Backend<Block> = Backend::new_test(10, 10);
		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let block1 = insert_header(&backend, 1, block0, None, Default::default());
		// Add block 2 not as the best block
		let block2 = insert_header_no_head(&backend, 2, block1, Default::default());
		assert_eq!(backend.blockchain().leaves().unwrap(), vec![block2]);
		assert_eq!(backend.blockchain().info().best_hash, block1);

		// Add block 2 as the best block
		let block2 = insert_header(&backend, 2, block1, None, Default::default());
		assert_eq!(backend.blockchain().leaves().unwrap(), vec![block2]);
		assert_eq!(backend.blockchain().info().best_hash, block2);
	}
}
