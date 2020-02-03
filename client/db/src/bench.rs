// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! State backend that's useful for benchmarking

use std::sync::Arc;
use std::path::PathBuf;
use std::io;
use rand::Rng;

use hash_db::Prefix;
use sp_trie::{MemoryDB, prefixed_key};
use sp_core::storage::ChildInfo;
use sp_runtime::traits::{Block as BlockT, HasherFor};
use sp_runtime::Storage;
use sp_state_machine::{DBValue, backend::Backend as StateBackend};
use crate::{DatabaseSettings, DatabaseSettingsSrc, columns};
use crate::utils::DatabaseType;
//use log::{trace, debug, warn};
pub use sc_state_db::PruningMode;
use kvdb::{KeyValueDB, DBTransaction};

type DbState<B> = sp_state_machine::TrieBackend<
	Arc<dyn sp_state_machine::Storage<HasherFor<B>>>, HasherFor<B>
>;

struct StorageDb<Block: BlockT> {
	db: Arc<dyn KeyValueDB>,
	_block: std::marker::PhantomData<Block>,
}

impl<Block: BlockT> sp_state_machine::Storage<HasherFor<Block>> for StorageDb<Block> {
	fn get(&self, key: &Block::Hash, prefix: Prefix) -> Result<Option<DBValue>, String> {
		let key = prefixed_key::<HasherFor<Block>>(key, prefix);
		self.db.get(columns::STATE, &key)
			.map_err(|e| format!("Database backend error: {:?}", e))
	}
}

impl<Block: BlockT> sc_state_db::NodeDb for StorageDb<Block> {
	type Error = io::Error;
	type Key = [u8];

	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.db.get(columns::STATE, key).map(|r| r.map(|v| v.to_vec()))
	}
}

/// State that manages the backend database reference. Allows runtime to control the database.
pub struct BenchmarkingState<B: BlockT> {
	state: Option<DbState<B>>,
	db: Option<Arc<dyn KeyValueDB>>,
	path: PathBuf,
	root: B::Hash,
}

impl<B: BlockT> BenchmarkingState<B> {
	/// Create a new instance that creates a database in a temporary dir.
	pub fn new(genesis: Storage) -> Result<Self, String> {
		let temp_dir = PathBuf::from(std::env::temp_dir());
		let name: String = rand::thread_rng().sample_iter(&rand::distributions::Alphanumeric).take(10).collect();
		let path = temp_dir.join(&name);

		let mut root = B::Hash::default();
		let mut mdb = MemoryDB::<HasherFor<B>>::default();
		sp_state_machine::TrieDBMut::<HasherFor<B>>::new(&mut mdb, &mut root);

		std::fs::create_dir(&path).map_err(|_| String::from("Error creating temp dir"))?;
		let mut state = BenchmarkingState {
			state: None,
			db: None,
			path,
			root,
		};

		state.reopen()?;
		let child_delta = genesis.children.into_iter().map(|(storage_key, child_content)|	(
				storage_key,
				child_content.data.into_iter().map(|(k, v)| (k, Some(v))), child_content.child_info),
		);
		let (root, transaction) = state.state.as_ref().unwrap().full_storage_root(
			genesis.top.into_iter().map(|(k, v)| (k, Some(v))),
			child_delta,
		);
		state.commit(root, transaction)?;
		Ok(state)
	}

	fn reopen(&mut self) -> Result<(), String> {
		self.db = None;
		self.state = None;
		let config = DatabaseSettings {
			state_cache_size: 0,
			state_cache_child_ratio: None,
			pruning: PruningMode::ArchiveAll,
			source: DatabaseSettingsSrc::Path { path: self.path.clone(), cache_size: None },
		};

		let db = crate::utils::open_database::<B>(&config, DatabaseType::Full)
			.map_err(|e| format!("Error opening dadabase: {:?}", e))?;
		self.db = Some(db.clone());
		self.state = Some(DbState::<B>::new(Arc::new(StorageDb::<B> { db, _block: Default::default() }), self.root));
		Ok(())
	}

	fn kill(&mut self) -> Result<(), String> {
		self.db = None;
		self.state = None;
		std::fs::remove_dir_all(&self.path).map_err(|_| "Error removing database dir".into())
	}
}

impl<B: BlockT> Drop for BenchmarkingState<B> {
	fn drop(&mut self) {
		self.kill().ok();
	}
}

fn state_err() -> String {
	"State is not open".into()
}

impl<B: BlockT> StateBackend<HasherFor<B>> for BenchmarkingState<B> {
	type Error =  <DbState<B> as StateBackend<HasherFor<B>>>::Error;
	type Transaction = <DbState<B> as StateBackend<HasherFor<B>>>::Transaction;
	type TrieBackendStorage = <DbState<B> as StateBackend<HasherFor<B>>>::TrieBackendStorage;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.as_ref().ok_or_else(state_err)?.storage(key)
	}

	fn storage_hash(&self, key: &[u8]) -> Result<Option<B::Hash>, Self::Error> {
		self.state.as_ref().ok_or_else(state_err)?.storage_hash(key)
	}

	fn child_storage(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.as_ref().ok_or_else(state_err)?.child_storage(storage_key, child_info, key)
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		self.state.as_ref().ok_or_else(state_err)?.exists_storage(key)
	}

	fn exists_child_storage(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		key: &[u8],
	) -> Result<bool, Self::Error> {
		self.state.as_ref().ok_or_else(state_err)?.exists_child_storage(storage_key, child_info, key)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.as_ref().ok_or_else(state_err)?.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.as_ref().ok_or_else(state_err)?.next_child_storage_key(storage_key, child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		if let Some(state) = self.state.as_ref() {
			state.for_keys_with_prefix(prefix, f)
		}
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		if let Some(state) = self.state.as_ref() {
			state.for_key_values_with_prefix(prefix, f)
		}
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		f: F,
	) {
		if let Some(state) = self.state.as_ref() {
			state.for_keys_in_child_storage(storage_key, child_info, f)
		}
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		if let Some(state) = self.state.as_ref() {
			state.for_child_keys_with_prefix(storage_key, child_info, prefix, f)
		}
	}

	fn storage_root<I>(&self, delta: I) -> (B::Hash, Self::Transaction)
		where
			I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		self.state.as_ref().map_or(Default::default(), |s| s.storage_root(delta))
	}

	fn child_storage_root<I>(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		delta: I,
	) -> (B::Hash, bool, Self::Transaction)
		where
			I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
	{
		self.state.as_ref().map_or(Default::default(), |s| s.child_storage_root(storage_key, child_info, delta))
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.state.as_ref().map_or(Default::default(), |s| s.pairs())
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.state.as_ref().map_or(Default::default(), |s| s.keys(prefix))
	}

	fn child_keys(
		&self,
		storage_key: &[u8],
		child_info: ChildInfo,
		prefix: &[u8],
	) -> Vec<Vec<u8>> {
		self.state.as_ref().map_or(Default::default(), |s| s.child_keys(storage_key, child_info, prefix))
	}

	fn as_trie_backend(&mut self)
		-> Option<&sp_state_machine::TrieBackend<Self::TrieBackendStorage, HasherFor<B>>>
	{
		self.state.as_mut().map_or(None, |s| s.as_trie_backend())
	}

	fn commit(&mut self, storage_root: B::Hash, mut transaction: Self::Transaction) -> Result<(), Self::Error> {
		if let Some(db) = self.db.as_ref() {
			let mut db_transaction = DBTransaction::new();

			for (key, (val, rc)) in transaction.drain() {
				if rc > 0 {
					db_transaction.put(columns::STATE, &key, &val);
				} else if rc < 0 {
					db_transaction.delete(columns::STATE, &key);
				}
			}
			db.write(db_transaction).map_err(|_| String::from("Error committing transaction"))?;
			self.root = storage_root;
			self.reopen()
		} else {
			Err("Trying to commit to a closed db".into())
		}
	}

	fn wipe(&mut self) -> Result<(), Self::Error> {
		self.kill()?;
		self.reopen()
	}
}

impl<Block: BlockT> std::fmt::Debug for BenchmarkingState<Block> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "DB at {:?}", self.path)
	}
}

