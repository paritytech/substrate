// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Client testing utilities.

#![warn(missing_docs)]

pub mod client_ext;

pub use client::{ExecutionStrategies, blockchain, backend, self};
pub use client_db::{Backend, self};
pub use client_ext::TestClient;
pub use consensus;
pub use executor::{NativeExecutor, self};
pub use keyring::{sr25519::Keyring as AuthorityKeyring, AccountKeyring};
pub use primitives::Blake2Hasher;
pub use state_machine::ExecutionStrategy;

use std::{sync::Arc, collections::HashMap};
use futures::future::FutureResult;
use hash_db::Hasher;
use primitives::storage::well_known_keys;
use runtime_primitives::{StorageOverlay, ChildrenStorageOverlay};
use runtime_primitives::traits::{
	Block as BlockT, Header as HeaderT, Hash as HashT, NumberFor
};
use client::LocalCallExecutor;

/// Test client light database backend.
pub type LightBackend<Block> = client::light::backend::Backend<
	client_db::light::LightStorage<Block>,
	LightFetcher,
	Blake2Hasher,
>;

/// Test client light fetcher.
pub struct LightFetcher;

type ExtraStorage = HashMap<Vec<u8>, Vec<u8>>;

/// A builder for creating a test client instance.
pub struct TestClientBuilder<Block> {
	execution_strategies: ExecutionStrategies,
	genesis_extension: ExtraStorage,
	support_changes_trie: bool,
	genesis_config: Box<Fn(bool) -> StorageOverlay>,
	additional_storage_with_genesis: Box<Fn(&Block) -> ExtraStorage>,
}

impl<Block> TestClientBuilder<Block> {
	/// Create a new instance of the test client builder.
	pub fn new() -> Self {
		TestClientBuilder {
			execution_strategies: ExecutionStrategies::default(),
			genesis_extension: HashMap::default(),
			support_changes_trie: false,
			genesis_config: Box::new(|_| StorageOverlay::default()),
			additional_storage_with_genesis: Box::new(|_| ExtraStorage::default()),
		}
	}

	/// Set the genesis storage creator.
	#[deprecated]
	pub fn set_genesis_config(
		mut self,
		genesis_config: impl Fn(bool) -> StorageOverlay + 'static,
	) -> Self {
		self.genesis_config = Box::new(genesis_config) as _;
		self
	}

	/// Set the genesis storage creator.
	#[deprecated]
	pub fn set_additional_storage_with_genesis(
		mut self,
		extra_storage: impl Fn(&Block) -> ExtraStorage + 'static,
	) -> Self {
		self.additional_storage_with_genesis = Box::new(extra_storage) as _;
		self
	}

	/// Set the execution strategy that should be used by all contexts.
	pub fn set_execution_strategy(
		mut self,
		execution_strategy: ExecutionStrategy
	) -> Self {
		self.execution_strategies = ExecutionStrategies {
			syncing: execution_strategy,
			importing: execution_strategy,
			block_construction: execution_strategy,
			offchain_worker: execution_strategy,
			other: execution_strategy,
		};
		self
	}

	/// Set an extension of the genesis storage.
	#[deprecated]
	pub fn set_genesis_extension(
		mut self,
		extension: HashMap<Vec<u8>, Vec<u8>>
	) -> Self {
		self.genesis_extension = extension;
		self
	}

	/// Enable/Disable changes trie support.
	#[deprecated]
	pub fn set_support_changes_trie(mut self, enable: bool) -> Self {
		self.support_changes_trie = enable;
		self
	}

	/// Build the test client with the given native executor.
	pub fn build_with_native_executor<E, RuntimeApi>(
		self,
		executor: impl Into<Option<executor::NativeExecutor<E>>>,
	) -> client::Client<
		Backend<Block>,
		client::LocalCallExecutor<Backend<Block>, executor::NativeExecutor<E>>,
		Block,
		RuntimeApi
	> where
		E: executor::NativeExecutionDispatch,
		Block: BlockT<Hash=<Blake2Hasher as Hasher>::Out>,
	{
		let backend = Arc::new(Backend::new_test(std::u32::MAX, std::u64::MAX));
		self.build_with(backend, executor)
	}

	/// Build the test client with the given native executor.
	pub fn build_with<E, Backend, RuntimeApi>(
		self,
		backend: Arc<Backend>,
		executor: impl Into<Option<executor::NativeExecutor<E>>>,
	) -> client::Client<
		Backend,
		client::LocalCallExecutor<Backend, executor::NativeExecutor<E>>,
		Block,
		RuntimeApi,
	> where
		E: executor::NativeExecutionDispatch,
		Backend: client::backend::Backend<Block, Blake2Hasher>,
		Block: BlockT<Hash=<Blake2Hasher as Hasher>::Out>,
	{
		let executor = executor.into().unwrap_or_else(|| executor::NativeExecutor::new(None));
		let executor = LocalCallExecutor::new(backend.clone(), executor);

		client::Client::new(
			backend,
			executor,
			self.genesis_storage(),
			self.execution_strategies
		).expect("Creates new client")
	}

	fn genesis_storage(
		&self,
	) -> (StorageOverlay, ChildrenStorageOverlay) where
		Block: BlockT
	{
		let mut storage = (*self.genesis_config)(self.support_changes_trie);
		storage.extend(self.genesis_extension.clone());

		let state_root = <<<Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
			storage.clone().into_iter()
		);
		let block: Block = client::genesis::construct_genesis_block(state_root);
		storage.extend((*self.additional_storage_with_genesis)(&block));

		let mut child_storage = ChildrenStorageOverlay::default();
		child_storage.insert(
			well_known_keys::CHILD_STORAGE_KEY_PREFIX.iter().chain(b"test").cloned().collect(),
			vec![(b"key".to_vec(), vec![42_u8])].into_iter().collect()
		);

		(storage, child_storage)
	}
}

impl<Block: BlockT> client::light::fetcher::Fetcher<Block> for LightFetcher {
	type RemoteHeaderResult = FutureResult<Block::Header, client::error::Error>;
	type RemoteReadResult = FutureResult<Option<Vec<u8>>, client::error::Error>;
	type RemoteCallResult = FutureResult<Vec<u8>, client::error::Error>;
	type RemoteChangesResult = FutureResult<Vec<(NumberFor<Block>, u32)>, client::error::Error>;
	type RemoteBodyResult = FutureResult<Vec<Block::Extrinsic>, client::error::Error>;

	fn remote_header(
		&self,
		_request: client::light::fetcher::RemoteHeaderRequest<Block::Header>,
	) -> Self::RemoteHeaderResult {
		unimplemented!("not (yet) used in tests")
	}

	fn remote_read(
		&self,
		_request: client::light::fetcher::RemoteReadRequest<Block::Header>,
	) -> Self::RemoteReadResult {
		unimplemented!("not (yet) used in tests")
	}

	fn remote_read_child(
		&self,
		_request: client::light::fetcher::RemoteReadChildRequest<Block::Header>,
	) -> Self::RemoteReadResult {
		unimplemented!("not (yet) used in tests")
	}

	fn remote_call(
		&self,
		_request: client::light::fetcher::RemoteCallRequest<Block::Header>,
	) -> Self::RemoteCallResult {
		unimplemented!("not (yet) used in tests")
	}

	fn remote_changes(
		&self,
		_request: client::light::fetcher::RemoteChangesRequest<Block::Header>,
	) -> Self::RemoteChangesResult {
		unimplemented!("not (yet) used in tests")
	}

	fn remote_body(
		&self,
		_request: client::light::fetcher::RemoteBodyRequest<Block::Header>,
	) -> Self::RemoteBodyResult {
		unimplemented!("not (yet) used in tests")
	}
}
