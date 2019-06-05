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

use std::sync::Arc;
use futures::future::FutureResult;
use hash_db::Hasher;
use primitives::storage::well_known_keys;
use runtime_primitives::{StorageOverlay, ChildrenStorageOverlay};
use runtime_primitives::traits::{
	Block as BlockT, NumberFor
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

/// A builder for creating a test client instance.
pub struct TestClientBuilder<GenesisStorageParams = ()> {
	execution_strategies: ExecutionStrategies,
	genesis_init: Box<Fn(GenesisStorageParams) -> (StorageOverlay, ChildrenStorageOverlay)>,
	genesis_params: GenesisStorageParams,
}

impl<GenesisStorageParams: Default> TestClientBuilder<GenesisStorageParams> {
	/// Create a new instance of the test client builder.
	pub fn new() -> Self {
		Self::with_genesis_storage(|_| Default::default(), Default::default())
	}
}

impl<GenesisStorageParams> TestClientBuilder<GenesisStorageParams> {
	/// Set new genesis storage initialisation code.
	pub fn with_genesis_storage(
		genesis_init: impl Fn(GenesisStorageParams) -> (StorageOverlay, ChildrenStorageOverlay) + 'static,
		genesis_params: GenesisStorageParams,
	) -> Self {
		TestClientBuilder {
			execution_strategies: ExecutionStrategies::default(),
			genesis_init: Box::new(genesis_init) as _,
			genesis_params,
		}
	}

	/// Alter the genesis storage parameters.
	pub fn genesis_storage_params_mut(&mut self) -> &mut GenesisStorageParams {
		&mut self.genesis_params
	}

	/// Extend genesis storage.
	pub fn extend_genesis_storage(
		mut self,
		extender: impl Fn(&mut (StorageOverlay, ChildrenStorageOverlay)) + 'static,
	) -> Self where GenesisStorageParams: 'static {
		let genesis_init = std::mem::replace(&mut self.genesis_init, Box::new(|_| Default::default()));
		self.genesis_init = Box::new(move |params| {
			let mut storage = (*genesis_init)(params);
			(extender)(&mut storage);
			storage
		});
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

	/// Build the test client with the given native executor.
	pub fn build_with_native_executor<Block, E, RuntimeApi>(
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
		let executor = executor.into().unwrap_or_else(|| executor::NativeExecutor::new(None));
		let executor = LocalCallExecutor::new(backend.clone(), executor);

		self.build_with(backend, executor)
	}

	/// Build the test client with the given native executor.
	pub fn build_with<Block, Executor, Backend, RuntimeApi>(
		self,
		backend: Arc<Backend>,
		executor: Executor,
	) -> client::Client<
		Backend,
		Executor,
		Block,
		RuntimeApi,
	> where
		Executor: client::CallExecutor<Block, Blake2Hasher>,
		Backend: client::backend::Backend<Block, Blake2Hasher>,
		Block: BlockT<Hash=<Blake2Hasher as Hasher>::Out>,
	{

		let storage = {
			let mut storage = (self.genesis_init)(self.genesis_params);

			// Add some child storage keys.
			storage.1.insert(
				well_known_keys::CHILD_STORAGE_KEY_PREFIX.iter().chain(b"test").cloned().collect(),
				vec![(b"key".to_vec(), vec![42_u8])].into_iter().collect()
			);

			storage
		};

		client::Client::new(
			backend,
			executor,
			storage,
			self.execution_strategies
		).expect("Creates new client")
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
