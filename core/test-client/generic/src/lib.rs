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
pub use runtime_primitives::{StorageOverlay, ChildrenStorageOverlay};
pub use state_machine::ExecutionStrategy;

use std::sync::Arc;
use futures::future::FutureResult;
use hash_db::Hasher;
use primitives::storage::well_known_keys;
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

/// A genesis storage initialisation trait.
pub trait GenesisInit: Default {
	/// Construct genesis storage.
	fn genesis_storage(&self) -> (StorageOverlay, ChildrenStorageOverlay);
}

impl GenesisInit for () {
	fn genesis_storage(&self) -> (StorageOverlay, ChildrenStorageOverlay) {
		Default::default()
	}
}

/// A builder for creating a test client instance.
pub struct TestClientBuilder<Executor, Backend, G: GenesisInit = ()> {
	execution_strategies: ExecutionStrategies,
	genesis_init: G,
	backend: Arc<Backend>,
	_executor: std::marker::PhantomData<Executor>,
}

impl<Block, Executor, G: GenesisInit> TestClientBuilder<
	Executor,
	Backend<Block>,
	G,
> where
	Block: BlockT<Hash=<Blake2Hasher as Hasher>::Out>,
{
	/// Create a new `TestClientBuilder` with test backend.
	pub fn new() -> Self {
		let backend = Arc::new(Backend::new_test(std::u32::MAX, std::u64::MAX));
		Self::with_backend(backend)
	}
}

impl<Executor, Backend, G: GenesisInit> TestClientBuilder<
	Executor,
	Backend,
	G,
> {
	/// Create a new instance of the test client builder.
	pub fn with_backend(backend: Arc<Backend>) -> Self {
		TestClientBuilder {
			backend,
			execution_strategies: ExecutionStrategies::default(),
			genesis_init: Default::default(),
			_executor: Default::default(),
		}
	}

	/// Alter the genesis storage parameters.
	pub fn genesis_init_mut(&mut self) -> &mut G {
		&mut self.genesis_init
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
	pub fn build_with_executor<Block, RuntimeApi>(
		self,
		executor: Executor,
	) -> (
		client::Client<
			Backend,
			Executor,
			Block,
			RuntimeApi,
		>,
		client::LongestChain<Backend, Block>,
	) where
		Executor: client::CallExecutor<Block, Blake2Hasher>,
		Backend: client::backend::Backend<Block, Blake2Hasher>,
		Block: BlockT<Hash=<Blake2Hasher as Hasher>::Out>,
	{

		let storage = {
			let mut storage = self.genesis_init.genesis_storage();

			// Add some child storage keys.
			storage.1.insert(
				well_known_keys::CHILD_STORAGE_KEY_PREFIX.iter().chain(b"test").cloned().collect(),
				vec![(b"key".to_vec(), vec![42_u8])].into_iter().collect()
			);

			storage
		};

		let client = client::Client::new(
			self.backend.clone(),
			executor,
			storage,
			self.execution_strategies
		).expect("Creates new client");

		#[allow(deprecated)]
		let longest_chain = client::LongestChain::new(self.backend);

		(client, longest_chain)
	}
}

impl<E, Backend, G: GenesisInit> TestClientBuilder<
	client::LocalCallExecutor<Backend, executor::NativeExecutor<E>>,
	Backend,
	G,
> {
	/// Build the test client with the given native executor.
	pub fn build_with_native_executor<Block, RuntimeApi>(
		self,
		executor: impl Into<Option<executor::NativeExecutor<E>>>,
	) -> (
		client::Client<
			Backend,
			client::LocalCallExecutor<Backend, executor::NativeExecutor<E>>,
			Block,
			RuntimeApi
		>,
		client::LongestChain<Backend, Block>,
	) where
		E: executor::NativeExecutionDispatch,
		Backend: client::backend::Backend<Block, Blake2Hasher>,
		Block: BlockT<Hash=<Blake2Hasher as Hasher>::Out>,
	{
		let executor = executor.into().unwrap_or_else(|| executor::NativeExecutor::new(None));
		let executor = LocalCallExecutor::new(self.backend.clone(), executor);

		self.build_with_executor(executor)
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
