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
#[cfg(feature = "include-wasm-blob")]
pub mod trait_tests;
mod block_builder_ext;

pub use client_ext::TestClient;
pub use block_builder_ext::BlockBuilderExt;
pub use client::{ExecutionStrategies, blockchain, backend, self};
pub use executor::{NativeExecutor, self};
pub use runtime;
pub use consensus;
pub use keyring::{sr25519::Keyring as AuthorityKeyring, AccountKeyring};

use std::{sync::Arc, collections::HashMap};
use futures::future::FutureResult;
use primitives::Blake2Hasher;
use runtime_primitives::StorageOverlay;
use runtime_primitives::traits::{
	Block as BlockT, Header as HeaderT, Hash as HashT, NumberFor
};
use runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
use state_machine::ExecutionStrategy;
use client::LocalCallExecutor;

#[cfg(feature = "include-wasm-blob")]
mod local_executor {
	#![allow(missing_docs)]
	use runtime;
	use executor::native_executor_instance;
	// FIXME #1576 change the macro and pass in the `BlakeHasher` that dispatch needs from here instead
	native_executor_instance!(
		pub LocalExecutor,
		runtime::api::dispatch,
		runtime::native_version,
		include_bytes!("../../test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm")
	);
}

/// Native executor used for tests.
#[cfg(feature = "include-wasm-blob")]
pub use local_executor::LocalExecutor;

/// Test client database backend.
pub type Backend = client_db::Backend<runtime::Block>;

/// Test client executor.
#[cfg(feature = "include-wasm-blob")]
pub type Executor = client::LocalCallExecutor<
	Backend,
	executor::NativeExecutor<LocalExecutor>,
>;

/// Test client light database backend.
pub type LightBackend = client::light::backend::Backend<
	client_db::light::LightStorage<runtime::Block>,
	LightFetcher,
	Blake2Hasher,
>;

/// Test client light fetcher.
pub struct LightFetcher;

/// Test client light executor.
#[cfg(feature = "include-wasm-blob")]
pub type LightExecutor = client::light::call_executor::RemoteOrLocalCallExecutor<
	runtime::Block,
	LightBackend,
	client::light::call_executor::RemoteCallExecutor<
		client::light::blockchain::Blockchain<
			client_db::light::LightStorage<runtime::Block>,
			LightFetcher
		>,
		LightFetcher
	>,
	client::LocalCallExecutor<
		client::light::backend::Backend<
			client_db::light::LightStorage<runtime::Block>,
			LightFetcher,
			Blake2Hasher
		>,
		executor::NativeExecutor<LocalExecutor>
	>
>;

/// A builder for creating a test client instance.
pub struct TestClientBuilder {
	execution_strategies: ExecutionStrategies,
	genesis_extension: HashMap<Vec<u8>, Vec<u8>>,
	support_changes_trie: bool,
}

impl TestClientBuilder {
	/// Create a new instance of the test client builder.
	pub fn new() -> Self {
		TestClientBuilder {
			execution_strategies: ExecutionStrategies::default(),
			genesis_extension: HashMap::default(),
			support_changes_trie: false,
		}
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
	pub fn set_genesis_extension(
		mut self,
		extension: HashMap<Vec<u8>, Vec<u8>>
	) -> Self {
		self.genesis_extension = extension;
		self
	}

	/// Enable/Disable changes trie support.
	pub fn set_support_changes_trie(mut self, enable: bool) -> Self {
		self.support_changes_trie = enable;
		self
	}

	/// Build the test client.
	#[cfg(feature = "include-wasm-blob")]
	pub fn build(self) -> client::Client<
		Backend, Executor, runtime::Block, runtime::RuntimeApi
	> {
		let backend = Arc::new(Backend::new_test(std::u32::MAX, std::u64::MAX));
		self.build_with_backend(backend)
	}

	/// Build the test client with the given backend.
	#[cfg(feature = "include-wasm-blob")]
	pub fn build_with_backend<B>(self, backend: Arc<B>) -> client::Client<
		B,
		client::LocalCallExecutor<B, executor::NativeExecutor<LocalExecutor>>,
		runtime::Block,
		runtime::RuntimeApi
	> where B: backend::LocalBackend<runtime::Block, Blake2Hasher> {
		let executor = NativeExecutor::new(None);
		let executor = LocalCallExecutor::new(backend.clone(), executor);

		client::Client::new(
			backend,
			executor,
			genesis_storage(self.support_changes_trie, self.genesis_extension),
			self.execution_strategies
		).expect("Creates new client")
	}

	/// Build the test client with the given native executor.
	pub fn build_with_native_executor<E>(
		self,
		executor: executor::NativeExecutor<E>
	) -> client::Client<
		Backend,
		client::LocalCallExecutor<Backend, executor::NativeExecutor<E>>,
		runtime::Block,
		runtime::RuntimeApi
	> where E: executor::NativeExecutionDispatch
	{
		let backend = Arc::new(Backend::new_test(std::u32::MAX, std::u64::MAX));
		let executor = LocalCallExecutor::new(backend.clone(), executor);

		client::Client::new(
			backend,
			executor,
			genesis_storage(self.support_changes_trie, self.genesis_extension),
			self.execution_strategies
		).expect("Creates new client")
	}
}

/// Creates new client instance used for tests.
#[cfg(feature = "include-wasm-blob")]
pub fn new() -> client::Client<Backend, Executor, runtime::Block, runtime::RuntimeApi> {
	new_with_backend(Arc::new(Backend::new_test(::std::u32::MAX, ::std::u64::MAX)), false)
}

/// Creates new light client instance used for tests.
#[cfg(feature = "include-wasm-blob")]
pub fn new_light() -> client::Client<LightBackend, LightExecutor, runtime::Block, runtime::RuntimeApi> {
	let storage = client_db::light::LightStorage::new_test();
	let blockchain = Arc::new(client::light::blockchain::Blockchain::new(storage));
	let backend = Arc::new(LightBackend::new(blockchain.clone()));
	let executor = NativeExecutor::new(None);
	let fetcher = Arc::new(LightFetcher);
	let remote_call_executor = client::light::call_executor::RemoteCallExecutor::new(blockchain.clone(), fetcher);
	let local_call_executor = client::LocalCallExecutor::new(backend.clone(), executor);
	let call_executor = LightExecutor::new(backend.clone(), remote_call_executor, local_call_executor);
	client::Client::new(backend, call_executor, genesis_storage(false, Default::default()), Default::default()).unwrap()
}

/// Creates new client instance used for tests with the given api execution strategy.
#[cfg(feature = "include-wasm-blob")]
pub fn new_with_execution_strategy(
	execution_strategy: ExecutionStrategy
) -> client::Client<Backend, Executor, runtime::Block, runtime::RuntimeApi> {
	TestClientBuilder::new().set_execution_strategy(execution_strategy).build()
}

/// Creates new test client instance that suports changes trie creation.
#[cfg(feature = "include-wasm-blob")]
pub fn new_with_changes_trie()
	-> client::Client<Backend, Executor, runtime::Block, runtime::RuntimeApi>
{
	TestClientBuilder::new().set_support_changes_trie(true).build()
}

/// Creates new client instance used for tests with an explicitly provided backend.
/// This is useful for testing backend implementations.
#[cfg(feature = "include-wasm-blob")]
pub fn new_with_backend<B>(
	backend: Arc<B>,
	support_changes_trie: bool
) -> client::Client<
	B,
	client::LocalCallExecutor<B, executor::NativeExecutor<LocalExecutor>>,
	runtime::Block,
	runtime::RuntimeApi
> where B: backend::LocalBackend<runtime::Block, Blake2Hasher>
{
	TestClientBuilder::new()
		.set_support_changes_trie(support_changes_trie)
		.build_with_backend(backend)
}

fn genesis_config(support_changes_trie: bool) -> GenesisConfig {
	GenesisConfig::new(support_changes_trie, vec![
		AuthorityKeyring::Alice.into(),
		AuthorityKeyring::Bob.into(),
		AuthorityKeyring::Charlie.into(),
	], vec![
		AccountKeyring::Alice.into(),
		AccountKeyring::Bob.into(),
		AccountKeyring::Charlie.into(),
	],
		1000
	)
}

fn genesis_storage(
	support_changes_trie: bool,
	extension: HashMap<Vec<u8>, Vec<u8>>
) -> StorageOverlay {
	let mut storage = genesis_config(support_changes_trie).genesis_map();
	storage.extend(extension.into_iter());

	let state_root = <<<runtime::Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
		storage.clone().into_iter()
	);
	let block: runtime::Block = client::genesis::construct_genesis_block(state_root);
	storage.extend(additional_storage_with_genesis(&block));
	storage
}

impl<Block: BlockT> client::light::fetcher::Fetcher<Block> for LightFetcher {
	type RemoteHeaderResult = FutureResult<Block::Header, client::error::Error>;
	type RemoteReadResult = FutureResult<Option<Vec<u8>>, client::error::Error>;
	type RemoteCallResult = FutureResult<Vec<u8>, client::error::Error>;
	type RemoteChangesResult = FutureResult<Vec<(NumberFor<Block>, u32)>, client::error::Error>;

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
}
