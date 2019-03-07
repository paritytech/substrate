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
pub mod trait_tests;
mod block_builder_ext;

pub use client_ext::TestClient;
pub use block_builder_ext::BlockBuilderExt;
pub use client;
pub use client::ExecutionStrategies;
pub use client::blockchain;
pub use client::backend;
pub use executor::NativeExecutor;
pub use keyring;
pub use runtime;
pub use consensus;

use std::sync::Arc;
use futures::future::FutureResult;
use primitives::Blake2Hasher;
use runtime_primitives::StorageOverlay;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Hash as HashT, NumberFor};
use runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
use keyring::Keyring;
use state_machine::ExecutionStrategy;
use client::LocalCallExecutor;

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
pub use local_executor::LocalExecutor;

/// Test client database backend.
pub type Backend = client_db::Backend<runtime::Block>;

/// Test client executor.
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

/// Creates new client instance used for tests.
pub fn new() -> client::Client<Backend, Executor, runtime::Block, runtime::RuntimeApi> {
	new_with_backend(Arc::new(Backend::new_test(::std::u32::MAX, ::std::u64::MAX)), false)
}

/// Creates new light client instance used for tests.
pub fn new_light() -> client::Client<LightBackend, LightExecutor, runtime::Block, runtime::RuntimeApi> {
	let storage = client_db::light::LightStorage::new_test();
	let blockchain = Arc::new(client::light::blockchain::Blockchain::new(storage));
	let backend = Arc::new(LightBackend::new(blockchain.clone()));
	let executor = NativeExecutor::new(None);
	let fetcher = Arc::new(LightFetcher);
	let remote_call_executor = client::light::call_executor::RemoteCallExecutor::new(blockchain.clone(), fetcher);
	let local_call_executor = client::LocalCallExecutor::new(backend.clone(), executor);
	let call_executor = LightExecutor::new(backend.clone(), remote_call_executor, local_call_executor);
	client::Client::new(backend, call_executor, genesis_storage(false), Default::default()).unwrap()
}

/// Creates new client instance used for tests with the given api execution strategy.
pub fn new_with_execution_strategy(
	execution_strategy: ExecutionStrategy
) -> client::Client<Backend, Executor, runtime::Block, runtime::RuntimeApi> {
	let backend = Arc::new(Backend::new_test(::std::u32::MAX, ::std::u64::MAX));
	let executor = NativeExecutor::new(None);
	let executor = LocalCallExecutor::new(backend.clone(), executor);

	let execution_strategies = ExecutionStrategies {
		syncing: execution_strategy,
		importing: execution_strategy,
		block_construction: execution_strategy,
		other: execution_strategy,
	};

	client::Client::new(
		backend,
		executor,
		genesis_storage(false),
		execution_strategies
	).expect("Creates new client")
}

/// Creates new test client instance that suports changes trie creation.
pub fn new_with_changes_trie()
	-> client::Client<Backend, Executor, runtime::Block, runtime::RuntimeApi>
{
	new_with_backend(Arc::new(Backend::new_test(::std::u32::MAX, ::std::u64::MAX)), true)
}

/// Creates new client instance used for tests with an explicitly provided backend.
/// This is useful for testing backend implementations.
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
	let executor = NativeExecutor::new(None);
	client::new_with_backend(backend, executor, genesis_storage(support_changes_trie)).unwrap()
}

fn genesis_config(support_changes_trie: bool) -> GenesisConfig {
	GenesisConfig::new(support_changes_trie, vec![
		Keyring::Alice.to_raw_public().into(),
		Keyring::Bob.to_raw_public().into(),
		Keyring::Charlie.to_raw_public().into(),
	], 1000)
}

fn genesis_storage(support_changes_trie: bool) -> StorageOverlay {
	let mut storage = genesis_config(support_changes_trie).genesis_map();
	let state_root = <<<runtime::Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(storage.clone().into_iter());
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
