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

#[cfg(feature = "include-wasm-blob")]
pub mod trait_tests;

mod block_builder_ext;

pub use block_builder_ext::BlockBuilderExt;
pub use generic_test_client::*;
pub use runtime;

use std::sync::Arc;
use runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Hash as HashT};

#[cfg(feature = "include-wasm-blob")]
mod local_executor {
	#![allow(missing_docs)]
	use runtime;
	use crate::executor::native_executor_instance;
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
pub type Backend = generic_test_client::Backend<runtime::Block>;

/// Test client executor.
#[cfg(feature = "include-wasm-blob")]
pub type Executor = client::LocalCallExecutor<
	Backend,
	NativeExecutor<LocalExecutor>,
>;

/// Test client light database backend.
pub type LightBackend = generic_test_client::LightBackend<runtime::Block>;

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
		NativeExecutor<LocalExecutor>
	>
>;

/// Parameters of test-client builder with test-runtime.
#[derive(Default)]
pub struct GenesisParameters {
	support_changes_trie: bool,
}

/// A `TestClient` with `test-runtime` builder.
pub type TestClientBuilder = generic_test_client::TestClientBuilder<GenesisParameters>;

/// A `test-runtime` extensions to `TestClientBuilder`.
pub trait TestClientBuilderExt: Sized {
	/// Create a new instance of the test client builder.
	fn new() -> Self;

	/// Enable or disable support for changes trie in genesis.
	fn set_support_changes_trie(self, support_changes_trie: bool) -> Self;

	/// Build the test client.
	#[cfg(feature = "include-wasm-blob")]
	fn build(self) -> client::Client<
		Backend, Executor, runtime::Block, runtime::RuntimeApi
	>;

	/// Build the test client with the given backend.
	#[cfg(feature = "include-wasm-blob")]
	fn build_with_backend<B>(self, backend: Arc<B>) -> client::Client<
		B,
		client::LocalCallExecutor<B, NativeExecutor<LocalExecutor>>,
		runtime::Block,
		runtime::RuntimeApi
	> where B: backend::LocalBackend<runtime::Block, Blake2Hasher>;
}

impl TestClientBuilderExt for TestClientBuilder {
	fn new() -> Self {
		generic_test_client::TestClientBuilder::with_genesis_storage(
			|params| {
				let mut storage = genesis_config(params.support_changes_trie).genesis_map();

				let state_root = <<<runtime::Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
					storage.clone().into_iter()
				);
				let block: runtime::Block = client::genesis::construct_genesis_block(state_root);
				storage.extend(additional_storage_with_genesis(&block));

				(storage, Default::default())
			},
			GenesisParameters::default(),
		)
	}

	fn set_support_changes_trie(mut self, support_changes_trie: bool) -> Self {
		self.genesis_storage_params_mut().support_changes_trie = support_changes_trie;
		self
	}

	#[cfg(feature = "include-wasm-blob")]
	fn build(self) -> client::Client<
		Backend, Executor, runtime::Block, runtime::RuntimeApi
	> {
		let backend = Arc::new(Backend::new_test(std::u32::MAX, std::u64::MAX));
		self.build_with_backend(backend)
	}

	#[cfg(feature = "include-wasm-blob")]
	fn build_with_backend<B>(self, backend: Arc<B>) -> client::Client<
		B,
		client::LocalCallExecutor<B, NativeExecutor<LocalExecutor>>,
		runtime::Block,
		runtime::RuntimeApi
	> where B: backend::LocalBackend<runtime::Block, Blake2Hasher> {
		let executor = client::LocalCallExecutor::new(backend.clone(), NativeExecutor::new(None));

		self.build_with(backend, executor)
	}
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

	TestClientBuilder::new()
		.build_with(backend, call_executor)
}

/// Creates new client instance used for tests with the given api execution strategy.
#[cfg(feature = "include-wasm-blob")]
pub fn new_with_execution_strategy(
	execution_strategy: ExecutionStrategy
) -> client::Client<Backend, Executor, runtime::Block, runtime::RuntimeApi> {
	TestClientBuilder::new()
		.set_execution_strategy(execution_strategy)
		.build()
}

/// Creates new test client instance that suports changes trie creation.
#[cfg(feature = "include-wasm-blob")]
pub fn new_with_changes_trie()
	-> client::Client<Backend, Executor, runtime::Block, runtime::RuntimeApi>
{
	TestClientBuilder::new()
		.set_support_changes_trie(true)
		.build()
}

/// Creates new client instance used for tests with an explicitly provided backend.
/// This is useful for testing backend implementations.
#[cfg(feature = "include-wasm-blob")]
pub fn new_with_backend<B>(
	backend: Arc<B>,
	support_changes_trie: bool
) -> client::Client<
	B,
	client::LocalCallExecutor<B, NativeExecutor<LocalExecutor>>,
	runtime::Block,
	runtime::RuntimeApi
> where B: backend::LocalBackend<runtime::Block, Blake2Hasher>
{
	TestClientBuilder::new()
		.set_support_changes_trie(support_changes_trie)
		.build_with_backend(backend)
}
