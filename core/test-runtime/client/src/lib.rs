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

pub mod trait_tests;

mod block_builder_ext;

pub use block_builder_ext::BlockBuilderExt;
pub use generic_test_client::*;
pub use runtime;

use runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Hash as HashT};

/// A prelude to import in tests.
pub mod prelude {
	// Trait extensions
	pub use super::{BlockBuilderExt, DefaultTestClientBuilderExt, TestClientBuilderExt, ClientExt};
	// Client structs
	pub use super::{
		TestClient, TestClientBuilder, Backend, LightBackend,
		Executor, LightExecutor, LocalExecutor, NativeExecutor,
	};
	// Keyring
	pub use super::{AccountKeyring, AuthorityKeyring};
}

mod local_executor {
	#![allow(missing_docs)]
	use runtime;
	use crate::executor::native_executor_instance;
	// FIXME #1576 change the macro and pass in the `BlakeHasher` that dispatch needs from here instead
	native_executor_instance!(
		pub LocalExecutor,
		runtime::api::dispatch,
		runtime::native_version,
		include_bytes!("../../wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm")
	);
}

/// Native executor used for tests.
pub use local_executor::LocalExecutor;

/// Test client database backend.
pub type Backend = generic_test_client::Backend<runtime::Block>;

/// Test client executor.
pub type Executor = client::LocalCallExecutor<
	Backend,
	NativeExecutor<LocalExecutor>,
>;

/// Test client light database backend.
pub type LightBackend = generic_test_client::LightBackend<runtime::Block>;

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
		NativeExecutor<LocalExecutor>
	>
>;

/// Parameters of test-client builder with test-runtime.
#[derive(Default)]
pub struct GenesisParameters {
	support_changes_trie: bool,
}

impl generic_test_client::GenesisInit for GenesisParameters {
	fn genesis_storage(&self) -> (StorageOverlay, ChildrenStorageOverlay) {
		let mut storage = genesis_config(self.support_changes_trie).genesis_map();

		let state_root = <<<runtime::Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
			storage.clone().into_iter()
		);
		let block: runtime::Block = client::genesis::construct_genesis_block(state_root);
		storage.extend(additional_storage_with_genesis(&block));

		(storage, Default::default())
	}
}

/// A `TestClient` with `test-runtime` builder.
pub type TestClientBuilder<E, B> = generic_test_client::TestClientBuilder<E, B, GenesisParameters>;

/// Test client type with `LocalExecutor` and generic Backend.
pub type Client<B> = client::Client<
	B,
	client::LocalCallExecutor<B, executor::NativeExecutor<LocalExecutor>>,
	runtime::Block,
	runtime::RuntimeApi,
>;

/// A test client with default backend.
pub type TestClient = Client<Backend>;

/// A `TestClientBuilder` with default backend and executor.
pub trait DefaultTestClientBuilderExt: Sized {
	/// Create new `TestClientBuilder`
	fn new() -> Self;
}

impl DefaultTestClientBuilderExt for TestClientBuilder<
	Executor,
	Backend,
> {
	fn new() -> Self {
		Self::with_default_backend()
	}
}

/// A `test-runtime` extensions to `TestClientBuilder`.
pub trait TestClientBuilderExt<B>: Sized {
	/// Enable or disable support for changes trie in genesis.
	fn set_support_changes_trie(self, support_changes_trie: bool) -> Self;

	/// Build the test client.
	fn build(self) -> Client<B> {
		self.build_with_longest_chain().0
	}

	/// Build the test client and longest chain selector.
	fn build_with_longest_chain(self) -> (Client<B>, client::LongestChain<B, runtime::Block>);
}

impl<B> TestClientBuilderExt<B> for TestClientBuilder<
	client::LocalCallExecutor<B, executor::NativeExecutor<LocalExecutor>>,
	B
> where
	B: client::backend::Backend<runtime::Block, Blake2Hasher>,
{
	fn set_support_changes_trie(mut self, support_changes_trie: bool) -> Self {
		self.genesis_init_mut().support_changes_trie = support_changes_trie;
		self
	}

	fn build_with_longest_chain(self) -> (Client<B>, client::LongestChain<B, runtime::Block>) {
		self.build_with_native_executor(None)
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
pub fn new() -> Client<Backend> {
	TestClientBuilder::new().build()
}

/// Creates new light client instance used for tests.
pub fn new_light() -> client::Client<LightBackend, LightExecutor, runtime::Block, runtime::RuntimeApi> {
	use std::sync::Arc;

	let storage = client_db::light::LightStorage::new_test();
	let blockchain = Arc::new(client::light::blockchain::Blockchain::new(storage));
	let backend = Arc::new(LightBackend::new(blockchain.clone()));
	let executor = NativeExecutor::new(None);
	let fetcher = Arc::new(LightFetcher);
	let remote_call_executor = client::light::call_executor::RemoteCallExecutor::new(blockchain.clone(), fetcher);
	let local_call_executor = client::LocalCallExecutor::new(backend.clone(), executor);
	let call_executor = LightExecutor::new(backend.clone(), remote_call_executor, local_call_executor);

	TestClientBuilder::with_backend(backend)
		.build_with_executor(call_executor)
		.0
}
