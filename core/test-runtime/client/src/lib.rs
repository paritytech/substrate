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

use std::sync::Arc;
use std::collections::HashMap;
pub use block_builder_ext::BlockBuilderExt;
pub use generic_test_client::*;
pub use runtime;

use primitives::sr25519;
use runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
use sr_primitives::traits::{Block as BlockT, Header as HeaderT, Hash as HashT};

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
	pub use super::{AccountKeyring, Sr25519Keyring};
}

mod local_executor {
	#![allow(missing_docs)]
	use runtime;
	use crate::executor::native_executor_instance;
	// FIXME #1576 change the macro and pass in the `BlakeHasher` that dispatch needs from here instead
	native_executor_instance!(
		pub LocalExecutor,
		runtime::api::dispatch,
		runtime::native_version
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
pub type LightExecutor = client::light::call_executor::GenesisCallExecutor<
	LightBackend,
	client::LocalCallExecutor<
		client::light::backend::Backend<
			client_db::light::LightStorage<runtime::Block>,
			Blake2Hasher,
		>,
		NativeExecutor<LocalExecutor>
	>
>;

/// Parameters of test-client builder with test-runtime.
#[derive(Default)]
pub struct GenesisParameters {
	support_changes_trie: bool,
	heap_pages_override: Option<u64>,
	extra_storage: HashMap<Vec<u8>, Vec<u8>>,
	child_extra_storage: HashMap<Vec<u8>, HashMap<Vec<u8>, Vec<u8>>>,
}

impl GenesisParameters {
	fn genesis_config(&self) -> GenesisConfig {
		GenesisConfig::new(
			self.support_changes_trie,
			vec![
				sr25519::Public::from(Sr25519Keyring::Alice).into(),
				sr25519::Public::from(Sr25519Keyring::Bob).into(),
				sr25519::Public::from(Sr25519Keyring::Charlie).into(),
			],
			vec![
				AccountKeyring::Alice.into(),
				AccountKeyring::Bob.into(),
				AccountKeyring::Charlie.into(),
			],
			1000,
			self.heap_pages_override,
			self.extra_storage.clone(),
			self.child_extra_storage.clone(),
		)
	}
}

impl generic_test_client::GenesisInit for GenesisParameters {
	fn genesis_storage(&self) -> (StorageOverlay, ChildrenStorageOverlay) {
		use codec::Encode;
		let mut storage = self.genesis_config().genesis_map();

		let child_roots = storage.1.iter().map(|(sk, child_map)| {
			let state_root = <<<runtime::Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
				child_map.clone().into_iter().collect()
			);
			(sk.clone(), state_root.encode())
		});
		let state_root = <<<runtime::Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
			storage.0.clone().into_iter().chain(child_roots).collect()
		);
		let block: runtime::Block = client::genesis::construct_genesis_block(state_root);
		storage.0.extend(additional_storage_with_genesis(&block));

		storage
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

	/// Override the default value for Wasm heap pages.
	fn set_heap_pages(self, heap_pages: u64) -> Self;

	/// Add an extra value into the genesis storage.
	///
	/// # Panics
	///
	/// Panics if the key is empty.
	fn add_extra_child_storage<SK: Into<Vec<u8>>, K: Into<Vec<u8>>, V: Into<Vec<u8>>>(
		self,
		storage_key: SK,
		key: K,
		value: V,
	) -> Self;

	/// Add an extra child value into the genesis storage.
	///
	/// # Panics
	///
	/// Panics if the key is empty.
	fn add_extra_storage<K: Into<Vec<u8>>, V: Into<Vec<u8>>>(self, key: K, value: V) -> Self;

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
	fn set_heap_pages(mut self, heap_pages: u64) -> Self {
		self.genesis_init_mut().heap_pages_override = Some(heap_pages);
		self
	}

	fn set_support_changes_trie(mut self, support_changes_trie: bool) -> Self {
		self.genesis_init_mut().support_changes_trie = support_changes_trie;
		self
	}

	fn add_extra_storage<K: Into<Vec<u8>>, V: Into<Vec<u8>>>(mut self, key: K, value: V) -> Self {
		let key = key.into();
		assert!(!key.is_empty());
		self.genesis_init_mut().extra_storage.insert(key, value.into());
		self
	}

	fn add_extra_child_storage<SK: Into<Vec<u8>>, K: Into<Vec<u8>>, V: Into<Vec<u8>>>(
		mut self,
		storage_key: SK,
		key: K,
		value: V,
	) -> Self {
		let storage_key = storage_key.into();
		let key = key.into();
		assert!(!storage_key.is_empty());
		assert!(!key.is_empty());
		self.genesis_init_mut().child_extra_storage
			.entry(storage_key)
			.or_insert_with(Default::default)
			.insert(key, value.into());
		self
	}


	fn build_with_longest_chain(self) -> (Client<B>, client::LongestChain<B, runtime::Block>) {
		self.build_with_native_executor(None)
	}
}

/// Creates new client instance used for tests.
pub fn new() -> Client<Backend> {
	TestClientBuilder::new().build()
}

/// Creates new light client instance used for tests.
pub fn new_light() -> (
	client::Client<LightBackend, LightExecutor, runtime::Block, runtime::RuntimeApi>,
	Arc<LightBackend>,
) {

	let storage = client_db::light::LightStorage::new_test();
	let blockchain = Arc::new(client::light::blockchain::Blockchain::new(storage));
	let backend = Arc::new(LightBackend::new(blockchain.clone()));
	let executor = NativeExecutor::new(None);
	let local_call_executor = client::LocalCallExecutor::new(backend.clone(), executor, None);
	let call_executor = LightExecutor::new(
		backend.clone(),
		local_call_executor,
	);

	(
		TestClientBuilder::with_backend(backend.clone())
			.build_with_executor(call_executor)
			.0,
		backend,
	)
}
