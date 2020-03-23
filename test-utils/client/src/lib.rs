// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

pub use sc_client::{blockchain, self};
pub use sc_client_api::{
	execution_extensions::{ExecutionStrategies, ExecutionExtensions},
	ForkBlocks, BadBlocks, CloneableSpawn,
};
pub use sc_client_db::{Backend, self};
pub use sp_consensus;
pub use sc_executor::{NativeExecutor, WasmExecutionMethod, self};
pub use sp_keyring::{
	AccountKeyring,
	ed25519::Keyring as Ed25519Keyring,
	sr25519::Keyring as Sr25519Keyring,
};
pub use sp_core::{traits::BareCryptoStorePtr, tasks::executor as tasks_executor};
pub use sp_runtime::{Storage, StorageChild};
pub use sp_state_machine::ExecutionStrategy;
pub use self::client_ext::{ClientExt, ClientBlockImportExt};

use std::sync::Arc;
use std::collections::HashMap;
use sp_core::storage::{well_known_keys, ChildInfo};
use sp_runtime::traits::{Block as BlockT, BlakeTwo256};
use sc_client::LocalCallExecutor;

/// Test client light database backend.
pub type LightBackend<Block> = sc_client::light::backend::Backend<
	sc_client_db::light::LightStorage<Block>,
	BlakeTwo256,
>;

/// A genesis storage initialization trait.
pub trait GenesisInit: Default {
	/// Construct genesis storage.
	fn genesis_storage(&self) -> Storage;
}

impl GenesisInit for () {
	fn genesis_storage(&self) -> Storage {
		Default::default()
	}
}

/// A builder for creating a test client instance.
pub struct TestClientBuilder<Block: BlockT, Executor, Backend, G: GenesisInit> {
	execution_strategies: ExecutionStrategies,
	genesis_init: G,
	child_storage_extension: HashMap<Vec<u8>, StorageChild>,
	backend: Arc<Backend>,
	_executor: std::marker::PhantomData<Executor>,
	keystore: Option<BareCryptoStorePtr>,
	fork_blocks: ForkBlocks<Block>,
	bad_blocks: BadBlocks<Block>,
}

impl<Block: BlockT, Executor, G: GenesisInit> Default
	for TestClientBuilder<Block, Executor, Backend<Block>, G> {
	fn default() -> Self {
		Self::with_default_backend()
	}
}

impl<Block: BlockT, Executor, G: GenesisInit> TestClientBuilder<Block, Executor, Backend<Block>, G> {
	/// Create new `TestClientBuilder` with default backend.
	pub fn with_default_backend() -> Self {
		let backend = Arc::new(Backend::new_test(std::u32::MAX, std::u64::MAX));
		Self::with_backend(backend)
	}

	/// Create new `TestClientBuilder` with default backend and pruning window size
	pub fn with_pruning_window(keep_blocks: u32) -> Self {
		let backend = Arc::new(Backend::new_test(keep_blocks, 0));
		Self::with_backend(backend)
	}
}

impl<Block: BlockT, Executor, Backend, G: GenesisInit> TestClientBuilder<Block, Executor, Backend, G> {
	/// Create a new instance of the test client builder.
	pub fn with_backend(backend: Arc<Backend>) -> Self {
		TestClientBuilder {
			backend,
			execution_strategies: ExecutionStrategies::default(),
			child_storage_extension: Default::default(),
			genesis_init: Default::default(),
			_executor: Default::default(),
			keystore: None,
			fork_blocks: None,
			bad_blocks: None,
		}
	}

	/// Set the keystore that should be used by the externalities.
	pub fn set_keystore(mut self, keystore: BareCryptoStorePtr) -> Self {
		self.keystore = Some(keystore);
		self
	}

	/// Alter the genesis storage parameters.
	pub fn genesis_init_mut(&mut self) -> &mut G {
		&mut self.genesis_init
	}

	/// Give access to the underlying backend of these clients
	pub fn backend(&self) -> Arc<Backend> {
		self.backend.clone()
	}

	/// Extend child storage
	pub fn add_child_storage(
		mut self,
		key: impl AsRef<[u8]>,
		child_key: impl AsRef<[u8]>,
		child_info: ChildInfo,
		value: impl AsRef<[u8]>,
	) -> Self {
		let entry = self.child_storage_extension.entry(key.as_ref().to_vec())
			.or_insert_with(|| StorageChild {
				data: Default::default(),
				child_info: child_info.to_owned(),
			});
		entry.data.insert(child_key.as_ref().to_vec(), value.as_ref().to_vec());
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

	/// Sets custom block rules.
	pub fn set_block_rules(mut self,
		fork_blocks: ForkBlocks<Block>,
		bad_blocks: BadBlocks<Block>,
	) -> Self {
		self.fork_blocks = fork_blocks;
		self.bad_blocks = bad_blocks;
		self
	}

	/// Build the test client with the given native executor.
	pub fn build_with_executor<RuntimeApi>(
		self,
		executor: Executor,
	) -> (
		sc_client::Client<
			Backend,
			Executor,
			Block,
			RuntimeApi,
		>,
		sc_client::LongestChain<Backend, Block>,
	) where
		Executor: sc_client::CallExecutor<Block> + 'static,
		Backend: sc_client_api::backend::Backend<Block>,
	{
		let storage = {
			let mut storage = self.genesis_init.genesis_storage();

			// Add some child storage keys.
			for (key, child_content) in self.child_storage_extension {
				storage.children.insert(
					well_known_keys::CHILD_STORAGE_KEY_PREFIX.iter().cloned().chain(key).collect(),
					StorageChild {
						data: child_content.data.into_iter().collect(),
						child_info: child_content.child_info,
					},
				);
			}

			storage
		};

		let client = sc_client::Client::new(
			self.backend.clone(),
			executor,
			&storage,
			self.fork_blocks,
			self.bad_blocks,
			ExecutionExtensions::new(
				self.execution_strategies,
				self.keystore.clone(),
			),
			None,
		).expect("Creates new client");

		let longest_chain = sc_client::LongestChain::new(self.backend);

		(client, longest_chain)
	}
}

impl<Block: BlockT, E, Backend, G: GenesisInit> TestClientBuilder<
	Block,
	sc_client::LocalCallExecutor<Backend, NativeExecutor<E>>,
	Backend,
	G,
> {
	/// Build the test client with the given native executor.
	pub fn build_with_native_executor<RuntimeApi, I>(
		self,
		executor: I,
	) -> (
		sc_client::Client<
			Backend,
			sc_client::LocalCallExecutor<Backend, NativeExecutor<E>>,
			Block,
			RuntimeApi
		>,
		sc_client::LongestChain<Backend, Block>,
	) where
		I: Into<Option<NativeExecutor<E>>>,
		E: sc_executor::NativeExecutionDispatch + 'static,
		Backend: sc_client_api::backend::Backend<Block> + 'static,
	{
		let executor = executor.into().unwrap_or_else(||
			NativeExecutor::new(WasmExecutionMethod::Interpreted, None, 8)
		);
		let executor = LocalCallExecutor::new(self.backend.clone(), executor, tasks_executor());

		self.build_with_executor(executor)
	}
}
