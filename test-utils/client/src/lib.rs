// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Client testing utilities.

#![warn(missing_docs)]

pub mod client_ext;

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
pub use sc_service::{RpcHandlers, RpcSession, client};
pub use self::client_ext::{ClientExt, ClientBlockImportExt};

use std::pin::Pin;
use std::sync::Arc;
use std::collections::{HashSet, HashMap};
use futures::{future::{Future, FutureExt}, stream::StreamExt};
use sp_core::storage::ChildInfo;
use sp_runtime::{OpaqueExtrinsic, codec::Encode, traits::{Block as BlockT, BlakeTwo256}};
use sc_service::client::{LocalCallExecutor, ClientConfig};
use sc_client_api::BlockchainEvents;

/// Test client light database backend.
pub type LightBackend<Block> = sc_light::Backend<
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
	/// The key is an unprefixed storage key, this only contains
	/// default child trie content.
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
		child_info: &ChildInfo,
		key: impl AsRef<[u8]>,
		value: impl AsRef<[u8]>,
	) -> Self {
		let storage_key = child_info.storage_key();
		let entry = self.child_storage_extension.entry(storage_key.to_vec())
			.or_insert_with(|| StorageChild {
				data: Default::default(),
				child_info: child_info.clone(),
			});
		entry.data.insert(key.as_ref().to_vec(), value.as_ref().to_vec());
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
		client::Client<
			Backend,
			Executor,
			Block,
			RuntimeApi,
		>,
		sc_consensus::LongestChain<Backend, Block>,
	) where
		Executor: sc_client_api::CallExecutor<Block> + 'static,
		Backend: sc_client_api::backend::Backend<Block>,
	{
		let storage = {
			let mut storage = self.genesis_init.genesis_storage();

			// Add some child storage keys.
			for (key, child_content) in self.child_storage_extension {
				storage.children_default.insert(
					key,
					StorageChild {
						data: child_content.data.into_iter().collect(),
						child_info: child_content.child_info,
					},
				);
			}

			storage
		};

		let client = client::Client::new(
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
			ClientConfig::default(),
		).expect("Creates new client");

		let longest_chain = sc_consensus::LongestChain::new(self.backend);

		(client, longest_chain)
	}
}

impl<Block: BlockT, E, Backend, G: GenesisInit> TestClientBuilder<
	Block,
	client::LocalCallExecutor<Backend, NativeExecutor<E>>,
	Backend,
	G,
> {
	/// Build the test client with the given native executor.
	pub fn build_with_native_executor<RuntimeApi, I>(
		self,
		executor: I,
	) -> (
		client::Client<
			Backend,
			client::LocalCallExecutor<Backend, NativeExecutor<E>>,
			Block,
			RuntimeApi
		>,
		sc_consensus::LongestChain<Backend, Block>,
	) where
		I: Into<Option<NativeExecutor<E>>>,
		E: sc_executor::NativeExecutionDispatch + 'static,
		Backend: sc_client_api::backend::Backend<Block> + 'static,
	{
		let executor = executor.into().unwrap_or_else(||
			NativeExecutor::new(WasmExecutionMethod::Interpreted, None, 8)
		);
		let executor = LocalCallExecutor::new(self.backend.clone(), executor, tasks_executor(), Default::default());

		self.build_with_executor(executor)
	}
}

/// An extension trait for `RpcHandlers`.
pub trait RpcHandlersExt {
	/// Send a transaction through the RpcHandlers.
	fn send_transaction(
		&self,
		extrinsic: OpaqueExtrinsic,
	) -> Pin<Box<dyn Future<
		Output = (
			Option<String>,
			RpcSession,
			futures01::sync::mpsc::Receiver<String>,
		),
	> + Send>>;
}

impl RpcHandlersExt for RpcHandlers {
	fn send_transaction(
		&self,
		extrinsic: OpaqueExtrinsic,
	) -> Pin<Box<dyn Future<
		Output = (
			Option<String>,
			RpcSession,
			futures01::sync::mpsc::Receiver<String>,
		),
	> + Send>> {
		let (tx, rx) = futures01::sync::mpsc::channel(0);
		let mem = RpcSession::new(tx.into());
		Box::pin(self
			.rpc_query(
				&mem,
				&format!(
					r#"{{
						"jsonrpc": "2.0",
						"method": "author_submitExtrinsic",
						"params": ["0x{}"],
						"id": 0
					}}"#,
					hex::encode(extrinsic.encode())
				),
			)
			.map(move |res| (res, mem, rx)))
	}
}

/// An extension trait for `BlockchainEvents`.
pub trait BlockchainEventsExt<C, B>
where
	C: BlockchainEvents<B>,
	B: BlockT,
{
	/// Wait for `count` blocks to be imported in the node and then exit. This function will not return if no blocks
	/// are ever created, thus you should restrict the maximum amount of time of the test execution.
	fn wait_for_blocks(&self, count: usize) -> Pin<Box<dyn Future<Output = ()> + Send>>;
}

impl<C, B> BlockchainEventsExt<C, B> for C
where
	C: BlockchainEvents<B>,
	B: BlockT,
{
	fn wait_for_blocks(&self, count: usize) -> Pin<Box<dyn Future<Output = ()> + Send>> {
		assert!(count > 0, "'count' argument must be greater than 0");

		let mut import_notification_stream = self.import_notification_stream();
		let mut blocks = HashSet::new();

		Box::pin(async move {
			while let Some(notification) = import_notification_stream.next().await {
				blocks.insert(notification.hash);
				if blocks.len() == count {
					break;
				}
			}
		})
	}
}
