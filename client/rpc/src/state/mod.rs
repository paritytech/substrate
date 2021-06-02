// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Substrate state API.

mod state_full;
mod state_light;

#[cfg(test)]
mod tests;

use std::sync::Arc;
use jsonrpsee_types::error::{Error as JsonRpseeError, CallError as JsonRpseeCallError};
use jsonrpsee_ws_server::RpcModule;

use sc_rpc_api::{DenyUnsafe, state::ReadProof};
use sc_client_api::light::{RemoteBlockchain, Fetcher};
use sp_core::{Bytes, storage::{StorageKey, PrefixedStorageKey, StorageData, StorageChangeSet}};
use sp_version::RuntimeVersion;
use sp_runtime::traits::Block as BlockT;

use sp_api::{Metadata, ProvideRuntimeApi, CallApiAt};

use self::error::Error;

pub use sc_rpc_api::state::*;
pub use sc_rpc_api::child_state::*;
use sc_client_api::{
	ExecutorProvider, StorageProvider, BlockchainEvents, Backend, BlockBackend, ProofProvider
};
use sp_blockchain::{HeaderMetadata, HeaderBackend};

const STORAGE_KEYS_PAGED_MAX_COUNT: u32 = 1000;

/// State backend API.
#[async_trait::async_trait]
pub trait StateBackend<Block: BlockT, Client>: Send + Sync + 'static
	where
		Block: BlockT + 'static,
		Client: Send + Sync + 'static,
{
	/// Call runtime method at given block.
	async fn call(
		&self,
		block: Option<Block::Hash>,
		method: String,
		call_data: Bytes,
	) -> Result<Bytes, Error>;

	/// Returns the keys with prefix, leave empty to get all the keys.
	async fn storage_keys(
		&self,
		block: Option<Block::Hash>,
		prefix: StorageKey,
	) -> Result<Vec<StorageKey>, Error>;

	/// Returns the keys with prefix along with their values, leave empty to get all the pairs.
	async fn storage_pairs(
		&self,
		block: Option<Block::Hash>,
		prefix: StorageKey,
	) -> Result<Vec<(StorageKey, StorageData)>, Error>;

	/// Returns the keys with prefix with pagination support.
	async fn storage_keys_paged(
		&self,
		block: Option<Block::Hash>,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
	) -> Result<Vec<StorageKey>, Error>;

	/// Returns a storage entry at a specific block's state.
	async fn storage(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> Result<Option<StorageData>, Error>;

	/// Returns the hash of a storage entry at a block's state.
	async fn storage_hash(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> Result<Option<Block::Hash>, Error>;

	/// Returns the size of a storage entry at a block's state.
	///
	/// If data is available at `key`, it is returned. Else, the sum of values who's key has `key`
	/// prefix is returned, i.e. all the storage (double) maps that have this prefix.
	async fn storage_size(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> Result<Option<u64>, Error>;

	/// Returns the runtime metadata as an opaque blob.
	async fn metadata(&self, block: Option<Block::Hash>) -> Result<Bytes, Error>;

	/// Get the runtime version.
	async fn runtime_version(&self, block: Option<Block::Hash>) -> Result<RuntimeVersion, Error>;

	/// Query historical storage entries (by key) starting from a block given as the second parameter.
	///
	/// NOTE This first returned result contains the initial state of storage for all keys.
	/// Subsequent values in the vector represent changes to the previous state (diffs).
	async fn query_storage(
		&self,
		from: Block::Hash,
		to: Option<Block::Hash>,
		keys: Vec<StorageKey>,
	) -> Result<Vec<StorageChangeSet<Block::Hash>>, Error>;

	/// Query storage entries (by key) starting at block hash given as the second parameter.
	async fn query_storage_at(
		&self,
		keys: Vec<StorageKey>,
		at: Option<Block::Hash>
	) -> Result<Vec<StorageChangeSet<Block::Hash>>, Error>;

	/// Returns proof of storage entries at a specific block's state.
	async fn read_proof(
		&self,
		block: Option<Block::Hash>,
		keys: Vec<StorageKey>,
	) -> Result<ReadProof<Block::Hash>, Error>;

	/// Trace storage changes for block
	async fn trace_block(
		&self,
		block: Block::Hash,
		targets: Option<String>,
		storage_keys: Option<String>,
	) -> Result<sp_rpc::tracing::TraceBlockResponse, Error>;
}

/// Create new state API that works on full node.
pub fn new_full<BE, Block: BlockT, Client>(
	client: Arc<Client>,
	deny_unsafe: DenyUnsafe,
) -> (State<Block, Client>, ChildState<Block, Client>)
	where
		Block: BlockT + 'static,
		BE: Backend<Block> + 'static,
		Client: ExecutorProvider<Block> + StorageProvider<Block, BE> + ProofProvider<Block>
			+ HeaderMetadata<Block, Error = sp_blockchain::Error> + BlockchainEvents<Block>
			+ CallApiAt<Block> + HeaderBackend<Block>
			+ BlockBackend<Block> + ProvideRuntimeApi<Block> + Send + Sync + 'static,
		Client::Api: Metadata<Block>,
{
	let child_backend = Box::new(
		self::state_full::FullState::new(client.clone())
	);
	let backend = Box::new(self::state_full::FullState::new(client));
	(State { backend, deny_unsafe }, ChildState { backend: child_backend })
}

/// Create new state API that works on light node.
pub fn new_light<BE, Block: BlockT, Client, F: Fetcher<Block>>(
	client: Arc<Client>,
	remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
	fetcher: Arc<F>,
	deny_unsafe: DenyUnsafe,
) -> (State<Block, Client>, ChildState<Block, Client>)
	where
		Block: BlockT + 'static,
		BE: Backend<Block> + 'static,
		Client: ExecutorProvider<Block> + StorageProvider<Block, BE>
			+ HeaderMetadata<Block, Error = sp_blockchain::Error>
			+ ProvideRuntimeApi<Block> + HeaderBackend<Block> + BlockchainEvents<Block>
			+ Send + Sync + 'static,
		F: Send + Sync + 'static,
{
	let child_backend = Box::new(self::state_light::LightState::new(
			client.clone(),
			remote_blockchain.clone(),
			fetcher.clone(),
	));

	let backend = Box::new(self::state_light::LightState::new(
			client,
			remote_blockchain,
			fetcher,
	));
	(State { backend, deny_unsafe }, ChildState { backend: child_backend })
}

/// State API with subscriptions support.
pub struct State<Block, Client> {
	backend: Box<dyn StateBackend<Block, Client>>,
	/// Whether to deny unsafe calls
	deny_unsafe: DenyUnsafe,
}

impl<Block, Client> State<Block, Client>
	where
		Block: BlockT + 'static,
		Client: Send + Sync + 'static,
{
	/// Convert this to a RPC module.
	pub fn into_rpc_module(self) -> Result<RpcModule<Self>, JsonRpseeError> {
		let mut ctx_module = RpcModule::new(self);

		ctx_module.register_method("state_call", |params, state| {
			let (method, data, block) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.call(block, method, data))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("state_getKeys", |params, state| {
			let (key_prefix, block) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.storage_keys(block, key_prefix))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("state_getPairs", |params, state| {
			state.deny_unsafe.check_if_safe()?;
			let (key_prefix, block) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.storage_pairs(block, key_prefix))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("state_getKeysPaged", |params, state| {
			let (prefix, count, start_key, block) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			if count > STORAGE_KEYS_PAGED_MAX_COUNT {
				return Err(JsonRpseeCallError::Failed(Box::new(Error::InvalidCount {
						value: count,
						max: STORAGE_KEYS_PAGED_MAX_COUNT,
					})
				));
			}
			futures::executor::block_on(state.backend.storage_keys_paged(block, prefix, count,start_key))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("state_getStorage", |params, state| {
			let (key, block) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.storage(block, key))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("state_getStorageHash", |params, state| {
			let (key, block) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.storage(block, key))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("state_getStorageSize", |params, state| {
			let (key, block) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.storage_size(block, key))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("state_getMetadata", |params, state| {
			let maybe_block = params.one().ok();
			futures::executor::block_on(state.backend.metadata(maybe_block))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("state_getRuntimeVersion", |params, state| {
			state.deny_unsafe.check_if_safe()?;
			let at = params.one().ok();
			futures::executor::block_on(state.backend.runtime_version(at))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("state_queryStorage", |params, state| {
			state.deny_unsafe.check_if_safe()?;
			let (keys, from, to) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.query_storage(from, to, keys))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("state_queryStorageAt", |params, state| {
			state.deny_unsafe.check_if_safe()?;
			let (keys, at) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.query_storage_at(keys, at))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("state_getReadProof", |params, state| {
			state.deny_unsafe.check_if_safe()?;
			let (keys, block) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.read_proof(block, keys))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("state_traceBlock", |params, state| {
			state.deny_unsafe.check_if_safe()?;
			let (block, targets, storage_keys) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.trace_block(block, targets, storage_keys))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;


		// TODO: add subscriptions.

		Ok(ctx_module)
	}
}

/// Child state backend API.
#[async_trait::async_trait]
pub trait ChildStateBackend<Block: BlockT, Client>: Send + Sync + 'static
	where
		Block: BlockT + 'static,
		Client: Send + Sync + 'static,
{
	/// Returns proof of storage for a child key entries at a specific block's state.
	async fn read_child_proof(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
	) -> Result<ReadProof<Block::Hash>, Error>;

	/// Returns the keys with prefix from a child storage,
	/// leave prefix empty to get all the keys.
	async fn storage_keys(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		prefix: StorageKey,
	) -> Result<Vec<StorageKey>, Error>;

	/// Returns a child storage entry at a specific block's state.
	async fn storage(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
	) -> Result<Option<StorageData>, Error>;

	/// Returns the hash of a child storage entry at a block's state.
	async fn storage_hash(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
	) -> Result<Option<Block::Hash>, Error>;

	/// Returns the size of a child storage entry at a block's state.
	async fn storage_size(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
	) -> Result<Option<u64>, Error> {
		self.storage(block, storage_key, key)
			.await
			.map(|x| x.map(|x| x.0.len() as u64))
	}
}

/// Child state API with subscriptions support.
pub struct ChildState<Block, Client> {
	backend: Box<dyn ChildStateBackend<Block, Client>>,
}

impl<Block, Client> ChildState<Block, Client>
	where
		Block: BlockT + 'static,
		Client: Send + Sync + 'static,
{
	/// Convert this to a RPC module.
	pub fn into_rpc_module(self) -> Result<RpcModule<Self>, JsonRpseeError> {
		let mut ctx_module = RpcModule::new(self);

		ctx_module.register_method("childstate_getStorage", |params, state| {
			let (storage_key, key, block) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.storage(block, storage_key, key))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("childstate_getKeys", |params, state| {
			let (storage_key, key, block) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.storage_keys(block, storage_key, key))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("childstate_getStorageHash", |params, state| {
			let (storage_key, key, block) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.storage_hash(block, storage_key, key))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		ctx_module.register_method("childstate_getStorageSize", |params, state| {
			let (storage_key, key, block) = params.parse().map_err(|_| JsonRpseeCallError::InvalidParams)?;
			futures::executor::block_on(state.backend.storage_size(block, storage_key, key))
				.map_err(|e| to_jsonrpsee_call_error(e))
		})?;

		Ok(ctx_module)
	}

}

fn client_err(err: sp_blockchain::Error) -> Error {
	Error::Client(Box::new(err))
}

fn to_jsonrpsee_call_error(err: Error) -> JsonRpseeCallError {
	JsonRpseeCallError::Failed(Box::new(err))
}
