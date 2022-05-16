// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

#[cfg(test)]
mod tests;

use std::sync::Arc;

use crate::SubscriptionTaskExecutor;

use jsonrpsee::{
	core::{async_trait, Error as JsonRpseeError, RpcResult},
	ws_server::PendingSubscription,
};

use sc_rpc_api::{state::ReadProof, DenyUnsafe};
use sp_core::{
	storage::{PrefixedStorageKey, StorageChangeSet, StorageData, StorageKey},
	Bytes,
};
use sp_runtime::traits::Block as BlockT;
use sp_version::RuntimeVersion;

use sp_api::{CallApiAt, Metadata, ProvideRuntimeApi};

use self::error::Error;

use sc_client_api::{
	Backend, BlockBackend, BlockchainEvents, ExecutorProvider, ProofProvider, StorageProvider,
};
pub use sc_rpc_api::{child_state::*, state::*};
use sp_blockchain::{HeaderBackend, HeaderMetadata};

const STORAGE_KEYS_PAGED_MAX_COUNT: u32 = 1000;

/// State backend API.
#[async_trait]
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

	/// Query historical storage entries (by key) starting from a block given as the second
	/// parameter.
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
		at: Option<Block::Hash>,
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
		methods: Option<String>,
	) -> Result<sp_rpc::tracing::TraceBlockResponse, Error>;

	/// New runtime version subscription
	fn subscribe_runtime_version(&self, sink: PendingSubscription);

	/// New storage subscription
	fn subscribe_storage(&self, sink: PendingSubscription, keys: Option<Vec<StorageKey>>);
}

/// Create new state API that works on full node.
pub fn new_full<BE, Block: BlockT, Client>(
	client: Arc<Client>,
	executor: SubscriptionTaskExecutor,
	deny_unsafe: DenyUnsafe,
	rpc_max_payload: Option<usize>,
) -> (StateApi<Block, Client>, ChildState<Block, Client>)
where
	Block: BlockT + 'static,
	Block::Hash: Unpin,
	BE: Backend<Block> + 'static,
	Client: ExecutorProvider<Block>
		+ StorageProvider<Block, BE>
		+ ProofProvider<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ BlockchainEvents<Block>
		+ CallApiAt<Block>
		+ HeaderBackend<Block>
		+ BlockBackend<Block>
		+ ProvideRuntimeApi<Block>
		+ Send
		+ Sync
		+ 'static,
	Client::Api: Metadata<Block>,
{
	let child_backend = Box::new(self::state_full::FullState::new(
		client.clone(),
		executor.clone(),
		rpc_max_payload,
	));
	let backend = Box::new(self::state_full::FullState::new(client, executor, rpc_max_payload));
	(StateApi { backend, deny_unsafe }, ChildState { backend: child_backend })
}

/// State API with subscriptions support.
pub struct StateApi<Block, Client> {
	backend: Box<dyn StateBackend<Block, Client>>,
	/// Whether to deny unsafe calls
	deny_unsafe: DenyUnsafe,
}

#[async_trait]
impl<Block, Client> StateApiServer<Block::Hash> for StateApi<Block, Client>
where
	Block: BlockT + 'static,
	Client: Send + Sync + 'static,
{
	async fn call(
		&self,
		method: String,
		data: Bytes,
		block: Option<Block::Hash>,
	) -> RpcResult<Bytes> {
		self.backend.call(block, method, data).await.map_err(Into::into)
	}

	async fn storage_keys(
		&self,
		key_prefix: StorageKey,
		block: Option<Block::Hash>,
	) -> RpcResult<Vec<StorageKey>> {
		self.backend.storage_keys(block, key_prefix).await.map_err(Into::into)
	}

	async fn storage_pairs(
		&self,
		key_prefix: StorageKey,
		block: Option<Block::Hash>,
	) -> RpcResult<Vec<(StorageKey, StorageData)>> {
		self.deny_unsafe.check_if_safe()?;
		self.backend.storage_pairs(block, key_prefix).await.map_err(Into::into)
	}

	async fn storage_keys_paged(
		&self,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
		block: Option<Block::Hash>,
	) -> RpcResult<Vec<StorageKey>> {
		if count > STORAGE_KEYS_PAGED_MAX_COUNT {
			return Err(JsonRpseeError::from(Error::InvalidCount {
				value: count,
				max: STORAGE_KEYS_PAGED_MAX_COUNT,
			}))
		}
		self.backend
			.storage_keys_paged(block, prefix, count, start_key)
			.await
			.map_err(Into::into)
	}

	async fn storage(
		&self,
		key: StorageKey,
		block: Option<Block::Hash>,
	) -> RpcResult<Option<StorageData>> {
		self.backend.storage(block, key).await.map_err(Into::into)
	}

	async fn storage_hash(
		&self,
		key: StorageKey,
		block: Option<Block::Hash>,
	) -> RpcResult<Option<Block::Hash>> {
		self.backend.storage_hash(block, key).await.map_err(Into::into)
	}

	async fn storage_size(
		&self,
		key: StorageKey,
		block: Option<Block::Hash>,
	) -> RpcResult<Option<u64>> {
		self.backend.storage_size(block, key).await.map_err(Into::into)
	}

	async fn metadata(&self, block: Option<Block::Hash>) -> RpcResult<Bytes> {
		self.backend.metadata(block).await.map_err(Into::into)
	}

	async fn runtime_version(&self, at: Option<Block::Hash>) -> RpcResult<RuntimeVersion> {
		self.backend.runtime_version(at).await.map_err(Into::into)
	}

	async fn query_storage(
		&self,
		keys: Vec<StorageKey>,
		from: Block::Hash,
		to: Option<Block::Hash>,
	) -> RpcResult<Vec<StorageChangeSet<Block::Hash>>> {
		self.deny_unsafe.check_if_safe()?;
		self.backend.query_storage(from, to, keys).await.map_err(Into::into)
	}

	async fn query_storage_at(
		&self,
		keys: Vec<StorageKey>,
		at: Option<Block::Hash>,
	) -> RpcResult<Vec<StorageChangeSet<Block::Hash>>> {
		self.backend.query_storage_at(keys, at).await.map_err(Into::into)
	}

	async fn read_proof(
		&self,
		keys: Vec<StorageKey>,
		block: Option<Block::Hash>,
	) -> RpcResult<ReadProof<Block::Hash>> {
		self.backend.read_proof(block, keys).await.map_err(Into::into)
	}

	/// Re-execute the given block with the tracing targets given in `targets`
	/// and capture all state changes.
	///
	/// Note: requires the node to run with `--rpc-methods=Unsafe`.
	/// Note: requires runtimes compiled with wasm tracing support, `--features with-tracing`.
	async fn trace_block(
		&self,
		block: Block::Hash,
		targets: Option<String>,
		storage_keys: Option<String>,
		methods: Option<String>,
	) -> RpcResult<sp_rpc::tracing::TraceBlockResponse> {
		self.deny_unsafe.check_if_safe()?;
		self.backend
			.trace_block(block, targets, storage_keys, methods)
			.await
			.map_err(Into::into)
	}

	fn subscribe_runtime_version(&self, sink: PendingSubscription) {
		self.backend.subscribe_runtime_version(sink)
	}

	fn subscribe_storage(&self, sink: PendingSubscription, keys: Option<Vec<StorageKey>>) {
		if keys.is_none() {
			if let Err(err) = self.deny_unsafe.check_if_safe() {
				let _ = sink.reject(JsonRpseeError::from(err));
				return
			}
		}

		self.backend.subscribe_storage(sink, keys)
	}
}

/// Child state backend API.
#[async_trait]
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

	/// Returns the keys with prefix from a child storage with pagination support.
	async fn storage_keys_paged(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
	) -> Result<Vec<StorageKey>, Error>;

	/// Returns a child storage entry at a specific block's state.
	async fn storage(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
	) -> Result<Option<StorageData>, Error>;

	/// Returns child storage entries at a specific block's state.
	async fn storage_entries(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
	) -> Result<Vec<Option<StorageData>>, Error>;

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
		self.storage(block, storage_key, key).await.map(|x| x.map(|x| x.0.len() as u64))
	}
}

/// Child state API with subscriptions support.
pub struct ChildState<Block, Client> {
	backend: Box<dyn ChildStateBackend<Block, Client>>,
}

#[async_trait]
impl<Block, Client> ChildStateApiServer<Block::Hash> for ChildState<Block, Client>
where
	Block: BlockT + 'static,
	Client: Send + Sync + 'static,
{
	async fn storage_keys(
		&self,
		storage_key: PrefixedStorageKey,
		key_prefix: StorageKey,
		block: Option<Block::Hash>,
	) -> RpcResult<Vec<StorageKey>> {
		self.backend
			.storage_keys(block, storage_key, key_prefix)
			.await
			.map_err(Into::into)
	}

	async fn storage_keys_paged(
		&self,
		storage_key: PrefixedStorageKey,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
		block: Option<Block::Hash>,
	) -> RpcResult<Vec<StorageKey>> {
		self.backend
			.storage_keys_paged(block, storage_key, prefix, count, start_key)
			.await
			.map_err(Into::into)
	}

	async fn storage(
		&self,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
		block: Option<Block::Hash>,
	) -> RpcResult<Option<StorageData>> {
		self.backend.storage(block, storage_key, key).await.map_err(Into::into)
	}

	async fn storage_entries(
		&self,
		storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
		block: Option<Block::Hash>,
	) -> RpcResult<Vec<Option<StorageData>>> {
		self.backend.storage_entries(block, storage_key, keys).await.map_err(Into::into)
	}

	async fn storage_hash(
		&self,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
		block: Option<Block::Hash>,
	) -> RpcResult<Option<Block::Hash>> {
		self.backend.storage_hash(block, storage_key, key).await.map_err(Into::into)
	}

	async fn storage_size(
		&self,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
		block: Option<Block::Hash>,
	) -> RpcResult<Option<u64>> {
		self.backend.storage_size(block, storage_key, key).await.map_err(Into::into)
	}

	async fn read_child_proof(
		&self,
		child_storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
		block: Option<Block::Hash>,
	) -> RpcResult<ReadProof<Block::Hash>> {
		self.backend
			.read_child_proof(block, child_storage_key, keys)
			.await
			.map_err(Into::into)
	}
}

fn client_err(err: sp_blockchain::Error) -> Error {
	Error::Client(Box::new(err))
}
