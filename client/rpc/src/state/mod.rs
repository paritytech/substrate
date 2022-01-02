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

use futures::FutureExt;
use jsonrpc_pubsub::{manager::SubscriptionManager, typed::Subscriber, SubscriptionId};
use rpc::Result as RpcResult;
use std::sync::Arc;

use sc_rpc_api::{state::ReadProof, DenyUnsafe};
use sp_core::{
	storage::{PrefixedStorageKey, StorageChangeSet, StorageData, StorageKey},
	Bytes,
};
use sp_runtime::traits::Block as BlockT;
use sp_version::RuntimeVersion;

use sp_api::{CallApiAt, Metadata, ProvideRuntimeApi};

use self::error::{Error, FutureResult};

use sc_client_api::{
	Backend, BlockBackend, BlockchainEvents, ExecutorProvider, ProofProvider, StorageProvider,
};
pub use sc_rpc_api::{child_state::*, state::*};
use sp_blockchain::{HeaderBackend, HeaderMetadata};

const STORAGE_KEYS_PAGED_MAX_COUNT: u32 = 1000;

/// State backend API.
pub trait StateBackend<Block: BlockT, Client>: Send + Sync + 'static
where
	Block: BlockT + 'static,
	Client: Send + Sync + 'static,
{
	/// Call runtime method at given block.
	fn call(
		&self,
		block: Option<Block::Hash>,
		method: String,
		call_data: Bytes,
	) -> FutureResult<Bytes>;

	/// Returns the keys with prefix, leave empty to get all the keys.
	fn storage_keys(
		&self,
		block: Option<Block::Hash>,
		prefix: StorageKey,
	) -> FutureResult<Vec<StorageKey>>;

	/// Returns the keys with prefix along with their values, leave empty to get all the pairs.
	fn storage_pairs(
		&self,
		block: Option<Block::Hash>,
		prefix: StorageKey,
	) -> FutureResult<Vec<(StorageKey, StorageData)>>;

	/// Returns the keys with prefix with pagination support.
	fn storage_keys_paged(
		&self,
		block: Option<Block::Hash>,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
	) -> FutureResult<Vec<StorageKey>>;

	/// Returns a storage entry at a specific block's state.
	fn storage(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<StorageData>>;

	/// Returns the hash of a storage entry at a block's state.
	fn storage_hash(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<Block::Hash>>;

	/// Returns the size of a storage entry at a block's state.
	///
	/// If data is available at `key`, it is returned. Else, the sum of values who's key has `key`
	/// prefix is returned, i.e. all the storage (double) maps that have this prefix.
	fn storage_size(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<u64>>;

	/// Returns the runtime metadata as an opaque blob.
	fn metadata(&self, block: Option<Block::Hash>) -> FutureResult<Bytes>;

	/// Get the runtime version.
	fn runtime_version(&self, block: Option<Block::Hash>) -> FutureResult<RuntimeVersion>;

	/// Query historical storage entries (by key) starting from a block given as the second
	/// parameter.
	///
	/// NOTE This first returned result contains the initial state of storage for all keys.
	/// Subsequent values in the vector represent changes to the previous state (diffs).
	fn query_storage(
		&self,
		from: Block::Hash,
		to: Option<Block::Hash>,
		keys: Vec<StorageKey>,
	) -> FutureResult<Vec<StorageChangeSet<Block::Hash>>>;

	/// Query storage entries (by key) starting at block hash given as the second parameter.
	fn query_storage_at(
		&self,
		keys: Vec<StorageKey>,
		at: Option<Block::Hash>,
	) -> FutureResult<Vec<StorageChangeSet<Block::Hash>>>;

	/// Returns proof of storage entries at a specific block's state.
	fn read_proof(
		&self,
		block: Option<Block::Hash>,
		keys: Vec<StorageKey>,
	) -> FutureResult<ReadProof<Block::Hash>>;

	/// New runtime version subscription
	fn subscribe_runtime_version(
		&self,
		_meta: crate::Metadata,
		subscriber: Subscriber<RuntimeVersion>,
	);

	/// Unsubscribe from runtime version subscription
	fn unsubscribe_runtime_version(
		&self,
		_meta: Option<crate::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool>;

	/// New storage subscription
	fn subscribe_storage(
		&self,
		_meta: crate::Metadata,
		subscriber: Subscriber<StorageChangeSet<Block::Hash>>,
		keys: Option<Vec<StorageKey>>,
	);

	/// Unsubscribe from storage subscription
	fn unsubscribe_storage(
		&self,
		_meta: Option<crate::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool>;

	/// Trace storage changes for block
	fn trace_block(
		&self,
		block: Block::Hash,
		targets: Option<String>,
		storage_keys: Option<String>,
		methods: Option<String>,
	) -> FutureResult<sp_rpc::tracing::TraceBlockResponse>;
}

/// Create new state API that works on full node.
pub fn new_full<BE, Block: BlockT, Client>(
	client: Arc<Client>,
	subscriptions: SubscriptionManager,
	deny_unsafe: DenyUnsafe,
	rpc_max_payload: Option<usize>,
) -> (State<Block, Client>, ChildState<Block, Client>)
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
		subscriptions.clone(),
		rpc_max_payload,
	));
	let backend =
		Box::new(self::state_full::FullState::new(client, subscriptions, rpc_max_payload));
	(State { backend, deny_unsafe }, ChildState { backend: child_backend })
}

/// State API with subscriptions support.
pub struct State<Block, Client> {
	backend: Box<dyn StateBackend<Block, Client>>,
	/// Whether to deny unsafe calls
	deny_unsafe: DenyUnsafe,
}

impl<Block, Client> StateApi<Block::Hash> for State<Block, Client>
where
	Block: BlockT + 'static,
	Client: Send + Sync + 'static,
{
	type Metadata = crate::Metadata;

	fn call(&self, method: String, data: Bytes, block: Option<Block::Hash>) -> FutureResult<Bytes> {
		self.backend.call(block, method, data)
	}

	fn storage_keys(
		&self,
		key_prefix: StorageKey,
		block: Option<Block::Hash>,
	) -> FutureResult<Vec<StorageKey>> {
		self.backend.storage_keys(block, key_prefix)
	}

	fn storage_pairs(
		&self,
		key_prefix: StorageKey,
		block: Option<Block::Hash>,
	) -> FutureResult<Vec<(StorageKey, StorageData)>> {
		if let Err(err) = self.deny_unsafe.check_if_safe() {
			return async move { Err(err.into()) }.boxed()
		}

		self.backend.storage_pairs(block, key_prefix)
	}

	fn storage_keys_paged(
		&self,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
		block: Option<Block::Hash>,
	) -> FutureResult<Vec<StorageKey>> {
		if count > STORAGE_KEYS_PAGED_MAX_COUNT {
			return async move {
				Err(Error::InvalidCount { value: count, max: STORAGE_KEYS_PAGED_MAX_COUNT })
			}
			.boxed()
		}
		self.backend.storage_keys_paged(block, prefix, count, start_key)
	}

	fn storage(
		&self,
		key: StorageKey,
		block: Option<Block::Hash>,
	) -> FutureResult<Option<StorageData>> {
		self.backend.storage(block, key)
	}

	fn storage_hash(
		&self,
		key: StorageKey,
		block: Option<Block::Hash>,
	) -> FutureResult<Option<Block::Hash>> {
		self.backend.storage_hash(block, key)
	}

	fn storage_size(
		&self,
		key: StorageKey,
		block: Option<Block::Hash>,
	) -> FutureResult<Option<u64>> {
		self.backend.storage_size(block, key)
	}

	fn metadata(&self, block: Option<Block::Hash>) -> FutureResult<Bytes> {
		self.backend.metadata(block)
	}

	fn query_storage(
		&self,
		keys: Vec<StorageKey>,
		from: Block::Hash,
		to: Option<Block::Hash>,
	) -> FutureResult<Vec<StorageChangeSet<Block::Hash>>> {
		if let Err(err) = self.deny_unsafe.check_if_safe() {
			return async move { Err(err.into()) }.boxed()
		}

		self.backend.query_storage(from, to, keys)
	}

	fn query_storage_at(
		&self,
		keys: Vec<StorageKey>,
		at: Option<Block::Hash>,
	) -> FutureResult<Vec<StorageChangeSet<Block::Hash>>> {
		self.backend.query_storage_at(keys, at)
	}

	fn read_proof(
		&self,
		keys: Vec<StorageKey>,
		block: Option<Block::Hash>,
	) -> FutureResult<ReadProof<Block::Hash>> {
		self.backend.read_proof(block, keys)
	}

	fn subscribe_storage(
		&self,
		meta: Self::Metadata,
		subscriber: Subscriber<StorageChangeSet<Block::Hash>>,
		keys: Option<Vec<StorageKey>>,
	) {
		self.backend.subscribe_storage(meta, subscriber, keys);
	}

	fn unsubscribe_storage(
		&self,
		meta: Option<Self::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		self.backend.unsubscribe_storage(meta, id)
	}

	fn runtime_version(&self, at: Option<Block::Hash>) -> FutureResult<RuntimeVersion> {
		self.backend.runtime_version(at)
	}

	fn subscribe_runtime_version(
		&self,
		meta: Self::Metadata,
		subscriber: Subscriber<RuntimeVersion>,
	) {
		self.backend.subscribe_runtime_version(meta, subscriber);
	}

	fn unsubscribe_runtime_version(
		&self,
		meta: Option<Self::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		self.backend.unsubscribe_runtime_version(meta, id)
	}

	/// Re-execute the given block with the tracing targets given in `targets`
	/// and capture all state changes.
	///
	/// Note: requires the node to run with `--rpc-methods=Unsafe`.
	/// Note: requires runtimes compiled with wasm tracing support, `--features with-tracing`.
	fn trace_block(
		&self,
		block: Block::Hash,
		targets: Option<String>,
		storage_keys: Option<String>,
		methods: Option<String>,
	) -> FutureResult<sp_rpc::tracing::TraceBlockResponse> {
		if let Err(err) = self.deny_unsafe.check_if_safe() {
			return async move { Err(err.into()) }.boxed()
		}

		self.backend.trace_block(block, targets, storage_keys, methods)
	}
}

/// Child state backend API.
pub trait ChildStateBackend<Block: BlockT, Client>: Send + Sync + 'static
where
	Block: BlockT + 'static,
	Client: Send + Sync + 'static,
{
	/// Returns proof of storage for a child key entries at a specific block's state.
	fn read_child_proof(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
	) -> FutureResult<ReadProof<Block::Hash>>;

	/// Returns the keys with prefix from a child storage,
	/// leave prefix empty to get all the keys.
	fn storage_keys(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		prefix: StorageKey,
	) -> FutureResult<Vec<StorageKey>>;

	/// Returns the keys with prefix from a child storage with pagination support.
	fn storage_keys_paged(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
	) -> FutureResult<Vec<StorageKey>>;

	/// Returns a child storage entry at a specific block's state.
	fn storage(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
	) -> FutureResult<Option<StorageData>>;

	/// Returns child storage entries at a specific block's state.
	fn storage_entries(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
	) -> FutureResult<Vec<Option<StorageData>>>;

	/// Returns the hash of a child storage entry at a block's state.
	fn storage_hash(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
	) -> FutureResult<Option<Block::Hash>>;

	/// Returns the size of a child storage entry at a block's state.
	fn storage_size(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
	) -> FutureResult<Option<u64>> {
		self.storage(block, storage_key, key)
			.map(|x| x.map(|r| r.map(|v| v.0.len() as u64)))
			.boxed()
	}
}

/// Child state API with subscriptions support.
pub struct ChildState<Block, Client> {
	backend: Box<dyn ChildStateBackend<Block, Client>>,
}

impl<Block, Client> ChildStateApi<Block::Hash> for ChildState<Block, Client>
where
	Block: BlockT + 'static,
	Client: Send + Sync + 'static,
{
	type Metadata = crate::Metadata;

	fn read_child_proof(
		&self,
		child_storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
		block: Option<Block::Hash>,
	) -> FutureResult<ReadProof<Block::Hash>> {
		self.backend.read_child_proof(block, child_storage_key, keys)
	}

	fn storage(
		&self,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
		block: Option<Block::Hash>,
	) -> FutureResult<Option<StorageData>> {
		self.backend.storage(block, storage_key, key)
	}

	fn storage_entries(
		&self,
		storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
		block: Option<Block::Hash>,
	) -> FutureResult<Vec<Option<StorageData>>> {
		self.backend.storage_entries(block, storage_key, keys)
	}

	fn storage_keys(
		&self,
		storage_key: PrefixedStorageKey,
		key_prefix: StorageKey,
		block: Option<Block::Hash>,
	) -> FutureResult<Vec<StorageKey>> {
		self.backend.storage_keys(block, storage_key, key_prefix)
	}

	fn storage_keys_paged(
		&self,
		storage_key: PrefixedStorageKey,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
		block: Option<Block::Hash>,
	) -> FutureResult<Vec<StorageKey>> {
		self.backend.storage_keys_paged(block, storage_key, prefix, count, start_key)
	}

	fn storage_hash(
		&self,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
		block: Option<Block::Hash>,
	) -> FutureResult<Option<Block::Hash>> {
		self.backend.storage_hash(block, storage_key, key)
	}

	fn storage_size(
		&self,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
		block: Option<Block::Hash>,
	) -> FutureResult<Option<u64>> {
		self.backend.storage_size(block, storage_key, key)
	}
}

fn client_err(err: sp_blockchain::Error) -> Error {
	Error::Client(Box::new(err))
}
