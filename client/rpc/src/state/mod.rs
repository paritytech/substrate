// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Substrate state API.

mod state_full;
mod state_light;

#[cfg(test)]
mod tests;

use std::sync::Arc;
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId};
use rpc::{Result as RpcResult, futures::{Future, future::result}};

use sc_rpc_api::{Subscriptions, state::ReadProof};
use sc_client_api::light::{RemoteBlockchain, Fetcher};
use sp_core::{Bytes, storage::{StorageKey, PrefixedStorageKey, StorageData, StorageChangeSet}};
use sp_version::RuntimeVersion;
use sp_runtime::traits::Block as BlockT;

use sp_api::{Metadata, ProvideRuntimeApi, CallApiAt};

use self::error::{Error, FutureResult};

pub use sc_rpc_api::state::*;
pub use sc_rpc_api::child_state::*;
use sc_client_api::{ExecutorProvider, StorageProvider, BlockchainEvents, Backend, ProofProvider};
use sp_blockchain::{HeaderMetadata, HeaderBackend};

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
	fn storage_size(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<u64>> {
		Box::new(self.storage(block, key)
			.map(|x| x.map(|x| x.0.len() as u64)))
	}

	/// Returns the runtime metadata as an opaque blob.
	fn metadata(&self, block: Option<Block::Hash>) -> FutureResult<Bytes>;

	/// Get the runtime version.
	fn runtime_version(&self, block: Option<Block::Hash>) -> FutureResult<RuntimeVersion>;

	/// Query historical storage entries (by key) starting from a block given as the second parameter.
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
		at: Option<Block::Hash>
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
		_meta: crate::metadata::Metadata,
		subscriber: Subscriber<RuntimeVersion>,
	);

	/// Unsubscribe from runtime version subscription
	fn unsubscribe_runtime_version(
		&self,
		_meta: Option<crate::metadata::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool>;

	/// New storage subscription
	fn subscribe_storage(
		&self,
		_meta: crate::metadata::Metadata,
		subscriber: Subscriber<StorageChangeSet<Block::Hash>>,
		keys: Option<Vec<StorageKey>>,
	);

	/// Unsubscribe from storage subscription
	fn unsubscribe_storage(
		&self,
		_meta: Option<crate::metadata::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool>;
}

/// Create new state API that works on full node.
pub fn new_full<BE, Block: BlockT, Client>(
	client: Arc<Client>,
	subscriptions: Subscriptions,
) -> (State<Block, Client>, ChildState<Block, Client>)
	where
		Block: BlockT + 'static,
		BE: Backend<Block> + 'static,
		Client: ExecutorProvider<Block> + StorageProvider<Block, BE> + ProofProvider<Block> + HeaderBackend<Block>
			+ HeaderMetadata<Block, Error = sp_blockchain::Error> + BlockchainEvents<Block>
			+ CallApiAt<Block, Error = sp_blockchain::Error>
			+ ProvideRuntimeApi<Block> + Send + Sync + 'static,
		Client::Api: Metadata<Block, Error = sp_blockchain::Error>,
{
	let child_backend = Box::new(
		self::state_full::FullState::new(client.clone(), subscriptions.clone())
	);
	let backend = Box::new(self::state_full::FullState::new(client, subscriptions));
	(State { backend }, ChildState { backend: child_backend })
}

/// Create new state API that works on light node.
pub fn new_light<BE, Block: BlockT, Client, F: Fetcher<Block>>(
	client: Arc<Client>,
	subscriptions: Subscriptions,
	remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
	fetcher: Arc<F>,
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
			subscriptions.clone(),
			remote_blockchain.clone(),
			fetcher.clone(),
	));

	let backend = Box::new(self::state_light::LightState::new(
			client,
			subscriptions,
			remote_blockchain,
			fetcher,
	));
	(State { backend }, ChildState { backend: child_backend })
}

/// State API with subscriptions support.
pub struct State<Block, Client> {
	backend: Box<dyn StateBackend<Block, Client>>,
}

impl<Block, Client> StateApi<Block::Hash> for State<Block, Client>
	where
		Block: BlockT + 'static,
		Client: Send + Sync + 'static,
{
	type Metadata = crate::metadata::Metadata;

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
			return Box::new(result(Err(
				Error::InvalidCount {
					value: count,
					max: STORAGE_KEYS_PAGED_MAX_COUNT,
				}
			)));
		}
		self.backend.storage_keys_paged(block, prefix, count, start_key)
	}

	fn storage(&self, key: StorageKey, block: Option<Block::Hash>) -> FutureResult<Option<StorageData>> {
		self.backend.storage(block, key)
	}

	fn storage_hash(&self, key: StorageKey, block: Option<Block::Hash>) -> FutureResult<Option<Block::Hash>> {
		self.backend.storage_hash(block, key)
	}

	fn storage_size(&self, key: StorageKey, block: Option<Block::Hash>) -> FutureResult<Option<u64>> {
		self.backend.storage_size(block, key)
	}

	fn metadata(&self, block: Option<Block::Hash>) -> FutureResult<Bytes> {
		self.backend.metadata(block)
	}

	fn query_storage(
		&self,
		keys: Vec<StorageKey>,
		from: Block::Hash,
		to: Option<Block::Hash>
	) -> FutureResult<Vec<StorageChangeSet<Block::Hash>>> {
		self.backend.query_storage(from, to, keys)
	}

	fn query_storage_at(
		&self,
		keys: Vec<StorageKey>,
		at: Option<Block::Hash>
	) -> FutureResult<Vec<StorageChangeSet<Block::Hash>>> {
		self.backend.query_storage_at(keys, at)
	}

	fn read_proof(&self, keys: Vec<StorageKey>, block: Option<Block::Hash>) -> FutureResult<ReadProof<Block::Hash>> {
		self.backend.read_proof(block, keys)
	}

	fn subscribe_storage(
		&self,
		meta: Self::Metadata,
		subscriber: Subscriber<StorageChangeSet<Block::Hash>>,
		keys: Option<Vec<StorageKey>>
	) {
		self.backend.subscribe_storage(meta, subscriber, keys);
	}

	fn unsubscribe_storage(&self, meta: Option<Self::Metadata>, id: SubscriptionId) -> RpcResult<bool> {
		self.backend.unsubscribe_storage(meta, id)
	}

	fn runtime_version(&self, at: Option<Block::Hash>) -> FutureResult<RuntimeVersion> {
		self.backend.runtime_version(at)
	}

	fn subscribe_runtime_version(&self, meta: Self::Metadata, subscriber: Subscriber<RuntimeVersion>) {
		self.backend.subscribe_runtime_version(meta, subscriber);
	}

	fn unsubscribe_runtime_version(
		&self,
		meta: Option<Self::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		self.backend.unsubscribe_runtime_version(meta, id)
	}
}

/// Child state backend API.
pub trait ChildStateBackend<Block: BlockT, Client>: Send + Sync + 'static
	where
		Block: BlockT + 'static,
		Client: Send + Sync + 'static,
{
	/// Returns the keys with prefix from a child storage,
	/// leave prefix empty to get all the keys.
	fn storage_keys(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		prefix: StorageKey,
	) -> FutureResult<Vec<StorageKey>>;

	/// Returns a child storage entry at a specific block's state.
	fn storage(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
	) -> FutureResult<Option<StorageData>>;

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
		Box::new(self.storage(block, storage_key, key)
			.map(|x| x.map(|x| x.0.len() as u64)))
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
	type Metadata = crate::metadata::Metadata;

	fn storage(
		&self,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
		block: Option<Block::Hash>
	) -> FutureResult<Option<StorageData>> {
		self.backend.storage(block, storage_key, key)
	}

	fn storage_keys(
		&self,
		storage_key: PrefixedStorageKey,
		key_prefix: StorageKey,
		block: Option<Block::Hash>
	) -> FutureResult<Vec<StorageKey>> {
		self.backend.storage_keys(block, storage_key, key_prefix)
	}

	fn storage_hash(
		&self,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
		block: Option<Block::Hash>
	) -> FutureResult<Option<Block::Hash>> {
		self.backend.storage_hash(block, storage_key, key)
	}

	fn storage_size(
		&self,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
		block: Option<Block::Hash>
	) -> FutureResult<Option<u64>> {
		self.backend.storage_size(block, storage_key, key)
	}
}

fn client_err(err: sp_blockchain::Error) -> Error {
	Error::Client(Box::new(err))
}
