// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use futures03::{future, StreamExt as _, TryStreamExt as _};
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId};
use log::warn;
use rpc::{
	Result as RpcResult,
	futures::{stream, Future, Sink, Stream},
};

use api::Subscriptions;
use client::{
	BlockchainEvents, Client, CallExecutor,
	runtime_api::Metadata,
	light::{blockchain::RemoteBlockchain, fetcher::Fetcher},
};
use primitives::{
	Blake2Hasher, Bytes, H256,
	storage::{well_known_keys, StorageKey, StorageData, StorageChangeSet},
};
use runtime_version::RuntimeVersion;
use sr_primitives::{
	generic::BlockId,
	traits::{Block as BlockT, ProvideRuntimeApi},
};

use self::error::{Error, FutureResult};

pub use api::state::*;

/// State backend API.
pub trait StateBackend<B, E, Block: BlockT, RA>: Send + Sync + 'static
	where
		Block: BlockT<Hash=H256> + 'static,
		B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
		E: client::CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
		RA: Send + Sync + 'static,
{
	/// Get client reference.
	fn client(&self) -> &Arc<Client<B, E, Block, RA>>;

	/// Get subscriptions reference.
	fn subscriptions(&self) -> &Subscriptions;

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

	/// Returns the keys with prefix from a child storage, leave empty to get all the keys
	fn child_storage_keys(
		&self,
		block: Option<Block::Hash>,
		child_storage_key: StorageKey,
		prefix: StorageKey,
	) -> FutureResult<Vec<StorageKey>>;

	/// Returns a child storage entry at a specific block's state.
	fn child_storage(
		&self,
		block: Option<Block::Hash>,
		child_storage_key: StorageKey,
		key: StorageKey,
	) -> FutureResult<Option<StorageData>>;

	/// Returns the hash of a child storage entry at a block's state.
	fn child_storage_hash(
		&self,
		block: Option<Block::Hash>,
		child_storage_key: StorageKey,
		key: StorageKey,
	) -> FutureResult<Option<Block::Hash>>;

	/// Returns the size of a child storage entry at a block's state.
	fn child_storage_size(
		&self,
		block: Option<Block::Hash>,
		child_storage_key: StorageKey,
		key: StorageKey,
	) -> FutureResult<Option<u64>> {
		Box::new(self.child_storage(block, child_storage_key, key)
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

	/// New runtime version subscription
	fn subscribe_runtime_version(
		&self,
		_meta: crate::metadata::Metadata,
		subscriber: Subscriber<RuntimeVersion>,
	) {
		let stream = match self.client().storage_changes_notification_stream(
			Some(&[StorageKey(well_known_keys::CODE.to_vec())]),
			None,
		) {
			Ok(stream) => stream,
			Err(err) => {
				let _ = subscriber.reject(Error::from(client_err(err)).into());
				return;
			}
		};

		self.subscriptions().add(subscriber, |sink| {
			let version = self.runtime_version(None.into())
				.map_err(Into::into)
				.wait();

			let client = self.client().clone();
			let mut previous_version = version.clone();

			let stream = stream
				.filter_map(move |_| {
					let info = client.info();
					let version = client
						.runtime_version_at(&BlockId::hash(info.chain.best_hash))
						.map_err(client_err)
						.map_err(Into::into);
					if previous_version != version {
						previous_version = version.clone();
						future::ready(Some(Ok::<_, ()>(version)))
					} else {
						future::ready(None)
					}
				})
				.compat();

			sink
				.sink_map_err(|e| warn!("Error sending notifications: {:?}", e))
				.send_all(
					stream::iter_result(vec![Ok(version)])
					.chain(stream)
				)
				// we ignore the resulting Stream (if the first stream is over we are unsubscribed)
				.map(|_| ())
		});
	}

	/// Unsubscribe from runtime version subscription
	fn unsubscribe_runtime_version(
		&self,
		_meta: Option<crate::metadata::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		Ok(self.subscriptions().cancel(id))
	}

	/// New storage subscription
	fn subscribe_storage(
		&self,
		_meta: crate::metadata::Metadata,
		subscriber: Subscriber<StorageChangeSet<Block::Hash>>,
		keys: Option<Vec<StorageKey>>
	) {
		let keys = Into::<Option<Vec<_>>>::into(keys);
		let stream = match self.client().storage_changes_notification_stream(
			keys.as_ref().map(|x| &**x),
			None
		) {
			Ok(stream) => stream,
			Err(err) => {
				let _ = subscriber.reject(client_err(err).into());
				return;
			},
		};

		// initial values
		let initial = stream::iter_result(keys
			.map(|keys| {
				let block = self.client().info().chain.best_hash;
				let changes = keys
					.into_iter()
					.map(|key| self.storage(Some(block.clone()).into(), key.clone())
						.map(|val| (key.clone(), val))
						.wait()
						.unwrap_or_else(|_| (key, None))
					)
					.collect();
				vec![Ok(Ok(StorageChangeSet { block, changes }))]
			}).unwrap_or_default());

		self.subscriptions().add(subscriber, |sink| {
			let stream = stream
				.map(|(block, changes)| Ok::<_, ()>(Ok(StorageChangeSet {
					block,
					changes: changes.iter()
						.filter_map(|(o_sk, k, v)| if o_sk.is_none() {
							Some((k.clone(),v.cloned()))
						} else { None }).collect(),
				})))
				.compat();

			sink
				.sink_map_err(|e| warn!("Error sending notifications: {:?}", e))
				.send_all(initial.chain(stream))
				// we ignore the resulting Stream (if the first stream is over we are unsubscribed)
				.map(|_| ())
		})
	}

	/// Unsubscribe from storage subscription
	fn unsubscribe_storage(
		&self,
		_meta: Option<crate::metadata::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		Ok(self.subscriptions().cancel(id))
	}
}

/// Create new state API that works on full node.
pub fn new_full<B, E, Block: BlockT, RA>(
	client: Arc<Client<B, E, Block, RA>>,
	subscriptions: Subscriptions,
) -> State<B, E, Block, RA>
	where
		Block: BlockT<Hash=H256> + 'static,
		B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static + Clone,
		RA: Send + Sync + 'static,
		Client<B, E, Block, RA>: ProvideRuntimeApi,
		<Client<B, E, Block, RA> as ProvideRuntimeApi>::Api: Metadata<Block>,
{
	State {
		backend: Box::new(self::state_full::FullState::new(client, subscriptions)),
	}
}

/// Create new state API that works on light node.
pub fn new_light<B, E, Block: BlockT, RA, F: Fetcher<Block>>(
	client: Arc<Client<B, E, Block, RA>>,
	subscriptions: Subscriptions,
	remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
	fetcher: Arc<F>,
) -> State<B, E, Block, RA>
	where
		Block: BlockT<Hash=H256> + 'static,
		B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static + Clone,
		RA: Send + Sync + 'static,
		F: Send + Sync + 'static,
{
	State {
		backend: Box::new(self::state_light::LightState::new(
			client,
			subscriptions,
			remote_blockchain,
			fetcher,
		)),
	}
}

/// State API with subscriptions support.
pub struct State<B, E, Block, RA> {
	backend: Box<dyn StateBackend<B, E, Block, RA>>,
}

impl<B, E, Block, RA> StateApi<Block::Hash> for State<B, E, Block, RA>
	where
		Block: BlockT<Hash=H256> + 'static,
		B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static + Clone,
		RA: Send + Sync + 'static,
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

	fn storage(&self, key: StorageKey, block: Option<Block::Hash>) -> FutureResult<Option<StorageData>> {
		self.backend.storage(block, key)
	}

	fn storage_hash(&self, key: StorageKey, block: Option<Block::Hash>) -> FutureResult<Option<Block::Hash>> {
		self.backend.storage_hash(block, key)
	}

	fn storage_size(&self, key: StorageKey, block: Option<Block::Hash>) -> FutureResult<Option<u64>> {
		self.backend.storage_size(block, key)
	}

	fn child_storage(
		&self,
		child_storage_key: StorageKey,
		key: StorageKey,
		block: Option<Block::Hash>
	) -> FutureResult<Option<StorageData>> {
		self.backend.child_storage(block, child_storage_key, key)
	}

	fn child_storage_keys(
		&self,
		child_storage_key: StorageKey,
		key_prefix: StorageKey,
		block: Option<Block::Hash>
	) -> FutureResult<Vec<StorageKey>> {
		self.backend.child_storage_keys(block, child_storage_key, key_prefix)
	}

	fn child_storage_hash(
		&self,
		child_storage_key: StorageKey,
		key: StorageKey,
		block: Option<Block::Hash>
	) -> FutureResult<Option<Block::Hash>> {
		self.backend.child_storage_hash(block, child_storage_key, key)
	}

	fn child_storage_size(
		&self,
		child_storage_key: StorageKey,
		key: StorageKey,
		block: Option<Block::Hash>
	) -> FutureResult<Option<u64>> {
		self.backend.child_storage_size(block, child_storage_key, key)
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

fn client_err(err: client::error::Error) -> Error {
	Error::Client(Box::new(err))
}
