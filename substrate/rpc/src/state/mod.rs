// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Polkadot state API.

use std::sync::Arc;

use client::{self, Client, CallExecutor, BlockchainEvents};
use jsonrpc_macros::Trailing;
use jsonrpc_macros::pubsub;
use jsonrpc_pubsub::SubscriptionId;
use primitives::hexdisplay::HexDisplay;
use primitives::storage::{StorageKey, StorageData, StorageChangeSet};
use rpc::Result as RpcResult;
use rpc::futures::{Future, Sink, Stream};
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::Block as BlockT;
use tokio::runtime::TaskExecutor;

use subscriptions::Subscriptions;

mod error;
#[cfg(test)]
mod tests;

use self::error::Result;

build_rpc_trait! {
	/// Polkadot state API
	pub trait StateApi<Hash> {
		type Metadata;

		/// Returns a storage entry at a specific block's state.
		#[rpc(name = "state_getStorageAt")]
		fn storage_at(&self, StorageKey, Hash) -> Result<StorageData>;

		/// Call a contract at a block's state.
		#[rpc(name = "state_callAt")]
		fn call_at(&self, String, Vec<u8>, Hash) -> Result<Vec<u8>>;

		/// Returns the hash of a storage entry at a block's state.
		#[rpc(name = "state_getStorageHashAt")]
		fn storage_hash_at(&self, StorageKey, Hash) -> Result<Hash>;

		/// Returns the size of a storage entry at a block's state.
		#[rpc(name = "state_getStorageSizeAt")]
		fn storage_size_at(&self, StorageKey, Hash) -> Result<u64>;

		/// Returns the hash of a storage entry at the best block.
		#[rpc(name = "state_getStorageHash")]
		fn storage_hash(&self, StorageKey) -> Result<Hash>;

		/// Returns the size of a storage entry at the best block.
		#[rpc(name = "state_getStorageSize")]
		fn storage_size(&self, StorageKey) -> Result<u64>;

		/// Returns a storage entry at the best block.
		#[rpc(name = "state_getStorage")]
		fn storage(&self, StorageKey) -> Result<StorageData>;

		/// Call a contract at the best block.
		#[rpc(name = "state_call")]
		fn call(&self, String, Vec<u8>) -> Result<Vec<u8>>;

		#[pubsub(name = "state_storage")] {
			/// New storage subscription
			#[rpc(name = "state_subscribeStorage")]
			fn subscribe_storage(&self, Self::Metadata, pubsub::Subscriber<StorageChangeSet<Hash>>, Trailing<Vec<StorageKey>>);

			/// Unsubscribe from storage subscription
			#[rpc(name = "state_unsubscribeStorage")]
			fn unsubscribe_storage(&self, SubscriptionId) -> RpcResult<bool>;
		}
	}
}

/// State API with subscriptions support.
pub struct State<B, E, Block: BlockT> {
	/// Substrate client.
	client: Arc<Client<B, E, Block>>,
	/// Current subscriptions.
	subscriptions: Subscriptions,
}

impl<B, E, Block: BlockT> State<B, E, Block> {
	/// Create new State API RPC handler.
	pub fn new(client: Arc<Client<B, E, Block>>, executor: TaskExecutor) -> Self {
		Self {
			client,
			subscriptions: Subscriptions::new(executor),
		}
	}
}

impl<B, E, Block> StateApi<Block::Hash> for State<B, E, Block> where
	Block: BlockT + 'static,
	B: client::backend::Backend<Block> + Send + Sync + 'static,
	E: CallExecutor<Block> + Send + Sync + 'static,
{
	type Metadata = ::metadata::Metadata;

	fn storage_at(&self, key: StorageKey, block: Block::Hash) -> Result<StorageData> {
		trace!(target: "rpc", "Querying storage at {:?} for key {}", block, HexDisplay::from(&key.0));
		Ok(self.client.storage(&BlockId::Hash(block), &key)?)
	}

	fn call_at(&self, method: String, data: Vec<u8>, block: Block::Hash) -> Result<Vec<u8>> {
		trace!(target: "rpc", "Calling runtime at {:?} for method {} ({})", block, method, HexDisplay::from(&data));
		Ok(self.client.executor().call(&BlockId::Hash(block), &method, &data)?.return_data)
	}

	fn storage_hash_at(&self, key: StorageKey, block: Block::Hash) -> Result<Block::Hash> {
		use runtime_primitives::traits::{Hash, Header as HeaderT};
		self.storage_at(key, block).map(|x| <Block::Header as HeaderT>::Hashing::hash(&x.0))
	}

	fn storage_size_at(&self, key: StorageKey, block: Block::Hash) -> Result<u64> {
		self.storage_at(key, block).map(|x| x.0.len() as u64)
	}

	fn storage_hash(&self, key: StorageKey) -> Result<Block::Hash> {
		self.storage_hash_at(key, self.client.info()?.chain.best_hash)
	}

	fn storage_size(&self, key: StorageKey) -> Result<u64> {
		self.storage_size_at(key, self.client.info()?.chain.best_hash)
	}

	fn storage(&self, key: StorageKey) -> Result<StorageData> {
		self.storage_at(key, self.client.info()?.chain.best_hash)
	}

	fn call(&self, method: String, data: Vec<u8>) -> Result<Vec<u8>> {
		self.call_at(method, data, self.client.info()?.chain.best_hash)
	}

	fn subscribe_storage(
		&self,
		_meta: Self::Metadata,
		subscriber: pubsub::Subscriber<StorageChangeSet<Block::Hash>>,
		keys: Trailing<Vec<StorageKey>>
	) {
		let keys = Into::<Option<Vec<_>>>::into(keys);
		let stream = match self.client.storage_changes_notification_stream(keys.as_ref().map(|x| &**x)) {
			Ok(stream) => stream,
			Err(err) => {
				let _ = subscriber.reject(error::Error::from(err).into());
				return;
			},
		};

		self.subscriptions.add(subscriber, |sink| {
			let stream = stream
				.map_err(|e| warn!("Error creating storage notification stream: {:?}", e))
				.map(|(block, changes)| Ok(StorageChangeSet {
					block,
					changes: changes.iter().cloned().collect(),
				}));
			sink
				.sink_map_err(|e| warn!("Error sending notifications: {:?}", e))
				.send_all(stream)
				// we ignore the resulting Stream (if the first stream is over we are unsubscribed)
				.map(|_| ())
		})
	}

	fn unsubscribe_storage(&self, id: SubscriptionId) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}
}
