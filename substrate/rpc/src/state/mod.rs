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
use rpc::futures::{stream, Future, Sink, Stream};
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

		/// Call a contract at a block's state.
		#[rpc(name = "state_call", alias = ["state_callAt", ])]
		fn call(&self, String, Vec<u8>, Trailing<Hash>) -> Result<Vec<u8>>;

		/// Returns a storage entry at a specific block's state.
		#[rpc(name = "state_getStorage", alias = ["state_getStorageAt", ])]
		fn storage(&self, StorageKey, Trailing<Hash>) -> Result<Option<StorageData>>;

		/// Returns the hash of a storage entry at a block's state.
		#[rpc(name = "state_getStorageHash", alias = ["state_getStorageHashAt", ])]
		fn storage_hash(&self, StorageKey, Trailing<Hash>) -> Result<Option<Hash>>;

		/// Returns the size of a storage entry at a block's state.
		#[rpc(name = "state_getStorageSize", alias = ["state_getStorageSizeAt", ])]
		fn storage_size(&self, StorageKey, Trailing<Hash>) -> Result<Option<u64>>;

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

impl<B, E, Block> State<B, E, Block> where
	Block: BlockT + 'static,
	B: client::backend::Backend<Block> + Send + Sync + 'static,
	E: CallExecutor<Block> + Send + Sync + 'static,
{
	fn unwrap_or_best(&self, hash: Trailing<Block::Hash>) -> Result<Block::Hash> {
		Ok(match hash.into() {
			None => self.client.info()?.chain.best_hash,
			Some(hash) => hash,
		})
	}
}

impl<B, E, Block> StateApi<Block::Hash> for State<B, E, Block> where
	Block: BlockT + 'static,
	B: client::backend::Backend<Block> + Send + Sync + 'static,
	E: CallExecutor<Block> + Send + Sync + 'static,
{
	type Metadata = ::metadata::Metadata;

	fn call(&self, method: String, data: Vec<u8>, block: Trailing<Block::Hash>) -> Result<Vec<u8>> {
		let block = self.unwrap_or_best(block)?;
		trace!(target: "rpc", "Calling runtime at {:?} for method {} ({})", block, method, HexDisplay::from(&data));
		Ok(self.client.executor().call(&BlockId::Hash(block), &method, &data)?.return_data)
	}

	fn storage(&self, key: StorageKey, block: Trailing<Block::Hash>) -> Result<Option<StorageData>> {
		let block = self.unwrap_or_best(block)?;
		trace!(target: "rpc", "Querying storage at {:?} for key {}", block, HexDisplay::from(&key.0));
		Ok(self.client.storage(&BlockId::Hash(block), &key)?)
	}

	fn storage_hash(&self, key: StorageKey, block: Trailing<Block::Hash>) -> Result<Option<Block::Hash>> {
		use runtime_primitives::traits::{Hash, Header as HeaderT};
		Ok(self.storage(key, block)?.map(|x| <Block::Header as HeaderT>::Hashing::hash(&x.0)))
	}

	fn storage_size(&self, key: StorageKey, block: Trailing<Block::Hash>) -> Result<Option<u64>> {
		Ok(self.storage(key, block)?.map(|x| x.0.len() as u64))
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

		// initial values
		let initial = stream::iter_result(keys
			.map(|keys| {
				let block = self.client.info().map(|info| info.chain.best_hash).unwrap_or_default();
				let changes = keys
					.into_iter()
					.map(|key| self.storage(key.clone(), Some(block.clone()).into())
						.map(|val| (key.clone(), val))
						.unwrap_or_else(|_| (key, None))
					)
					.collect();
				vec![Ok(Ok(StorageChangeSet { block, changes }))]
			}).unwrap_or_default());

		self.subscriptions.add(subscriber, |sink| {
			let stream = stream
				.map_err(|e| warn!("Error creating storage notification stream: {:?}", e))
				.map(|(block, changes)| Ok(StorageChangeSet {
					block,
					changes: changes.iter().cloned().collect(),
				}));

			sink
				.sink_map_err(|e| warn!("Error sending notifications: {:?}", e))
				.send_all(initial.chain(stream))
				// we ignore the resulting Stream (if the first stream is over we are unsubscribed)
				.map(|_| ())
		})
	}

	fn unsubscribe_storage(&self, id: SubscriptionId) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}
}
