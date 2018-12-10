// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use std::{
	collections::HashMap,
	sync::Arc,
};

use client::{self, Client, CallExecutor, BlockchainEvents, runtime_api::Metadata};
use jsonrpc_macros::Trailing;
use jsonrpc_macros::pubsub;
use jsonrpc_pubsub::SubscriptionId;
use primitives::{H256, Blake2Hasher, Bytes};
use primitives::hexdisplay::HexDisplay;
use primitives::storage::{self, StorageKey, StorageData, StorageChangeSet};
use rpc::Result as RpcResult;
use rpc::futures::{stream, Future, Sink, Stream};
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Header, ProvideRuntimeApi};
use runtime_version::RuntimeVersion;

use subscriptions::Subscriptions;

mod error;
#[cfg(test)]
mod tests;

use self::error::Result;

build_rpc_trait! {
	/// Substrate state API
	pub trait StateApi<Hash> {
		type Metadata;

		/// Call a contract at a block's state.
		#[rpc(name = "state_call", alias = ["state_callAt", ])]
		fn call(&self, String, Bytes, Trailing<Hash>) -> Result<Bytes>;

		/// Returns a storage entry at a specific block's state.
		#[rpc(name = "state_getStorage", alias = ["state_getStorageAt", ])]
		fn storage(&self, StorageKey, Trailing<Hash>) -> Result<Option<StorageData>>;

		/// Returns the hash of a storage entry at a block's state.
		#[rpc(name = "state_getStorageHash", alias = ["state_getStorageHashAt", ])]
		fn storage_hash(&self, StorageKey, Trailing<Hash>) -> Result<Option<Hash>>;

		/// Returns the size of a storage entry at a block's state.
		#[rpc(name = "state_getStorageSize", alias = ["state_getStorageSizeAt", ])]
		fn storage_size(&self, StorageKey, Trailing<Hash>) -> Result<Option<u64>>;

		/// Returns the runtime metadata as an opaque blob.
		#[rpc(name = "state_getMetadata")]
		fn metadata(&self, Trailing<Hash>) -> Result<Bytes>;

		/// Get the runtime version.
		#[rpc(name = "state_getRuntimeVersion", alias = ["chain_getRuntimeVersion", ])]
		fn runtime_version(&self, Trailing<Hash>) -> Result<RuntimeVersion>;

		/// Query historical storage entries (by key) starting from a block given as the second parameter.
		///
		/// NOTE This first returned result contains the initial state of storage for all keys.
		/// Subsequent values in the vector represent changes to the previous state (diffs).
		#[rpc(name = "state_queryStorage")]
		fn query_storage(&self, Vec<StorageKey>, Hash, Trailing<Hash>) -> Result<Vec<StorageChangeSet<Hash>>>;

		#[pubsub(name = "state_runtimeVersion")] {
			/// New runtime version subscription
			#[rpc(name = "state_subscribeRuntimeVersion", alias = ["chain_subscribeRuntimeVersion", ])]
			fn subscribe_runtime_version(&self, Self::Metadata, pubsub::Subscriber<RuntimeVersion>);

			/// Unsubscribe from runtime version subscription
			#[rpc(name = "state_unsubscribeRuntimeVersion", alias = ["chain_unsubscribeRuntimeVersion", ])]
			fn unsubscribe_runtime_version(&self, Self::Metadata, SubscriptionId) -> RpcResult<bool>;
		}

		#[pubsub(name = "state_storage")] {
			/// New storage subscription
			#[rpc(name = "state_subscribeStorage")]
			fn subscribe_storage(&self, Self::Metadata, pubsub::Subscriber<StorageChangeSet<Hash>>, Trailing<Vec<StorageKey>>);

			/// Unsubscribe from storage subscription
			#[rpc(name = "state_unsubscribeStorage")]
			fn unsubscribe_storage(&self, Self::Metadata, SubscriptionId) -> RpcResult<bool>;
		}
	}
}

/// State API with subscriptions support.
pub struct State<B, E, Block: BlockT, RA> {
	/// Substrate client.
	client: Arc<Client<B, E, Block, RA>>,
	/// Current subscriptions.
	subscriptions: Subscriptions,
}

impl<B, E, Block: BlockT, RA> State<B, E, Block, RA> {
	/// Create new State API RPC handler.
	pub fn new(client: Arc<Client<B, E, Block, RA>>, subscriptions: Subscriptions) -> Self {
		Self {
			client,
			subscriptions,
		}
	}
}

impl<B, E, Block, RA> State<B, E, Block, RA> where
	Block: BlockT<Hash=H256>,
	B: client::backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
{
	fn unwrap_or_best(&self, hash: Trailing<Block::Hash>) -> Result<Block::Hash> {
		::helpers::unwrap_or_else(|| Ok(self.client.info()?.chain.best_hash), hash)
	}
}

impl<B, E, Block, RA> StateApi<Block::Hash> for State<B, E, Block, RA> where
	Block: BlockT<Hash=H256> + 'static,
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static + Clone,
	RA: Metadata<Block>
{
	type Metadata = ::metadata::Metadata;

	fn call(&self, method: String, data: Bytes, block: Trailing<Block::Hash>) -> Result<Bytes> {
		let block = self.unwrap_or_best(block)?;
		trace!(target: "rpc", "Calling runtime at {:?} for method {} ({})", block, method, HexDisplay::from(&data.0));
		let return_data = self.client
			.executor()
			.call(
				&BlockId::Hash(block),
				&method, &data.0
			)?
			.return_data;
		Ok(Bytes(return_data))
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

	fn metadata(&self, block: Trailing<Block::Hash>) -> Result<Bytes> {
		let block = self.unwrap_or_best(block)?;
		self.client.runtime_api().metadata(&BlockId::Hash(block)).map(Into::into).map_err(Into::into)
	}

	fn query_storage(&self, keys: Vec<StorageKey>, from: Block::Hash, to: Trailing<Block::Hash>) -> Result<Vec<StorageChangeSet<Block::Hash>>> {
		let to = self.unwrap_or_best(to)?;

		let from_hdr = self.client.header(&BlockId::hash(from))?;
		let to_hdr = self.client.header(&BlockId::hash(to))?;

		match (from_hdr, to_hdr) {
			(Some(ref from), Some(ref to)) if from.number() <= to.number() => {
				let from = from.clone();
				let to = to.clone();
				// check if we can get from `to` to `from` by going through parent_hashes.
				let blocks = {
					let mut blocks = vec![to.hash()];
					let mut last = to.clone();
					while last.number() > from.number() {
						if let Some(hdr) = self.client.header(&BlockId::hash(*last.parent_hash()))? {
							blocks.push(hdr.hash());
							last = hdr;
						} else {
							bail!(invalid_block_range(
								Some(from),
								Some(to),
								format!("Parent of {} ({}) not found", last.number(), last.hash()),
							))
						}
					}
					if last.hash() != from.hash() {
						bail!(invalid_block_range(
							Some(from),
							Some(to),
							format!("Expected to reach `from`, got {} ({})", last.number(), last.hash()),
						))
					}
					blocks.reverse();
					blocks
				};
				let mut result = Vec::new();
				let mut last_state: HashMap<_, Option<_>> = Default::default();
				for block in blocks {
					let mut changes = vec![];
					let id = BlockId::hash(block.clone());

					for key in &keys {
						let (has_changed, data) = {
							let curr_data = self.client.storage(&id, key)?;
							let prev_data = last_state.get(key).and_then(|x| x.as_ref());

							(curr_data.as_ref() != prev_data, curr_data)
						};

						if has_changed {
							changes.push((key.clone(), data.clone()));
						}

						last_state.insert(key.clone(), data);
					}

					result.push(StorageChangeSet {
						block,
						changes,
					});
				}
				Ok(result)
			},
			(from, to) => bail!(invalid_block_range(from, to, "Invalid range or unknown block".into())),
		}
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

	fn unsubscribe_storage(&self, _meta: Self::Metadata, id: SubscriptionId) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}

	fn runtime_version(&self, at: Trailing<Block::Hash>) -> Result<RuntimeVersion> {
		let at = self.unwrap_or_best(at)?;
		Ok(self.client.runtime_version_at(&BlockId::Hash(at))?)
	}

	fn subscribe_runtime_version(&self, _meta: Self::Metadata, subscriber: pubsub::Subscriber<RuntimeVersion>) {
		let stream = match self.client.storage_changes_notification_stream(Some(&[StorageKey(storage::well_known_keys::CODE.to_vec())])) {
			Ok(stream) => stream,
			Err(err) => {
				let _ = subscriber.reject(error::Error::from(err).into());
				return;
			}
		};

		self.subscriptions.add(subscriber, |sink| {
			let version = self.runtime_version(None.into())
				.map_err(Into::into);

			let client = self.client.clone();
			let mut previous_version = version.clone();

			let stream = stream
				.map_err(|e| warn!("Error creating storage notification stream: {:?}", e))
				.filter_map(move |_| {
					let version = client.info().and_then(|info| {
							client.runtime_version_at(&BlockId::hash(info.chain.best_hash))
						})
						.map_err(error::Error::from)
						.map_err(Into::into);
					if previous_version != version {
						previous_version = version.clone();
						Some(version)
					} else {
						None
					}
				});

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

	fn unsubscribe_runtime_version(&self, _meta: Self::Metadata, id: SubscriptionId) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}
}

fn invalid_block_range<H: Header>(from: Option<H>, to: Option<H>, reason: String) -> error::ErrorKind {
	let to_string = |x: Option<H>| match x {
		None => "unknown hash".into(),
		Some(h) => format!("{} ({})", h.number(), h.hash()),
	};

	error::ErrorKind::InvalidBlockRange(to_string(from), to_string(to), reason)
}
