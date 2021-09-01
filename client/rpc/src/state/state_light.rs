// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! State API backend for light nodes.

use codec::Decode;
use futures::{
	channel::oneshot::{channel, Sender},
	future::{ready, Either},
	Future, FutureExt, SinkExt, Stream, StreamExt as _, TryFutureExt, TryStreamExt as _,
};
use hash_db::Hasher;
use jsonrpc_pubsub::{manager::SubscriptionManager, typed::Subscriber, SubscriptionId};
use log::warn;
use parking_lot::Mutex;
use rpc::Result as RpcResult;
use std::{
	collections::{hash_map::Entry, HashMap, HashSet},
	sync::Arc,
};

use sc_client_api::{
	light::{
		future_header, Fetcher, RemoteBlockchain, RemoteCallRequest, RemoteReadChildRequest,
		RemoteReadRequest,
	},
	BlockchainEvents,
};
use sc_rpc_api::state::ReadProof;
use sp_blockchain::{Error as ClientError, HeaderBackend};
use sp_core::{
	storage::{PrefixedStorageKey, StorageChangeSet, StorageData, StorageKey},
	Bytes, OpaqueMetadata,
};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, HashFor},
};
use sp_version::RuntimeVersion;

use super::{
	client_err,
	error::{Error, FutureResult},
	ChildStateBackend, StateBackend,
};

/// Storage data map of storage keys => (optional) storage value.
type StorageMap = HashMap<StorageKey, Option<StorageData>>;

/// State API backend for light nodes.
#[derive(Clone)]
pub struct LightState<Block: BlockT, F: Fetcher<Block>, Client> {
	client: Arc<Client>,
	subscriptions: SubscriptionManager,
	version_subscriptions: SimpleSubscriptions<Block::Hash, RuntimeVersion>,
	storage_subscriptions: Arc<Mutex<StorageSubscriptions<Block>>>,
	remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
	fetcher: Arc<F>,
}

/// Shared requests container.
trait SharedRequests<Hash, V>: Clone + Send + Sync {
	/// Tries to listen for already issued request, or issues request.
	///
	/// Returns true if requests has been issued.
	fn listen_request(&self, block: Hash, sender: Sender<Result<V, ()>>) -> bool;

	/// Returns (and forgets) all listeners for given request.
	fn on_response_received(&self, block: Hash) -> Vec<Sender<Result<V, ()>>>;
}

/// Storage subscriptions data.
struct StorageSubscriptions<Block: BlockT> {
	/// Active storage requests.
	active_requests: HashMap<Block::Hash, Vec<Sender<Result<StorageMap, ()>>>>,
	/// Map of subscription => keys that this subscription watch for.
	keys_by_subscription: HashMap<SubscriptionId, HashSet<StorageKey>>,
	/// Map of key => set of subscriptions that watch this key.
	subscriptions_by_key: HashMap<StorageKey, HashSet<SubscriptionId>>,
}

impl<Block: BlockT> SharedRequests<Block::Hash, StorageMap>
	for Arc<Mutex<StorageSubscriptions<Block>>>
{
	fn listen_request(&self, block: Block::Hash, sender: Sender<Result<StorageMap, ()>>) -> bool {
		let mut subscriptions = self.lock();
		let active_requests_at = subscriptions.active_requests.entry(block).or_default();
		active_requests_at.push(sender);
		active_requests_at.len() == 1
	}

	fn on_response_received(&self, block: Block::Hash) -> Vec<Sender<Result<StorageMap, ()>>> {
		self.lock().active_requests.remove(&block).unwrap_or_default()
	}
}

/// Simple, maybe shared, subscription data that shares per block requests.
type SimpleSubscriptions<Hash, V> = Arc<Mutex<HashMap<Hash, Vec<Sender<Result<V, ()>>>>>>;

impl<Hash, V> SharedRequests<Hash, V> for SimpleSubscriptions<Hash, V>
where
	Hash: Send + Eq + std::hash::Hash,
	V: Send,
{
	fn listen_request(&self, block: Hash, sender: Sender<Result<V, ()>>) -> bool {
		let mut subscriptions = self.lock();
		let active_requests_at = subscriptions.entry(block).or_default();
		active_requests_at.push(sender);
		active_requests_at.len() == 1
	}

	fn on_response_received(&self, block: Hash) -> Vec<Sender<Result<V, ()>>> {
		self.lock().remove(&block).unwrap_or_default()
	}
}

impl<Block: BlockT, F: Fetcher<Block> + 'static, Client> LightState<Block, F, Client>
where
	Block: BlockT,
	Client: HeaderBackend<Block> + Send + Sync + 'static,
{
	/// Create new state API backend for light nodes.
	pub fn new(
		client: Arc<Client>,
		subscriptions: SubscriptionManager,
		remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
		fetcher: Arc<F>,
	) -> Self {
		Self {
			client,
			subscriptions,
			version_subscriptions: Arc::new(Mutex::new(HashMap::new())),
			storage_subscriptions: Arc::new(Mutex::new(StorageSubscriptions {
				active_requests: HashMap::new(),
				keys_by_subscription: HashMap::new(),
				subscriptions_by_key: HashMap::new(),
			})),
			remote_blockchain,
			fetcher,
		}
	}

	/// Returns given block hash or best block hash if None is passed.
	fn block_or_best(&self, hash: Option<Block::Hash>) -> Block::Hash {
		hash.unwrap_or_else(|| self.client.info().best_hash)
	}
}

impl<Block, F, Client> StateBackend<Block, Client> for LightState<Block, F, Client>
where
	Block: BlockT,
	Block::Hash: Unpin,
	Client: BlockchainEvents<Block> + HeaderBackend<Block> + Send + Sync + 'static,
	F: Fetcher<Block> + 'static,
{
	fn call(
		&self,
		block: Option<Block::Hash>,
		method: String,
		call_data: Bytes,
	) -> FutureResult<Bytes> {
		call(
			&*self.remote_blockchain,
			self.fetcher.clone(),
			self.block_or_best(block),
			method,
			call_data,
		)
		.boxed()
	}

	fn storage_keys(
		&self,
		_block: Option<Block::Hash>,
		_prefix: StorageKey,
	) -> FutureResult<Vec<StorageKey>> {
		async move { Err(client_err(ClientError::NotAvailableOnLightClient)) }.boxed()
	}

	fn storage_pairs(
		&self,
		_block: Option<Block::Hash>,
		_prefix: StorageKey,
	) -> FutureResult<Vec<(StorageKey, StorageData)>> {
		async move { Err(client_err(ClientError::NotAvailableOnLightClient)) }.boxed()
	}

	fn storage_keys_paged(
		&self,
		_block: Option<Block::Hash>,
		_prefix: Option<StorageKey>,
		_count: u32,
		_start_key: Option<StorageKey>,
	) -> FutureResult<Vec<StorageKey>> {
		async move { Err(client_err(ClientError::NotAvailableOnLightClient)) }.boxed()
	}

	fn storage_size(&self, _: Option<Block::Hash>, _: StorageKey) -> FutureResult<Option<u64>> {
		async move { Err(client_err(ClientError::NotAvailableOnLightClient)) }.boxed()
	}

	fn storage(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<StorageData>> {
		storage(
			&*self.remote_blockchain,
			self.fetcher.clone(),
			self.block_or_best(block),
			vec![key.0.clone()],
		)
		.map_ok(move |mut values| {
			values
				.remove(&key)
				.expect("successful request has entries for all requested keys; qed")
		})
		.boxed()
	}

	fn storage_hash(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<Block::Hash>> {
		let res = StateBackend::storage(self, block, key);
		async move { res.await.map(|r| r.map(|s| HashFor::<Block>::hash(&s.0))) }.boxed()
	}

	fn metadata(&self, block: Option<Block::Hash>) -> FutureResult<Bytes> {
		self.call(block, "Metadata_metadata".into(), Bytes(Vec::new()))
			.and_then(|metadata| async move {
				OpaqueMetadata::decode(&mut &metadata.0[..])
					.map(Into::into)
					.map_err(|decode_err| {
						client_err(ClientError::CallResultDecode(
							"Unable to decode metadata",
							decode_err,
						))
					})
			})
			.boxed()
	}

	fn runtime_version(&self, block: Option<Block::Hash>) -> FutureResult<RuntimeVersion> {
		runtime_version(&*self.remote_blockchain, self.fetcher.clone(), self.block_or_best(block))
			.boxed()
	}

	fn query_storage(
		&self,
		_from: Block::Hash,
		_to: Option<Block::Hash>,
		_keys: Vec<StorageKey>,
	) -> FutureResult<Vec<StorageChangeSet<Block::Hash>>> {
		async move { Err(client_err(ClientError::NotAvailableOnLightClient)) }.boxed()
	}

	fn query_storage_at(
		&self,
		_keys: Vec<StorageKey>,
		_at: Option<Block::Hash>,
	) -> FutureResult<Vec<StorageChangeSet<Block::Hash>>> {
		async move { Err(client_err(ClientError::NotAvailableOnLightClient)) }.boxed()
	}

	fn read_proof(
		&self,
		_block: Option<Block::Hash>,
		_keys: Vec<StorageKey>,
	) -> FutureResult<ReadProof<Block::Hash>> {
		async move { Err(client_err(ClientError::NotAvailableOnLightClient)) }.boxed()
	}

	fn subscribe_storage(
		&self,
		_meta: crate::Metadata,
		subscriber: Subscriber<StorageChangeSet<Block::Hash>>,
		keys: Option<Vec<StorageKey>>,
	) {
		let keys = match keys {
			Some(keys) if !keys.is_empty() => keys,
			_ => {
				warn!("Cannot subscribe to all keys on light client. Subscription rejected.");
				return
			},
		};

		let keys = keys.iter().cloned().collect::<HashSet<_>>();
		let keys_to_check = keys.iter().map(|k| k.0.clone()).collect::<HashSet<_>>();
		let subscription_id = self.subscriptions.add(subscriber, move |sink| {
			let fetcher = self.fetcher.clone();
			let remote_blockchain = self.remote_blockchain.clone();
			let storage_subscriptions = self.storage_subscriptions.clone();
			let initial_block = self.block_or_best(None);
			let initial_keys = keys_to_check.iter().cloned().collect::<Vec<_>>();

			let changes_stream = subscription_stream::<Block, _, _, _, _, _, _, _, _>(
				storage_subscriptions.clone(),
				self.client.import_notification_stream().map(|notification| notification.hash),
				display_error(
					storage(&*remote_blockchain, fetcher.clone(), initial_block, initial_keys)
						.map(move |r| r.map(|r| (initial_block, r))),
				),
				move |block| {
					// there'll be single request per block for all active subscriptions
					// with all subscribed keys
					let keys = storage_subscriptions
						.lock()
						.subscriptions_by_key
						.keys()
						.map(|k| k.0.clone())
						.collect();

					storage(&*remote_blockchain, fetcher.clone(), block, keys)
				},
				move |block, old_value, new_value| {
					// let's only select keys which are valid for this subscription
					let new_value = new_value
						.iter()
						.filter(|(k, _)| keys_to_check.contains(&k.0))
						.map(|(k, v)| (k.clone(), v.clone()))
						.collect::<HashMap<_, _>>();
					let value_differs = old_value
						.as_ref()
						.map(|old_value| **old_value != new_value)
						.unwrap_or(true);

					value_differs.then(|| StorageChangeSet {
						block,
						changes: new_value.iter().map(|(k, v)| (k.clone(), v.clone())).collect(),
					})
				},
			);

			changes_stream
				.map_ok(Ok)
				.forward(sink.sink_map_err(|e| warn!("Error sending notifications: {:?}", e)))
				// we ignore the resulting Stream (if the first stream is over we are unsubscribed)
				.map(|_| ())
		});

		// remember keys associated with this subscription
		let mut storage_subscriptions = self.storage_subscriptions.lock();
		storage_subscriptions
			.keys_by_subscription
			.insert(subscription_id.clone(), keys.clone());
		for key in keys {
			storage_subscriptions
				.subscriptions_by_key
				.entry(key)
				.or_default()
				.insert(subscription_id.clone());
		}
	}

	fn unsubscribe_storage(
		&self,
		_meta: Option<crate::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		if !self.subscriptions.cancel(id.clone()) {
			return Ok(false)
		}

		// forget subscription keys
		let mut storage_subscriptions = self.storage_subscriptions.lock();
		let keys = storage_subscriptions.keys_by_subscription.remove(&id);
		for key in keys.into_iter().flat_map(|keys| keys.into_iter()) {
			match storage_subscriptions.subscriptions_by_key.entry(key) {
				Entry::Vacant(_) => unreachable!(
					"every key from keys_by_subscription has\
					corresponding entry in subscriptions_by_key; qed"
				),
				Entry::Occupied(mut entry) => {
					entry.get_mut().remove(&id);
					if entry.get().is_empty() {
						entry.remove();
					}
				},
			}
		}

		Ok(true)
	}

	fn subscribe_runtime_version(
		&self,
		_meta: crate::Metadata,
		subscriber: Subscriber<RuntimeVersion>,
	) {
		self.subscriptions.add(subscriber, move |sink| {
			let fetcher = self.fetcher.clone();
			let remote_blockchain = self.remote_blockchain.clone();
			let version_subscriptions = self.version_subscriptions.clone();
			let initial_block = self.block_or_best(None);

			let versions_stream = subscription_stream::<Block, _, _, _, _, _, _, _, _>(
				version_subscriptions,
				self.client.import_notification_stream().map(|notification| notification.hash),
				display_error(
					runtime_version(&*remote_blockchain, fetcher.clone(), initial_block)
						.map(move |r| r.map(|r| (initial_block, r))),
				),
				move |block| runtime_version(&*remote_blockchain, fetcher.clone(), block),
				|_, old_version, new_version| {
					let version_differs = old_version
						.as_ref()
						.map(|old_version| *old_version != new_version)
						.unwrap_or(true);

					version_differs.then(|| new_version.clone())
				},
			);

			versions_stream
				.map_ok(Ok)
				.forward(sink.sink_map_err(|e| warn!("Error sending notifications: {:?}", e)))
				// we ignore the resulting Stream (if the first stream is over we are unsubscribed)
				.map(|_| ())
		});
	}

	fn unsubscribe_runtime_version(
		&self,
		_meta: Option<crate::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}

	fn trace_block(
		&self,
		_block: Block::Hash,
		_targets: Option<String>,
		_storage_keys: Option<String>,
		_methods: Option<String>,
	) -> FutureResult<sp_rpc::tracing::TraceBlockResponse> {
		async move { Err(client_err(ClientError::NotAvailableOnLightClient)) }.boxed()
	}
}

impl<Block, F, Client> ChildStateBackend<Block, Client> for LightState<Block, F, Client>
where
	Block: BlockT,
	Client: BlockchainEvents<Block> + HeaderBackend<Block> + Send + Sync + 'static,
	F: Fetcher<Block> + 'static,
{
	fn read_child_proof(
		&self,
		_block: Option<Block::Hash>,
		_storage_key: PrefixedStorageKey,
		_keys: Vec<StorageKey>,
	) -> FutureResult<ReadProof<Block::Hash>> {
		async move { Err(client_err(ClientError::NotAvailableOnLightClient)) }.boxed()
	}

	fn storage_keys(
		&self,
		_block: Option<Block::Hash>,
		_storage_key: PrefixedStorageKey,
		_prefix: StorageKey,
	) -> FutureResult<Vec<StorageKey>> {
		async move { Err(client_err(ClientError::NotAvailableOnLightClient)) }.boxed()
	}

	fn storage_keys_paged(
		&self,
		_block: Option<Block::Hash>,
		_storage_key: PrefixedStorageKey,
		_prefix: Option<StorageKey>,
		_count: u32,
		_start_key: Option<StorageKey>,
	) -> FutureResult<Vec<StorageKey>> {
		async move { Err(client_err(ClientError::NotAvailableOnLightClient)) }.boxed()
	}

	fn storage(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
	) -> FutureResult<Option<StorageData>> {
		let block = self.block_or_best(block);
		let fetcher = self.fetcher.clone();
		let child_storage =
			resolve_header(&*self.remote_blockchain, &*self.fetcher, block).then(move |result| {
				match result {
					Ok(header) => Either::Left(
						fetcher
							.remote_read_child(RemoteReadChildRequest {
								block,
								header,
								storage_key,
								keys: vec![key.0.clone()],
								retry_count: Default::default(),
							})
							.then(move |result| {
								ready(
									result
										.map(|mut data| {
											data.remove(&key.0)
												.expect(
													"successful result has entry for all keys; qed",
												)
												.map(StorageData)
										})
										.map_err(client_err),
								)
							}),
					),
					Err(error) => Either::Right(ready(Err(error))),
				}
			});

		child_storage.boxed()
	}

	fn storage_hash(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
	) -> FutureResult<Option<Block::Hash>> {
		let child_storage = ChildStateBackend::storage(self, block, storage_key, key);

		async move { child_storage.await.map(|r| r.map(|s| HashFor::<Block>::hash(&s.0))) }.boxed()
	}
}

/// Resolve header by hash.
fn resolve_header<Block: BlockT, F: Fetcher<Block>>(
	remote_blockchain: &dyn RemoteBlockchain<Block>,
	fetcher: &F,
	block: Block::Hash,
) -> impl std::future::Future<Output = Result<Block::Header, Error>> {
	let maybe_header = future_header(remote_blockchain, fetcher, BlockId::Hash(block));

	maybe_header.then(move |result| {
		ready(
			result
				.and_then(|maybe_header| {
					maybe_header.ok_or_else(|| ClientError::UnknownBlock(format!("{}", block)))
				})
				.map_err(client_err),
		)
	})
}

/// Call runtime method at given block
fn call<Block: BlockT, F: Fetcher<Block>>(
	remote_blockchain: &dyn RemoteBlockchain<Block>,
	fetcher: Arc<F>,
	block: Block::Hash,
	method: String,
	call_data: Bytes,
) -> impl std::future::Future<Output = Result<Bytes, Error>> {
	resolve_header(remote_blockchain, &*fetcher, block).then(move |result| match result {
		Ok(header) => Either::Left(
			fetcher
				.remote_call(RemoteCallRequest {
					block,
					header,
					method,
					call_data: call_data.0,
					retry_count: Default::default(),
				})
				.then(|result| ready(result.map(Bytes).map_err(client_err))),
		),
		Err(error) => Either::Right(ready(Err(error))),
	})
}

/// Get runtime version at given block.
fn runtime_version<Block: BlockT, F: Fetcher<Block>>(
	remote_blockchain: &dyn RemoteBlockchain<Block>,
	fetcher: Arc<F>,
	block: Block::Hash,
) -> impl std::future::Future<Output = Result<RuntimeVersion, Error>> {
	call(remote_blockchain, fetcher, block, "Core_version".into(), Bytes(Vec::new())).then(
		|version| {
			ready(version.and_then(|version| {
				Decode::decode(&mut &version.0[..])
					.map_err(|e| client_err(ClientError::VersionInvalid(e.to_string())))
			}))
		},
	)
}

/// Get storage value at given key at given block.
fn storage<Block: BlockT, F: Fetcher<Block>>(
	remote_blockchain: &dyn RemoteBlockchain<Block>,
	fetcher: Arc<F>,
	block: Block::Hash,
	keys: Vec<Vec<u8>>,
) -> impl std::future::Future<Output = Result<HashMap<StorageKey, Option<StorageData>>, Error>> {
	resolve_header(remote_blockchain, &*fetcher, block).then(move |result| match result {
		Ok(header) => Either::Left(
			fetcher
				.remote_read(RemoteReadRequest {
					block,
					header,
					keys,
					retry_count: Default::default(),
				})
				.then(|result| {
					ready(
						result
							.map(|result| {
								result
									.into_iter()
									.map(|(key, value)| (StorageKey(key), value.map(StorageData)))
									.collect()
							})
							.map_err(client_err),
					)
				}),
		),
		Err(error) => Either::Right(ready(Err(error))),
	})
}

/// Returns subscription stream that issues request on every imported block and
/// if value has changed from previous block, emits (stream) item.
fn subscription_stream<
	Block,
	Requests,
	FutureBlocksStream,
	V,
	N,
	InitialRequestFuture,
	IssueRequest,
	IssueRequestFuture,
	CompareValues,
>(
	shared_requests: Requests,
	future_blocks_stream: FutureBlocksStream,
	initial_request: InitialRequestFuture,
	issue_request: IssueRequest,
	compare_values: CompareValues,
) -> impl Stream<Item = std::result::Result<N, ()>>
where
	Block: BlockT,
	Requests: 'static + SharedRequests<Block::Hash, V>,
	FutureBlocksStream: Stream<Item = Block::Hash>,
	V: Send + 'static + Clone,
	InitialRequestFuture: Future<Output = Result<(Block::Hash, V), ()>> + Send + 'static,
	IssueRequest: 'static + Fn(Block::Hash) -> IssueRequestFuture,
	IssueRequestFuture: Future<Output = Result<V, Error>> + Send + 'static,
	CompareValues: Fn(Block::Hash, Option<&V>, &V) -> Option<N>,
{
	// we need to send initial value first, then we'll only be sending if value has changed
	let previous_value = Arc::new(Mutex::new(None));

	// prepare 'stream' of initial values
	let initial_value_stream = initial_request.into_stream();

	// prepare stream of future values
	//
	// we do not want to stop stream if single request fails
	// (the warning should have been already issued by the request issuer)
	let future_values_stream = future_blocks_stream
		.then(move |block| {
			maybe_share_remote_request::<Block, _, _, _, _>(
				shared_requests.clone(),
				block,
				&issue_request,
			)
			.map(move |r| r.map(|v| (block, v)))
		})
		.filter(|r| ready(r.is_ok()));

	// now let's return changed values for selected blocks
	initial_value_stream
		.chain(future_values_stream)
		.try_filter_map(move |(block, new_value)| {
			let mut previous_value = previous_value.lock();
			let res = compare_values(block, previous_value.as_ref(), &new_value).map(
				|notification_value| {
					*previous_value = Some(new_value);
					notification_value
				},
			);
			async move { Ok(res) }
		})
		.map_err(|_| ())
}

/// Request some data from remote node, probably reusing response from already
/// (in-progress) existing request.
fn maybe_share_remote_request<Block: BlockT, Requests, V, IssueRequest, IssueRequestFuture>(
	shared_requests: Requests,
	block: Block::Hash,
	issue_request: &IssueRequest,
) -> impl std::future::Future<Output = Result<V, ()>>
where
	V: Clone,
	Requests: SharedRequests<Block::Hash, V>,
	IssueRequest: Fn(Block::Hash) -> IssueRequestFuture,
	IssueRequestFuture: std::future::Future<Output = Result<V, Error>>,
{
	let (sender, receiver) = channel();
	let need_issue_request = shared_requests.listen_request(block, sender);

	// if that isn't the first request - just listen for existing request' response
	if !need_issue_request {
		return Either::Right(receiver.then(|r| ready(r.unwrap_or(Err(())))))
	}

	// that is the first request - issue remote request + notify all listeners on
	// completion
	Either::Left(display_error(issue_request(block)).then(move |remote_result| {
		let listeners = shared_requests.on_response_received(block);
		// skip first element, because this future is the first element
		for receiver in listeners.into_iter().skip(1) {
			if let Err(_) = receiver.send(remote_result.clone()) {
				// we don't care if receiver has been dropped already
			}
		}

		ready(remote_result)
	}))
}

/// Convert successful future result into Ok(result) and error into Err(()),
/// displaying warning.
fn display_error<F, T>(future: F) -> impl std::future::Future<Output = Result<T, ()>>
where
	F: std::future::Future<Output = Result<T, Error>>,
{
	future.then(|result| {
		ready(result.or_else(|err| {
			warn!("Remote request for subscription data has failed with: {:?}", err);
			Err(())
		}))
	})
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures::{executor, stream};
	use sp_core::H256;
	use substrate_test_runtime_client::runtime::Block;

	#[test]
	fn subscription_stream_works() {
		let stream = subscription_stream::<Block, _, _, _, _, _, _, _, _>(
			SimpleSubscriptions::default(),
			stream::iter(vec![H256::from([2; 32]), H256::from([3; 32])]),
			ready(Ok((H256::from([1; 32]), 100))),
			|block| match block[0] {
				2 => ready(Ok(100)),
				3 => ready(Ok(200)),
				_ => unreachable!("should not issue additional requests"),
			},
			|_, old_value, new_value| match old_value == Some(new_value) {
				true => None,
				false => Some(new_value.clone()),
			},
		);

		assert_eq!(executor::block_on(stream.collect::<Vec<_>>()), vec![Ok(100), Ok(200)]);
	}

	#[test]
	fn subscription_stream_ignores_failed_requests() {
		let stream = subscription_stream::<Block, _, _, _, _, _, _, _, _>(
			SimpleSubscriptions::default(),
			stream::iter(vec![H256::from([2; 32]), H256::from([3; 32])]),
			ready(Ok((H256::from([1; 32]), 100))),
			|block| match block[0] {
				2 => ready(Err(client_err(ClientError::NotAvailableOnLightClient))),
				3 => ready(Ok(200)),
				_ => unreachable!("should not issue additional requests"),
			},
			|_, old_value, new_value| match old_value == Some(new_value) {
				true => None,
				false => Some(new_value.clone()),
			},
		);

		assert_eq!(executor::block_on(stream.collect::<Vec<_>>()), vec![Ok(100), Ok(200)]);
	}

	#[test]
	fn maybe_share_remote_request_shares_request() {
		type UnreachableFuture = futures::future::Ready<Result<u32, Error>>;

		let shared_requests = SimpleSubscriptions::default();

		// let's 'issue' requests for B1
		shared_requests.lock().insert(H256::from([1; 32]), vec![channel().0]);

		// make sure that no additional requests are issued when we're asking for B1
		let _ = maybe_share_remote_request::<Block, _, _, _, UnreachableFuture>(
			shared_requests.clone(),
			H256::from([1; 32]),
			&|_| unreachable!("no duplicate requests issued"),
		);

		// make sure that additional requests is issued when we're asking for B2
		let request_issued = Arc::new(Mutex::new(false));
		let _ = maybe_share_remote_request::<Block, _, _, _, UnreachableFuture>(
			shared_requests.clone(),
			H256::from([2; 32]),
			&|_| {
				*request_issued.lock() = true;
				ready(Ok(Default::default()))
			},
		);
		assert!(*request_issued.lock());
	}
}
