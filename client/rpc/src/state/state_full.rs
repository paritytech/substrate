// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! State API backend for full nodes.

use futures::{
	future,
	future::{err, try_join_all},
	stream, FutureExt, SinkExt, StreamExt,
};
use jsonrpc_pubsub::{manager::SubscriptionManager, typed::Subscriber, SubscriptionId};
use log::warn;
use rpc::Result as RpcResult;
use std::{collections::HashMap, sync::Arc};

use sc_rpc_api::state::ReadProof;
use sp_blockchain::{
	CachedHeaderMetadata, Error as ClientError, HeaderBackend, HeaderMetadata,
	Result as ClientResult,
};
use sp_core::{
	storage::{
		ChildInfo, ChildType, PrefixedStorageKey, StorageChangeSet, StorageData, StorageKey,
	},
	Bytes,
};
use sp_runtime::{generic::BlockId, traits::Block as BlockT};
use sp_version::RuntimeVersion;

use sp_api::{CallApiAt, Metadata, ProvideRuntimeApi};

use super::{
	client_err,
	error::{Error, FutureResult, Result},
	ChildStateBackend, StateBackend,
};
use sc_client_api::{
	Backend, BlockBackend, BlockchainEvents, CallExecutor, ExecutorProvider, ProofProvider,
	StorageNotification, StorageProvider,
};
use std::marker::PhantomData;

/// Ranges to query in state_queryStorage.
struct QueryStorageRange<Block: BlockT> {
	/// Hashes of all the blocks in the range.
	pub hashes: Vec<Block::Hash>,
}

/// State API backend for full nodes.
pub struct FullState<BE, Block: BlockT, Client> {
	client: Arc<Client>,
	subscriptions: SubscriptionManager,
	_phantom: PhantomData<(BE, Block)>,
	rpc_max_payload: Option<usize>,
}

impl<BE, Block: BlockT, Client> FullState<BE, Block, Client>
where
	BE: Backend<Block>,
	Client: StorageProvider<Block, BE>
		+ HeaderBackend<Block>
		+ BlockBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>,
	Block: BlockT + 'static,
{
	/// Create new state API backend for full nodes.
	pub fn new(
		client: Arc<Client>,
		subscriptions: SubscriptionManager,
		rpc_max_payload: Option<usize>,
	) -> Self {
		Self { client, subscriptions, _phantom: PhantomData, rpc_max_payload }
	}

	/// Returns given block hash or best block hash if None is passed.
	fn block_or_best(&self, hash: Option<Block::Hash>) -> ClientResult<Block::Hash> {
		Ok(hash.unwrap_or_else(|| self.client.info().best_hash))
	}

	/// Validates block range.
	fn query_storage_range(
		&self,
		from: Block::Hash,
		to: Option<Block::Hash>,
	) -> Result<QueryStorageRange<Block>> {
		let to = self
			.block_or_best(to)
			.map_err(|e| invalid_block::<Block>(from, to, e.to_string()))?;

		let invalid_block_err =
			|e: ClientError| invalid_block::<Block>(from, Some(to), e.to_string());
		let from_meta = self.client.header_metadata(from).map_err(invalid_block_err)?;
		let to_meta = self.client.header_metadata(to).map_err(invalid_block_err)?;

		if from_meta.number > to_meta.number {
			return Err(invalid_block_range(
				&from_meta,
				&to_meta,
				"from number > to number".to_owned(),
			))
		}

		// check if we can get from `to` to `from` by going through parent_hashes.
		let from_number = from_meta.number;
		let hashes = {
			let mut hashes = vec![to_meta.hash];
			let mut last = to_meta.clone();
			while last.number > from_number {
				let header_metadata = self
					.client
					.header_metadata(last.parent)
					.map_err(|e| invalid_block_range::<Block>(&last, &to_meta, e.to_string()))?;
				hashes.push(header_metadata.hash);
				last = header_metadata;
			}
			if last.hash != from_meta.hash {
				return Err(invalid_block_range(
					&from_meta,
					&to_meta,
					"from and to are on different forks".to_owned(),
				))
			}
			hashes.reverse();
			hashes
		};

		Ok(QueryStorageRange { hashes })
	}

	/// Iterates through range.unfiltered_range and check each block for changes of keys' values.
	fn query_storage_unfiltered(
		&self,
		range: &QueryStorageRange<Block>,
		keys: &[StorageKey],
		last_values: &mut HashMap<StorageKey, Option<StorageData>>,
		changes: &mut Vec<StorageChangeSet<Block::Hash>>,
	) -> Result<()> {
		for block_hash in &range.hashes {
			let block_hash = block_hash.clone();
			let mut block_changes =
				StorageChangeSet { block: block_hash.clone(), changes: Vec::new() };
			let id = BlockId::hash(block_hash);
			for key in keys {
				let (has_changed, data) = {
					let curr_data = self.client.storage(&id, key).map_err(client_err)?;
					match last_values.get(key) {
						Some(prev_data) => (curr_data != *prev_data, curr_data),
						None => (true, curr_data),
					}
				};
				if has_changed {
					block_changes.changes.push((key.clone(), data.clone()));
				}
				last_values.insert(key.clone(), data);
			}
			if !block_changes.changes.is_empty() {
				changes.push(block_changes);
			}
		}
		Ok(())
	}
}

impl<BE, Block, Client> StateBackend<Block, Client> for FullState<BE, Block, Client>
where
	Block: BlockT + 'static,
	Block::Hash: Unpin,
	BE: Backend<Block> + 'static,
	Client: ExecutorProvider<Block>
		+ StorageProvider<Block, BE>
		+ ProofProvider<Block>
		+ HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ BlockchainEvents<Block>
		+ CallApiAt<Block>
		+ ProvideRuntimeApi<Block>
		+ BlockBackend<Block>
		+ Send
		+ Sync
		+ 'static,
	Client::Api: Metadata<Block>,
{
	fn call(
		&self,
		block: Option<Block::Hash>,
		method: String,
		call_data: Bytes,
	) -> FutureResult<Bytes> {
		let r = self
			.block_or_best(block)
			.and_then(|block| {
				self.client
					.executor()
					.call(
						&BlockId::Hash(block),
						&method,
						&*call_data,
						self.client.execution_extensions().strategies().other,
						None,
					)
					.map(Into::into)
			})
			.map_err(client_err);
		async move { r }.boxed()
	}

	fn storage_keys(
		&self,
		block: Option<Block::Hash>,
		prefix: StorageKey,
	) -> FutureResult<Vec<StorageKey>> {
		let r = self
			.block_or_best(block)
			.and_then(|block| self.client.storage_keys(&BlockId::Hash(block), &prefix))
			.map_err(client_err);
		async move { r }.boxed()
	}

	fn storage_pairs(
		&self,
		block: Option<Block::Hash>,
		prefix: StorageKey,
	) -> FutureResult<Vec<(StorageKey, StorageData)>> {
		let r = self
			.block_or_best(block)
			.and_then(|block| self.client.storage_pairs(&BlockId::Hash(block), &prefix))
			.map_err(client_err);
		async move { r }.boxed()
	}

	fn storage_keys_paged(
		&self,
		block: Option<Block::Hash>,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
	) -> FutureResult<Vec<StorageKey>> {
		let r = self
			.block_or_best(block)
			.and_then(|block| {
				self.client.storage_keys_iter(
					&BlockId::Hash(block),
					prefix.as_ref(),
					start_key.as_ref(),
				)
			})
			.map(|iter| iter.take(count as usize).collect())
			.map_err(client_err);
		async move { r }.boxed()
	}

	fn storage(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<StorageData>> {
		let r = self
			.block_or_best(block)
			.and_then(|block| self.client.storage(&BlockId::Hash(block), &key))
			.map_err(client_err);
		async move { r }.boxed()
	}

	fn storage_size(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<u64>> {
		let block = match self.block_or_best(block) {
			Ok(b) => b,
			Err(e) => return async move { Err(client_err(e)) }.boxed(),
		};

		match self.client.storage(&BlockId::Hash(block), &key) {
			Ok(Some(d)) => return async move { Ok(Some(d.0.len() as u64)) }.boxed(),
			Err(e) => return async move { Err(client_err(e)) }.boxed(),
			Ok(None) => {},
		}

		let r = self
			.client
			.storage_pairs(&BlockId::Hash(block), &key)
			.map(|kv| {
				let item_sum = kv.iter().map(|(_, v)| v.0.len() as u64).sum::<u64>();
				if item_sum > 0 {
					Some(item_sum)
				} else {
					None
				}
			})
			.map_err(client_err);
		async move { r }.boxed()
	}

	fn storage_hash(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<Block::Hash>> {
		let r = self
			.block_or_best(block)
			.and_then(|block| self.client.storage_hash(&BlockId::Hash(block), &key))
			.map_err(client_err);
		async move { r }.boxed()
	}

	fn metadata(&self, block: Option<Block::Hash>) -> FutureResult<Bytes> {
		let r = self.block_or_best(block).map_err(client_err).and_then(|block| {
			self.client
				.runtime_api()
				.metadata(&BlockId::Hash(block))
				.map(Into::into)
				.map_err(|e| Error::Client(Box::new(e)))
		});
		async move { r }.boxed()
	}

	fn runtime_version(&self, block: Option<Block::Hash>) -> FutureResult<RuntimeVersion> {
		let r = self.block_or_best(block).map_err(client_err).and_then(|block| {
			self.client
				.runtime_version_at(&BlockId::Hash(block))
				.map_err(|e| Error::Client(Box::new(e)))
		});
		async move { r }.boxed()
	}

	fn query_storage(
		&self,
		from: Block::Hash,
		to: Option<Block::Hash>,
		keys: Vec<StorageKey>,
	) -> FutureResult<Vec<StorageChangeSet<Block::Hash>>> {
		let call_fn = move || {
			let range = self.query_storage_range(from, to)?;
			let mut changes = Vec::new();
			let mut last_values = HashMap::new();
			self.query_storage_unfiltered(&range, &keys, &mut last_values, &mut changes)?;
			Ok(changes)
		};

		let r = call_fn();
		async move { r }.boxed()
	}

	fn query_storage_at(
		&self,
		keys: Vec<StorageKey>,
		at: Option<Block::Hash>,
	) -> FutureResult<Vec<StorageChangeSet<Block::Hash>>> {
		let at = at.unwrap_or_else(|| self.client.info().best_hash);
		self.query_storage(at, Some(at), keys)
	}

	fn read_proof(
		&self,
		block: Option<Block::Hash>,
		keys: Vec<StorageKey>,
	) -> FutureResult<ReadProof<Block::Hash>> {
		let r = self
			.block_or_best(block)
			.and_then(|block| {
				self.client
					.read_proof(&BlockId::Hash(block), &mut keys.iter().map(|key| key.0.as_ref()))
					.map(|proof| proof.iter_nodes().map(|node| node.into()).collect())
					.map(|proof| ReadProof { at: block, proof })
			})
			.map_err(client_err);
		async move { r }.boxed()
	}

	fn subscribe_runtime_version(
		&self,
		_meta: crate::Metadata,
		subscriber: Subscriber<RuntimeVersion>,
	) {
		self.subscriptions.add(subscriber, |sink| {
			let version = self
				.block_or_best(None)
				.and_then(|block| {
					self.client.runtime_version_at(&BlockId::Hash(block)).map_err(Into::into)
				})
				.map_err(client_err)
				.map_err(Into::into);

			let client = self.client.clone();
			let mut previous_version = version.clone();

			// A stream of all best blocks.
			let stream =
				client.import_notification_stream().filter(|n| future::ready(n.is_new_best));

			let stream = stream.filter_map(move |n| {
				let version = client
					.runtime_version_at(&BlockId::hash(n.hash))
					.map_err(|e| Error::Client(Box::new(e)))
					.map_err(Into::into);

				if previous_version != version {
					previous_version = version.clone();
					future::ready(Some(Ok::<_, ()>(version)))
				} else {
					future::ready(None)
				}
			});

			stream::iter(vec![Ok(version)])
				.chain(stream)
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

	fn subscribe_storage(
		&self,
		_meta: crate::Metadata,
		subscriber: Subscriber<StorageChangeSet<Block::Hash>>,
		keys: Option<Vec<StorageKey>>,
	) {
		let keys = Into::<Option<Vec<_>>>::into(keys);
		let stream = match self.client.storage_changes_notification_stream(keys.as_deref(), None) {
			Ok(stream) => stream,
			Err(err) => {
				let _ = subscriber.reject(client_err(err).into());
				return
			},
		};

		// initial values
		let initial = stream::iter(
			keys.map(|keys| {
				let block = self.client.info().best_hash;
				let changes = keys
					.into_iter()
					.map(|key| {
						let v = self.client.storage(&BlockId::Hash(block), &key).ok().flatten();
						(key, v)
					})
					.collect();
				vec![Ok(Ok(StorageChangeSet { block, changes }))]
			})
			.unwrap_or_default(),
		);

		self.subscriptions.add(subscriber, |sink| {
			let stream = stream.map(|StorageNotification { block, changes }| {
				Ok(Ok::<_, rpc::Error>(StorageChangeSet {
					block,
					changes: changes
						.iter()
						.filter_map(|(o_sk, k, v)| o_sk.is_none().then(|| (k.clone(), v.cloned())))
						.collect(),
				}))
			});

			initial
				.chain(stream)
				.forward(sink.sink_map_err(|e| warn!("Error sending notifications: {:?}", e)))
				// we ignore the resulting Stream (if the first stream is over we are unsubscribed)
				.map(|_| ())
		});
	}

	fn unsubscribe_storage(
		&self,
		_meta: Option<crate::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}

	fn trace_block(
		&self,
		block: Block::Hash,
		targets: Option<String>,
		storage_keys: Option<String>,
		methods: Option<String>,
	) -> FutureResult<sp_rpc::tracing::TraceBlockResponse> {
		let block_executor = sc_tracing::block::BlockExecutor::new(
			self.client.clone(),
			block,
			targets,
			storage_keys,
			methods,
			self.rpc_max_payload,
		);
		let r = block_executor
			.trace_block()
			.map_err(|e| invalid_block::<Block>(block, None, e.to_string()));
		async move { r }.boxed()
	}
}

impl<BE, Block, Client> ChildStateBackend<Block, Client> for FullState<BE, Block, Client>
where
	Block: BlockT + 'static,
	BE: Backend<Block> + 'static,
	Client: ExecutorProvider<Block>
		+ StorageProvider<Block, BE>
		+ ProofProvider<Block>
		+ HeaderBackend<Block>
		+ BlockBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ BlockchainEvents<Block>
		+ CallApiAt<Block>
		+ ProvideRuntimeApi<Block>
		+ Send
		+ Sync
		+ 'static,
	Client::Api: Metadata<Block>,
{
	fn read_child_proof(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
	) -> FutureResult<ReadProof<Block::Hash>> {
		let r = self
			.block_or_best(block)
			.and_then(|block| {
				let child_info = match ChildType::from_prefixed_key(&storage_key) {
					Some((ChildType::ParentKeyId, storage_key)) =>
						ChildInfo::new_default(storage_key),
					None => return Err(sp_blockchain::Error::InvalidChildStorageKey),
				};
				self.client
					.read_child_proof(
						&BlockId::Hash(block),
						&child_info,
						&mut keys.iter().map(|key| key.0.as_ref()),
					)
					.map(|proof| proof.iter_nodes().map(|node| node.into()).collect())
					.map(|proof| ReadProof { at: block, proof })
			})
			.map_err(client_err);

		async move { r }.boxed()
	}

	fn storage_keys(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		prefix: StorageKey,
	) -> FutureResult<Vec<StorageKey>> {
		let r = self
			.block_or_best(block)
			.and_then(|block| {
				let child_info = match ChildType::from_prefixed_key(&storage_key) {
					Some((ChildType::ParentKeyId, storage_key)) =>
						ChildInfo::new_default(storage_key),
					None => return Err(sp_blockchain::Error::InvalidChildStorageKey),
				};
				self.client.child_storage_keys(&BlockId::Hash(block), &child_info, &prefix)
			})
			.map_err(client_err);

		async move { r }.boxed()
	}

	fn storage_keys_paged(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		prefix: Option<StorageKey>,
		count: u32,
		start_key: Option<StorageKey>,
	) -> FutureResult<Vec<StorageKey>> {
		let r = self
			.block_or_best(block)
			.and_then(|block| {
				let child_info = match ChildType::from_prefixed_key(&storage_key) {
					Some((ChildType::ParentKeyId, storage_key)) =>
						ChildInfo::new_default(storage_key),
					None => return Err(sp_blockchain::Error::InvalidChildStorageKey),
				};
				self.client.child_storage_keys_iter(
					&BlockId::Hash(block),
					child_info,
					prefix.as_ref(),
					start_key.as_ref(),
				)
			})
			.map(|iter| iter.take(count as usize).collect())
			.map_err(client_err);

		async move { r }.boxed()
	}

	fn storage(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
	) -> FutureResult<Option<StorageData>> {
		let r = self
			.block_or_best(block)
			.and_then(|block| {
				let child_info = match ChildType::from_prefixed_key(&storage_key) {
					Some((ChildType::ParentKeyId, storage_key)) =>
						ChildInfo::new_default(storage_key),
					None => return Err(sp_blockchain::Error::InvalidChildStorageKey),
				};
				self.client.child_storage(&BlockId::Hash(block), &child_info, &key)
			})
			.map_err(client_err);

		async move { r }.boxed()
	}

	fn storage_entries(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		keys: Vec<StorageKey>,
	) -> FutureResult<Vec<Option<StorageData>>> {
		let child_info = match ChildType::from_prefixed_key(&storage_key) {
			Some((ChildType::ParentKeyId, storage_key)) =>
				Arc::new(ChildInfo::new_default(storage_key)),
			None => return err(client_err(sp_blockchain::Error::InvalidChildStorageKey)).boxed(),
		};
		let block = match self.block_or_best(block) {
			Ok(b) => b,
			Err(e) => return err(client_err(e)).boxed(),
		};
		let client = self.client.clone();
		try_join_all(keys.into_iter().map(move |key| {
			let res = client
				.clone()
				.child_storage(&BlockId::Hash(block), &child_info, &key)
				.map_err(client_err);

			async move { res }
		}))
		.boxed()
	}

	fn storage_hash(
		&self,
		block: Option<Block::Hash>,
		storage_key: PrefixedStorageKey,
		key: StorageKey,
	) -> FutureResult<Option<Block::Hash>> {
		let r = self
			.block_or_best(block)
			.and_then(|block| {
				let child_info = match ChildType::from_prefixed_key(&storage_key) {
					Some((ChildType::ParentKeyId, storage_key)) =>
						ChildInfo::new_default(storage_key),
					None => return Err(sp_blockchain::Error::InvalidChildStorageKey),
				};
				self.client.child_storage_hash(&BlockId::Hash(block), &child_info, &key)
			})
			.map_err(client_err);

		async move { r }.boxed()
	}
}

fn invalid_block_range<B: BlockT>(
	from: &CachedHeaderMetadata<B>,
	to: &CachedHeaderMetadata<B>,
	details: String,
) -> Error {
	let to_string = |h: &CachedHeaderMetadata<B>| format!("{} ({:?})", h.number, h.hash);

	Error::InvalidBlockRange { from: to_string(from), to: to_string(to), details }
}

fn invalid_block<B: BlockT>(from: B::Hash, to: Option<B::Hash>, details: String) -> Error {
	Error::InvalidBlockRange { from: format!("{:?}", from), to: format!("{:?}", to), details }
}
