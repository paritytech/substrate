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

//! State API backend for full nodes.

use futures::{future, stream, FutureExt, SinkExt, StreamExt};
use jsonrpc_pubsub::{manager::SubscriptionManager, typed::Subscriber, SubscriptionId};
use log::warn;
use rpc::Result as RpcResult;
use std::{
	collections::{BTreeMap, HashMap},
	marker::PhantomData,
	ops::Range,
	sync::Arc,
};

use sc_client_api::{
	Backend, BlockBackend, BlockchainEvents, CallExecutor, ExecutorProvider, ProofProvider,
	StateBackendFor, StorageProvider,
};
use sc_rpc_api::state::ReadProof;
use sc_rpc_server::RPC_MAX_PAYLOAD_DEFAULT;
use sp_api::{ApiExt, CallApiAt, Core, Metadata, ProvideRuntimeApi};
use sp_blockchain::{
	CachedHeaderMetadata, Error as ClientError, HeaderBackend, HeaderMetadata,
	Result as ClientResult,
};
use sp_core::{
	storage::{
		well_known_keys, ChildInfo, ChildType, PrefixedStorageKey, StorageChangeSet, StorageData,
		StorageKey,
	},
	Bytes,
};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, CheckedSub, Header as HeaderT, NumberFor, SaturatedConversion},
};
use sp_version::RuntimeVersion;

use super::{
	client_err,
	error::{Error, FutureResult, Result},
	BlockExecError, BlockExecResult, ChildStateBackend, StateBackend,
};

// Heuristic for average storage key/value size in bytes.
const AVG_STORAGE_KV: usize = 200 * 8;
// Estimate of the max base RPC payload size when the Id is bound as a u64. If strings
// are used for the RPC Id this may need to be adjusted. Note: The base payload
// does not include the RPC result.
//
// The estimate is based on the JSONRPC response message which has the following format:
// `{"jsonrpc":"2.0","result":[],"id":18446744073709551615}`.
//
// We care about the total size of the payload because jsonrpc-server will simply ignore
// messages larger than `sc_rpc_server::MAX_PAYLOAD` and the caller will not get any
// response.
const BASE_PAYLOAD: usize = 100;
const MEGABYTE: usize = 1024 * 1024;

/// Ranges to query in state_queryStorage.
struct QueryStorageRange<Block: BlockT> {
	/// Hashes of all the blocks in the range.
	pub hashes: Vec<Block::Hash>,
	/// Number of the first block in the range.
	pub first_number: NumberFor<Block>,
	/// Blocks subrange ([begin; end) indices within `hashes`) where we should read keys at
	/// each state to get changes.
	pub unfiltered_range: Range<usize>,
	/// Blocks subrange ([begin; end) indices within `hashes`) where we could pre-filter
	/// blocks-with-changes by using changes tries.
	pub filtered_range: Option<Range<usize>>,
}

/// State API backend for full nodes.
pub struct FullState<BE, Block: BlockT, Client> {
	backend: Arc<BE>,
	client: Arc<Client>,
	subscriptions: SubscriptionManager,
	_phantom: PhantomData<(BE, Block)>,
	rpc_max_payload: Option<usize>,
}

impl<BE, Block, Client> FullState<BE, Block, Client>
where
	BE: Backend<Block>,
	Client: StorageProvider<Block, BE>
		+ HeaderBackend<Block>
		+ BlockBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ ProvideRuntimeApi<Block>,
	Block: BlockT + 'static,
	Client::Api: Metadata<Block> + ApiExt<Block, StateBackend = StateBackendFor<BE, Block>>,
{
	/// Create new state API backend for full nodes.
	pub fn new(
		backend: Arc<BE>,
		client: Arc<Client>,
		subscriptions: SubscriptionManager,
		rpc_max_payload: Option<usize>,
	) -> Self {
		Self { backend, client, subscriptions, _phantom: PhantomData, rpc_max_payload }
	}

	/// Returns given block hash or best block hash if None is passed.
	fn block_or_best(&self, hash: Option<Block::Hash>) -> ClientResult<Block::Hash> {
		Ok(hash.unwrap_or_else(|| self.client.info().best_hash))
	}

	/// Splits the `query_storage` block range into 'filtered' and 'unfiltered' subranges.
	/// Blocks that contain changes within filtered subrange could be filtered using changes tries.
	/// Blocks that contain changes within unfiltered subrange must be filtered manually.
	fn split_query_storage_range(
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

		// check if we can filter blocks-with-changes from some (sub)range using changes tries
		let changes_trie_range = self
			.client
			.max_key_changes_range(from_number, BlockId::Hash(to_meta.hash))
			.map_err(client_err)?;
		let filtered_range_begin = changes_trie_range.and_then(|(begin, _)| {
			// avoids a corner case where begin < from_number (happens when querying genesis)
			begin.checked_sub(&from_number).map(|x| x.saturated_into::<usize>())
		});
		let (unfiltered_range, filtered_range) = split_range(hashes.len(), filtered_range_begin);

		Ok(QueryStorageRange {
			hashes,
			first_number: from_number,
			unfiltered_range,
			filtered_range,
		})
	}

	/// Iterates through range.unfiltered_range and check each block for changes of keys' values.
	fn query_storage_unfiltered(
		&self,
		range: &QueryStorageRange<Block>,
		keys: &[StorageKey],
		last_values: &mut HashMap<StorageKey, Option<StorageData>>,
		changes: &mut Vec<StorageChangeSet<Block::Hash>>,
	) -> Result<()> {
		for block in range.unfiltered_range.start..range.unfiltered_range.end {
			let block_hash = range.hashes[block].clone();
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

	/// Iterates through all blocks that are changing keys within range.filtered_range and collects
	/// these changes.
	fn query_storage_filtered(
		&self,
		range: &QueryStorageRange<Block>,
		keys: &[StorageKey],
		last_values: &HashMap<StorageKey, Option<StorageData>>,
		changes: &mut Vec<StorageChangeSet<Block::Hash>>,
	) -> Result<()> {
		let (begin, end) = match range.filtered_range {
			Some(ref filtered_range) => (
				range.first_number + filtered_range.start.saturated_into(),
				BlockId::Hash(range.hashes[filtered_range.end - 1].clone()),
			),
			None => return Ok(()),
		};
		let mut changes_map: BTreeMap<NumberFor<Block>, StorageChangeSet<Block::Hash>> =
			BTreeMap::new();
		for key in keys {
			let mut last_block = None;
			let mut last_value = last_values.get(key).cloned().unwrap_or_default();
			let key_changes = self.client.key_changes(begin, end, None, key).map_err(client_err)?;
			for (block, _) in key_changes.into_iter().rev() {
				if last_block == Some(block) {
					continue
				}

				let block_hash =
					range.hashes[(block - range.first_number).saturated_into::<usize>()].clone();
				let id = BlockId::Hash(block_hash);
				let value_at_block = self.client.storage(&id, key).map_err(client_err)?;
				if last_value == value_at_block {
					continue
				}

				changes_map
					.entry(block)
					.or_insert_with(|| StorageChangeSet { block: block_hash, changes: Vec::new() })
					.changes
					.push((key.clone(), value_at_block.clone()));
				last_block = Some(block);
				last_value = value_at_block;
			}
		}
		if let Some(additional_capacity) = changes_map.len().checked_sub(changes.len()) {
			changes.reserve(additional_capacity);
		}
		changes.extend(changes_map.into_iter().map(|(_, cs)| cs));
		Ok(())
	}

	fn query_storage_changes(
		&self,
		block: Block::Hash,
	) -> BlockExecResult<(Block::Hash, sp_api::StorageChanges<BE::State, Block>)> {
		// Prepare the block
		let id = BlockId::Hash(block);
		let mut header = self
			.client
			.header(id)
			.map_err(|e| BlockExecError::InvalidBlockId(e))?
			.ok_or_else(|| BlockExecError::MissingBlockComponent("Header not found".into()))?;
		let extrinsics = self
			.client
			.block_body(&id)
			.map_err(|e| BlockExecError::InvalidBlockId(e))?
			.ok_or_else(|| BlockExecError::MissingBlockComponent("Extrinsics not found".into()))?;

		let parent_hash = *header.parent_hash();
		let parent_id = BlockId::Hash(parent_hash);
		// Remove all `Seal`s as they are added by the consensus engines after building the block.
		// On import they are normally removed by the consensus engine.
		header.digest_mut().logs.retain(|d| d.as_seal().is_none());

		let state = self
			.backend
			.state_at(parent_id)
			.map_err(|e| BlockExecError::InvalidBlockId(e))?;
		let api = self.client.runtime_api();
		api.execute_block(&parent_id, Block::new(header, extrinsics))
			.map_err(|e| BlockExecError::InvalidBlockId(e.into()))?;
		api.into_storage_changes(&state, None, parent_hash)
			.map(|storage_changes| (parent_hash, storage_changes))
			.map_err(BlockExecError::Other)
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
	Client::Api: Metadata<Block> + ApiExt<Block, StateBackend = StateBackendFor<BE, Block>>,
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
			let range = self.split_query_storage_range(from, to)?;
			let mut changes = Vec::new();
			let mut last_values = HashMap::new();
			self.query_storage_unfiltered(&range, &keys, &mut last_values, &mut changes)?;
			self.query_storage_filtered(&range, &keys, &last_values, &mut changes)?;
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
		let stream = match self.client.storage_changes_notification_stream(
			Some(&[StorageKey(well_known_keys::CODE.to_vec())]),
			None,
		) {
			Ok(stream) => stream,
			Err(err) => {
				let _ = subscriber.reject(Error::from(client_err(err)).into());
				return
			},
		};

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

			let stream = stream.filter_map(move |_| {
				let info = client.info();
				let version = client
					.runtime_version_at(&BlockId::hash(info.best_hash))
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
		let stream = match self
			.client
			.storage_changes_notification_stream(keys.as_ref().map(|x| &**x), None)
		{
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
			let stream = stream.map(|(block, changes)| {
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
	) -> FutureResult<sp_rpc::tracing::TraceBlockResponse> {
		let block_executor = sc_tracing::block::BlockExecutor::new(
			self.client.clone(),
			block,
			targets,
			storage_keys,
			self.rpc_max_payload,
		);
		let r = block_executor
			.trace_block()
			.map_err(|e| invalid_block::<Block>(block, None, e.to_string()));
		async move { r }.boxed()
	}

	fn diff_block_storage(
		&self,
		block: Block::Hash,
		storage_prefixes: Option<Vec<String>>,
	) -> FutureResult<sp_rpc::storage::BlockStorageChangesResponse<Block::Hash>> {
		let prefixes = storage_prefixes.clone().map(|prefixes| {
			prefixes
				.into_iter()
				.filter_map(|prefix| hex::decode(prefix).ok())
				.collect::<Vec<_>>()
		});
		let rpc_max_payload = self
			.rpc_max_payload
			.map(|mb| mb.saturating_mul(MEGABYTE))
			.unwrap_or(RPC_MAX_PAYLOAD_DEFAULT);
		let r = self
			.query_storage_changes(block)
			.map(|(parent_hash, storage_changes)| {
				let main_storage_changes = storage_changes
					.main_storage_changes
					.into_iter()
					.filter(|(k, _v)| storage_key_filter(k, &prefixes))
					.map(|(k, v)| (StorageKey(k), v.map(StorageData)))
					.collect::<Vec<_>>();
				let approx_payload_size =
					BASE_PAYLOAD + main_storage_changes.len() * AVG_STORAGE_KV;
				if approx_payload_size > rpc_max_payload {
					sp_rpc::storage::BlockStorageChangesResponse::StorageChangesError(
						sp_rpc::storage::StorageChangesError {
							error: "Payload likely exceeds max payload size of RPC server."
								.to_string(),
						},
					)
				} else {
					sp_rpc::storage::BlockStorageChangesResponse::BlockStorageChanges(
						sp_rpc::storage::BlockStorageChanges {
							block_hash: block,
							parent_hash,
							storage_prefixes: storage_prefixes.unwrap_or_default(),
							storage_changes: main_storage_changes,
						},
					)
				}
			})
			.map_err(|e| invalid_block::<Block>(block, None, e.to_string()));

		async move { r }.boxed()
	}
}

fn storage_key_filter(key: &[u8], prefixes: &Option<Vec<Vec<u8>>>) -> bool {
	if let Some(prefixes) = prefixes {
		for prefix in prefixes {
			if key.starts_with(prefix) {
				return true
			}
		}
		return false
	} else {
		true
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
	Client::Api: Metadata<Block> + ApiExt<Block, StateBackend = StateBackendFor<BE, Block>>,
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

/// Splits passed range into two subranges where:
/// - first range has at least one element in it;
/// - second range (optionally) starts at given `middle` element.
pub(crate) fn split_range(
	size: usize,
	middle: Option<usize>,
) -> (Range<usize>, Option<Range<usize>>) {
	// check if we can filter blocks-with-changes from some (sub)range using changes tries
	let range2_begin = match middle {
		// some of required changes tries are pruned => use available tries
		Some(middle) if middle != 0 => Some(middle),
		// all required changes tries are available, but we still want values at first block
		// => do 'unfiltered' read for the first block and 'filtered' for the rest
		Some(_) if size > 1 => Some(1),
		// range contains single element => do not use changes tries
		Some(_) => None,
		// changes tries are not available => do 'unfiltered' read for the whole range
		None => None,
	};
	let range1 = 0..range2_begin.unwrap_or(size);
	let range2 = range2_begin.map(|begin| begin..size);
	(range1, range2)
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
