// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! State API backend for full nodes.

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;
use std::ops::Range;
use futures03::{future, StreamExt as _, TryStreamExt as _};
use log::warn;
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId};
use rpc::{
	Result as RpcResult,
	futures::{stream, Future, Sink, Stream, future::result},
};

use api::Subscriptions;
use client::{
	Client, CallExecutor, BlockchainEvents, runtime_api::Metadata,
	backend::Backend, error::Result as ClientResult,
};
use primitives::{
	H256, Blake2Hasher, Bytes, storage::{well_known_keys, StorageKey, StorageData, StorageChangeSet},
};
use runtime_version::RuntimeVersion;
use state_machine::ExecutionStrategy;
use sr_primitives::{
	generic::BlockId,
	traits::{Block as BlockT, Header, NumberFor, ProvideRuntimeApi, SaturatedConversion},
};

use super::{StateBackend, error::{FutureResult, Error, Result}, client_err};

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
pub struct FullState<B, E, Block: BlockT, RA> {
	client: Arc<Client<B, E, Block, RA>>,
	subscriptions: Subscriptions,
}

impl<B, E, Block: BlockT, RA> FullState<B, E, Block, RA>
	where
		Block: BlockT<Hash=H256> + 'static,
		B: Backend<Block, Blake2Hasher> + Send + Sync + 'static,
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static + Clone,
{
	/// Create new state API backend for full nodes.
	pub fn new(client: Arc<Client<B, E, Block, RA>>, subscriptions: Subscriptions) -> Self {
		Self { client, subscriptions }
	}

	/// Returns given block hash or best block hash if None is passed.
	fn block_or_best(&self, hash: Option<Block::Hash>) -> ClientResult<Block::Hash> {
		crate::helpers::unwrap_or_else(|| Ok(self.client.info().chain.best_hash), hash)
	}

	/// Splits the `query_storage` block range into 'filtered' and 'unfiltered' subranges.
	/// Blocks that contain changes within filtered subrange could be filtered using changes tries.
	/// Blocks that contain changes within unfiltered subrange must be filtered manually.
	fn split_query_storage_range(
		&self,
		from: Block::Hash,
		to: Option<Block::Hash>
	) -> Result<QueryStorageRange<Block>> {
		let to = self.block_or_best(to).map_err(client_err)?;
		let from_hdr = self.client.header(&BlockId::hash(from)).map_err(client_err)?;
		let to_hdr = self.client.header(&BlockId::hash(to)).map_err(client_err)?;
		match (from_hdr, to_hdr) {
			(Some(ref from), Some(ref to)) if from.number() <= to.number() => {
				// check if we can get from `to` to `from` by going through parent_hashes.
				let from_number = *from.number();
				let blocks = {
					let mut blocks = vec![to.hash()];
					let mut last = to.clone();
					while *last.number() > from_number {
						let hdr = self.client
							.header(&BlockId::hash(*last.parent_hash()))
							.map_err(client_err)?;
						if let Some(hdr) = hdr {
							blocks.push(hdr.hash());
							last = hdr;
						} else {
							return Err(invalid_block_range(
								Some(from),
								Some(to),
								format!("Parent of {} ({}) not found", last.number(), last.hash()),
							))
						}
					}
					if last.hash() != from.hash() {
						return Err(invalid_block_range(
							Some(from),
							Some(to),
							format!("Expected to reach `from`, got {} ({})", last.number(), last.hash()),
						))
					}
					blocks.reverse();
					blocks
				};
				// check if we can filter blocks-with-changes from some (sub)range using changes tries
				let changes_trie_range = self.client
					.max_key_changes_range(from_number, BlockId::Hash(to.hash()))
					.map_err(client_err)?;
				let filtered_range_begin = changes_trie_range
					.map(|(begin, _)| (begin - from_number).saturated_into::<usize>());
				let (unfiltered_range, filtered_range) = split_range(blocks.len(), filtered_range_begin);
				Ok(QueryStorageRange {
					hashes: blocks,
					first_number: from_number,
					unfiltered_range,
					filtered_range,
				})
			},
			(from, to) => Err(
				invalid_block_range(from.as_ref(), to.as_ref(), "Invalid range or unknown block".into())
			),
		}
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
			let mut block_changes = StorageChangeSet { block: block_hash.clone(), changes: Vec::new() };
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

	/// Iterates through all blocks that are changing keys within range.filtered_range and collects these changes.
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
				BlockId::Hash(range.hashes[filtered_range.end - 1].clone())
			),
			None => return Ok(()),
		};
		let mut changes_map: BTreeMap<NumberFor<Block>, StorageChangeSet<Block::Hash>> = BTreeMap::new();
		for key in keys {
			let mut last_block = None;
			let mut last_value = last_values.get(key).cloned().unwrap_or_default();
			let key_changes = self.client.key_changes(begin, end, None, key).map_err(client_err)?;
			for (block, _) in key_changes.into_iter().rev() {
				if last_block == Some(block) {
					continue;
				}

				let block_hash = range.hashes[(block - range.first_number).saturated_into::<usize>()].clone();
				let id = BlockId::Hash(block_hash);
				let value_at_block = self.client.storage(&id, key).map_err(client_err)?;
				if last_value == value_at_block {
					continue;
				}

				changes_map.entry(block)
					.or_insert_with(|| StorageChangeSet { block: block_hash, changes: Vec::new() })
					.changes.push((key.clone(), value_at_block.clone()));
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
}

impl<B, E, Block, RA> StateBackend<B, E, Block, RA> for FullState<B, E, Block, RA>
	where
		Block: BlockT<Hash=H256> + 'static,
		B: Backend<Block, Blake2Hasher> + Send + Sync + 'static,
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static + Clone,
		RA: Send + Sync + 'static,
		Client<B, E, Block, RA>: ProvideRuntimeApi,
		<Client<B, E, Block, RA> as ProvideRuntimeApi>::Api: Metadata<Block>,
{
	fn call(
		&self,
		block: Option<Block::Hash>,
		method: String,
		call_data: Bytes,
	) -> FutureResult<Bytes> {
		Box::new(result(
			self.block_or_best(block)
				.and_then(|block|
					self
					.client
					.executor()
					.call(
						&BlockId::Hash(block),
						&method,
						&*call_data,
						ExecutionStrategy::NativeElseWasm,
						None,
					)
					.map(Into::into))
				.map_err(client_err)))
	}

	fn storage_keys(
		&self,
		block: Option<Block::Hash>,
		prefix: StorageKey,
	) -> FutureResult<Vec<StorageKey>> {
		Box::new(result(
			self.block_or_best(block)
				.and_then(|block| self.client.storage_keys(&BlockId::Hash(block), &prefix))
				.map_err(client_err)))
	}

	fn storage(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<StorageData>> {
		Box::new(result(
			self.block_or_best(block)
				.and_then(|block| self.client.storage(&BlockId::Hash(block), &key))
				.map_err(client_err)))
	}

	fn storage_hash(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<Block::Hash>> {
		Box::new(result(
			self.block_or_best(block)
				.and_then(|block| self.client.storage_hash(&BlockId::Hash(block), &key))
				.map_err(client_err)))
	}

	fn child_storage_keys(
		&self,
		block: Option<Block::Hash>,
		child_storage_key: StorageKey,
		prefix: StorageKey,
	) -> FutureResult<Vec<StorageKey>> {
		Box::new(result(
			self.block_or_best(block)
				.and_then(|block| self.client.child_storage_keys(&BlockId::Hash(block), &child_storage_key, &prefix))
				.map_err(client_err)))
	}

	fn child_storage(
		&self,
		block: Option<Block::Hash>,
		child_storage_key: StorageKey,
		key: StorageKey,
	) -> FutureResult<Option<StorageData>> {
		Box::new(result(
			self.block_or_best(block)
				.and_then(|block| self.client.child_storage(&BlockId::Hash(block), &child_storage_key, &key))
				.map_err(client_err)))
	}

	fn child_storage_hash(
		&self,
		block: Option<Block::Hash>,
		child_storage_key: StorageKey,
		key: StorageKey,
	) -> FutureResult<Option<Block::Hash>> {
		Box::new(result(
			self.block_or_best(block)
				.and_then(|block| self.client.child_storage_hash(&BlockId::Hash(block), &child_storage_key, &key))
				.map_err(client_err)))
	}

	fn metadata(&self, block: Option<Block::Hash>) -> FutureResult<Bytes> {
		Box::new(result(
			self.block_or_best(block)
				.and_then(|block| self.client.runtime_api().metadata(&BlockId::Hash(block)).map(Into::into))
				.map_err(client_err)))
	}

	fn runtime_version(&self, block: Option<Block::Hash>) -> FutureResult<RuntimeVersion> {
		Box::new(result(
			self.block_or_best(block)
				.and_then(|block| self.client.runtime_version_at(&BlockId::Hash(block)))
				.map_err(client_err)))
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
		Box::new(result(call_fn()))
	}

	fn subscribe_runtime_version(
		&self,
		_meta: crate::metadata::Metadata,
		subscriber: Subscriber<RuntimeVersion>,
	) {
		let stream = match self.client.storage_changes_notification_stream(
			Some(&[StorageKey(well_known_keys::CODE.to_vec())]),
			None,
		) {
			Ok(stream) => stream,
			Err(err) => {
				let _ = subscriber.reject(Error::from(client_err(err)).into());
				return;
			}
		};

		self.subscriptions.add(subscriber, |sink| {
			let version = self.runtime_version(None.into())
				.map_err(Into::into)
				.wait();

			let client = self.client.clone();
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

	fn unsubscribe_runtime_version(
		&self,
		_meta: Option<crate::metadata::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}

	fn subscribe_storage(
		&self,
		_meta: crate::metadata::Metadata,
		subscriber: Subscriber<StorageChangeSet<Block::Hash>>,
		keys: Option<Vec<StorageKey>>,
	) {
		let keys = Into::<Option<Vec<_>>>::into(keys);
		let stream = match self.client.storage_changes_notification_stream(
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
				let block = self.client.info().chain.best_hash;
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

		self.subscriptions.add(subscriber, |sink| {
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
		});
	}

	fn unsubscribe_storage(
		&self,
		_meta: Option<crate::metadata::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}
}

/// Splits passed range into two subranges where:
/// - first range has at least one element in it;
/// - second range (optionally) starts at given `middle` element.
pub(crate) fn split_range(size: usize, middle: Option<usize>) -> (Range<usize>, Option<Range<usize>>) {
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

fn invalid_block_range<H: Header>(from: Option<&H>, to: Option<&H>, reason: String) -> Error {
	let to_string = |x: Option<&H>| match x {
		None => "unknown hash".into(),
		Some(h) => format!("{} ({})", h.number(), h.hash()),
	};

	Error::InvalidBlockRange {
		from: to_string(from),
		to: to_string(to),
		details: reason,
	}
}
