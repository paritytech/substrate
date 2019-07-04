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

pub mod error;

#[cfg(test)]
mod tests;

use std::{
	collections::{BTreeMap, HashMap},
	ops::Range,
	sync::Arc,
};

use client::{self, Client, CallExecutor, BlockchainEvents, runtime_api::Metadata};
use crate::rpc::Result as RpcResult;
use crate::rpc::futures::{stream, Future, Sink, Stream};
use crate::subscriptions::Subscriptions;
use jsonrpc_derive::rpc;
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId};
use log::{warn, trace};
use primitives::hexdisplay::HexDisplay;
use primitives::storage::{self, StorageKey, StorageData, StorageChangeSet};
use primitives::{H256, Blake2Hasher, Bytes};
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{
	Block as BlockT, Header, ProvideRuntimeApi, NumberFor,
	SaturatedConversion
};
use runtime_version::RuntimeVersion;
use self::error::Result;
use state_machine::{self, ExecutionStrategy};

pub use self::gen_client::Client as StateClient;

/// Substrate state API
#[rpc]
pub trait StateApi<Hash> {
	/// RPC Metadata
	type Metadata;

	/// Call a contract at a block's state.
	#[rpc(name = "state_call", alias("state_callAt"))]
	fn call(&self, name: String, bytes: Bytes, hash: Option<Hash>) -> Result<Bytes>;

	/// Returns the keys with prefix, leave empty to get all the keys
	#[rpc(name = "state_getKeys")]
	fn storage_keys(&self, prefix: StorageKey, hash: Option<Hash>) -> Result<Vec<StorageKey>>;

	/// Returns a storage entry at a specific block's state.
	#[rpc(name = "state_getStorage", alias("state_getStorageAt"))]
	fn storage(&self, key: StorageKey, hash: Option<Hash>) -> Result<Option<StorageData>>;

	/// Returns the hash of a storage entry at a block's state.
	#[rpc(name = "state_getStorageHash", alias("state_getStorageHashAt"))]
	fn storage_hash(&self, key: StorageKey, hash: Option<Hash>) -> Result<Option<Hash>>;

	/// Returns the size of a storage entry at a block's state.
	#[rpc(name = "state_getStorageSize", alias("state_getStorageSizeAt"))]
	fn storage_size(&self, key: StorageKey, hash: Option<Hash>) -> Result<Option<u64>>;

	/// Returns the keys with prefix from a child storage, leave empty to get all the keys
	#[rpc(name = "state_getChildKeys")]
	fn child_storage_keys(
		&self,
		child_storage_key: StorageKey,
		prefix: StorageKey,
		hash: Option<Hash>
	) -> Result<Vec<StorageKey>>;

	/// Returns a child storage entry at a specific block's state.
	#[rpc(name = "state_getChildStorage")]
	fn child_storage(
		&self,
		child_storage_key: StorageKey,
		key: StorageKey,
		hash: Option<Hash>
	) -> Result<Option<StorageData>>;

	/// Returns the hash of a child storage entry at a block's state.
	#[rpc(name = "state_getChildStorageHash")]
	fn child_storage_hash(
		&self,
		child_storage_key: StorageKey,
		key: StorageKey,
		hash: Option<Hash>
	) -> Result<Option<Hash>>;

	/// Returns the size of a child storage entry at a block's state.
	#[rpc(name = "state_getChildStorageSize")]
	fn child_storage_size(
		&self,
		child_storage_key: StorageKey,
		key: StorageKey,
		hash: Option<Hash>
	) -> Result<Option<u64>>;

	/// Returns the runtime metadata as an opaque blob.
	#[rpc(name = "state_getMetadata")]
	fn metadata(&self, hash: Option<Hash>) -> Result<Bytes>;

	/// Get the runtime version.
	#[rpc(name = "state_getRuntimeVersion", alias("chain_getRuntimeVersion"))]
	fn runtime_version(&self, hash: Option<Hash>) -> Result<RuntimeVersion>;

	/// Query historical storage entries (by key) starting from a block given as the second parameter.
	///
	/// NOTE This first returned result contains the initial state of storage for all keys.
	/// Subsequent values in the vector represent changes to the previous state (diffs).
	#[rpc(name = "state_queryStorage")]
	fn query_storage(
		&self,
		keys: Vec<StorageKey>,
		block: Hash,
		hash: Option<Hash>
	) -> Result<Vec<StorageChangeSet<Hash>>>;

	/// New runtime version subscription
	#[pubsub(
		subscription = "state_runtimeVersion",
		subscribe,
		name = "state_subscribeRuntimeVersion",
		alias("chain_subscribeRuntimeVersion")
	)]
	fn subscribe_runtime_version(&self, metadata: Self::Metadata, subscriber: Subscriber<RuntimeVersion>);

	/// Unsubscribe from runtime version subscription
	#[pubsub(
		subscription = "state_runtimeVersion",
		unsubscribe,
		name = "state_unsubscribeRuntimeVersion",
		alias("chain_unsubscribeRuntimeVersion")
	)]
	fn unsubscribe_runtime_version(&self, metadata: Option<Self::Metadata>, id: SubscriptionId) -> RpcResult<bool>;

	/// New storage subscription
	#[pubsub(subscription = "state_storage", subscribe, name = "state_subscribeStorage")]
	fn subscribe_storage(
		&self, metadata: Self::Metadata, subscriber: Subscriber<StorageChangeSet<Hash>>, keys: Option<Vec<StorageKey>>
	);

	/// Unsubscribe from storage subscription
	#[pubsub(subscription = "state_storage", unsubscribe, name = "state_unsubscribeStorage")]
	fn unsubscribe_storage(
		&self, metadata: Option<Self::Metadata>, id: SubscriptionId
	) -> RpcResult<bool>;
}

/// State API with subscriptions support.
pub struct State<B, E, Block: BlockT, RA> {
	/// Substrate client.
	client: Arc<Client<B, E, Block, RA>>,
	/// Current subscriptions.
	subscriptions: Subscriptions,
}

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

impl<B, E, Block: BlockT, RA> State<B, E, Block, RA> where
	Block: BlockT<Hash=H256>,
	B: client::backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
{
	/// Create new State API RPC handler.
	pub fn new(client: Arc<Client<B, E, Block, RA>>, subscriptions: Subscriptions) -> Self {
		Self {
			client,
			subscriptions,
		}
	}

	/// Splits the `query_storage` block range into 'filtered' and 'unfiltered' subranges.
	/// Blocks that contain changes within filtered subrange could be filtered using changes tries.
	/// Blocks that contain changes within unfiltered subrange must be filtered manually.
	fn split_query_storage_range(
		&self,
		from: Block::Hash,
		to: Option<Block::Hash>
	) -> Result<QueryStorageRange<Block>> {
		let to = self.unwrap_or_best(to)?;
		let from_hdr = self.client.header(&BlockId::hash(from))?;
		let to_hdr = self.client.header(&BlockId::hash(to))?;
		match (from_hdr, to_hdr) {
			(Some(ref from), Some(ref to)) if from.number() <= to.number() => {
				// check if we can get from `to` to `from` by going through parent_hashes.
				let from_number = *from.number();
				let blocks = {
					let mut blocks = vec![to.hash()];
					let mut last = to.clone();
					while *last.number() > from_number {
						if let Some(hdr) = self.client.header(&BlockId::hash(*last.parent_hash()))? {
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
				let changes_trie_range = self.client.max_key_changes_range(from_number, BlockId::Hash(to.hash()))?;
				let filtered_range_begin = changes_trie_range.map(|(begin, _)| (begin - from_number).saturated_into::<usize>());
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
					let curr_data = self.client.storage(&id, key)?;
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
			for (block, _) in self.client.key_changes(begin, end, key)?.into_iter().rev() {
				if last_block == Some(block) {
					continue;
				}

				let block_hash = range.hashes[(block - range.first_number).saturated_into::<usize>()].clone();
				let id = BlockId::Hash(block_hash);
				let value_at_block = self.client.storage(&id, key)?;
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

impl<B, E, Block, RA> State<B, E, Block, RA> where
	Block: BlockT<Hash=H256>,
	B: client::backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
{
	fn unwrap_or_best(&self, hash: Option<Block::Hash>) -> Result<Block::Hash> {
		crate::helpers::unwrap_or_else(|| Ok(self.client.info().chain.best_hash), hash)
	}
}

impl<B, E, Block, RA> StateApi<Block::Hash> for State<B, E, Block, RA> where
	Block: BlockT<Hash=H256> + 'static,
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static + Clone,
	RA: Send + Sync + 'static,
	Client<B, E, Block, RA>: ProvideRuntimeApi,
	<Client<B, E, Block, RA> as ProvideRuntimeApi>::Api: Metadata<Block>
{
	type Metadata = crate::metadata::Metadata;

	fn call(&self, method: String, data: Bytes, block: Option<Block::Hash>) -> Result<Bytes> {
		let block = self.unwrap_or_best(block)?;
		trace!(target: "rpc", "Calling runtime at {:?} for method {} ({})", block, method, HexDisplay::from(&data.0));
		let return_data = self.client
			.executor()
			.call(
				&BlockId::Hash(block),
				&method, &data.0, ExecutionStrategy::NativeElseWasm, state_machine::NeverOffchainExt::new(),
			)?;
		Ok(Bytes(return_data))
	}

	fn storage_keys(&self, key_prefix: StorageKey, block: Option<Block::Hash>) -> Result<Vec<StorageKey>> {
		let block = self.unwrap_or_best(block)?;
		trace!(target: "rpc", "Querying storage keys at {:?}", block);
		Ok(self.client.storage_keys(&BlockId::Hash(block), &key_prefix)?)
	}

	fn storage(&self, key: StorageKey, block: Option<Block::Hash>) -> Result<Option<StorageData>> {
		let block = self.unwrap_or_best(block)?;
		trace!(target: "rpc", "Querying storage at {:?} for key {}", block, HexDisplay::from(&key.0));
		Ok(self.client.storage(&BlockId::Hash(block), &key)?)
	}

	fn storage_hash(&self, key: StorageKey, block: Option<Block::Hash>) -> Result<Option<Block::Hash>> {
		let block = self.unwrap_or_best(block)?;
		trace!(target: "rpc", "Querying storage hash at {:?} for key {}", block, HexDisplay::from(&key.0));
		Ok(self.client.storage_hash(&BlockId::Hash(block), &key)?)
	}

	fn storage_size(&self, key: StorageKey, block: Option<Block::Hash>) -> Result<Option<u64>> {
		Ok(self.storage(key, block)?.map(|x| x.0.len() as u64))
	}

	fn child_storage(
		&self,
		child_storage_key: StorageKey,
		key: StorageKey,
		block: Option<Block::Hash>
	) -> Result<Option<StorageData>> {
		let block = self.unwrap_or_best(block)?;
		trace!(target: "rpc", "Querying child storage at {:?} for key {}", block, HexDisplay::from(&key.0));
		Ok(self.client.child_storage(&BlockId::Hash(block), &child_storage_key, &key)?)
	}

	fn child_storage_keys(
		&self,
		child_storage_key: StorageKey,
		key_prefix: StorageKey,
		block: Option<Block::Hash>
	) -> Result<Vec<StorageKey>> {
		let block = self.unwrap_or_best(block)?;
		trace!(target: "rpc", "Querying child storage keys at {:?}", block);
		Ok(self.client.child_storage_keys(&BlockId::Hash(block), &child_storage_key, &key_prefix)?)
	}

	fn child_storage_hash(
		&self,
		child_storage_key: StorageKey,
		key: StorageKey,
		block: Option<Block::Hash>
	) -> Result<Option<Block::Hash>> {
		let block = self.unwrap_or_best(block)?;
		trace!(
			target: "rpc", "Querying child storage hash at {:?} for key {}",
			block,
			HexDisplay::from(&key.0),
		);
		Ok(self.client.child_storage_hash(&BlockId::Hash(block), &child_storage_key, &key)?)
	}

	fn child_storage_size(
		&self,
		child_storage_key: StorageKey,
		key: StorageKey,
		block: Option<Block::Hash>
	) -> Result<Option<u64>> {
		Ok(self.child_storage(child_storage_key, key, block)?.map(|x| x.0.len() as u64))
	}

	fn metadata(&self, block: Option<Block::Hash>) -> Result<Bytes> {
		let block = self.unwrap_or_best(block)?;
		self.client.runtime_api().metadata(&BlockId::Hash(block)).map(Into::into).map_err(Into::into)
	}

	fn query_storage(
		&self,
		keys: Vec<StorageKey>,
		from: Block::Hash,
		to: Option<Block::Hash>
	) -> Result<Vec<StorageChangeSet<Block::Hash>>> {
		let range = self.split_query_storage_range(from, to)?;
		let mut changes = Vec::new();
		let mut last_values = HashMap::new();
		self.query_storage_unfiltered(&range, &keys, &mut last_values, &mut changes)?;
		self.query_storage_filtered(&range, &keys, &last_values, &mut changes)?;
		Ok(changes)
	}

	fn subscribe_storage(
		&self,
		_meta: Self::Metadata,
		subscriber: Subscriber<StorageChangeSet<Block::Hash>>,
		keys: Option<Vec<StorageKey>>
	) {
		let keys = Into::<Option<Vec<_>>>::into(keys);
		let stream = match self.client.storage_changes_notification_stream(
			keys.as_ref().map(|x| &**x),
			None
		) {
			Ok(stream) => stream,
			Err(err) => {
				let _ = subscriber.reject(error::Error::from(err).into());
				return;
			},
		};

		// initial values
		let initial = stream::iter_result(keys
			.map(|keys| {
				let block = self.client.info().chain.best_hash;
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
					changes: changes.iter()
						.filter_map(|(o_sk, k, v)| if o_sk.is_none() {
							Some((k.clone(),v.cloned()))
						} else { None }).collect(),
				}));

			sink
				.sink_map_err(|e| warn!("Error sending notifications: {:?}", e))
				.send_all(initial.chain(stream))
				// we ignore the resulting Stream (if the first stream is over we are unsubscribed)
				.map(|_| ())
		})
	}

	fn unsubscribe_storage(&self, _meta: Option<Self::Metadata>, id: SubscriptionId) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}

	fn runtime_version(&self, at: Option<Block::Hash>) -> Result<RuntimeVersion> {
		let at = self.unwrap_or_best(at)?;
		Ok(self.client.runtime_version_at(&BlockId::Hash(at))?)
	}

	fn subscribe_runtime_version(&self, _meta: Self::Metadata, subscriber: Subscriber<RuntimeVersion>) {
		let stream = match self.client.storage_changes_notification_stream(
			Some(&[StorageKey(storage::well_known_keys::CODE.to_vec())]),
			None,
		) {
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
					let info = client.info();
					let version = client
						.runtime_version_at(&BlockId::hash(info.chain.best_hash))
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

	fn unsubscribe_runtime_version(&self, _meta: Option<Self::Metadata>, id: SubscriptionId) -> RpcResult<bool> {
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

fn invalid_block_range<H: Header>(from: Option<&H>, to: Option<&H>, reason: String) -> error::Error {
	let to_string = |x: Option<&H>| match x {
		None => "unknown hash".into(),
		Some(h) => format!("{} ({})", h.number(), h.hash()),
	};

	error::Error::InvalidBlockRange {
		from: to_string(from),
		to: to_string(to),
		details: reason,
	}
}
