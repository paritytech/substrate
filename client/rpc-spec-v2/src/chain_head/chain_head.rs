// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! API implementation for `chainHead`.

use crate::{
	chain_head::{
		api::ChainHeadApiServer,
		error::Error as ChainHeadRpcError,
		event::{
			BestBlockChanged, ChainHeadEvent, ChainHeadResult, ErrorEvent, Finalized, FollowEvent,
			Initialized, NetworkConfig, NewBlock, RuntimeEvent, RuntimeVersionEvent,
		},
		subscription::{SubscriptionHandle, SubscriptionManagement, SubscriptionManagementError},
	},
	SubscriptionTaskExecutor,
};
use codec::Encode;
use futures::{
	channel::oneshot,
	future::FutureExt,
	stream::{self, Stream, StreamExt},
};
use futures_util::future::Either;
use itertools::Itertools;
use jsonrpsee::{
	core::{async_trait, RpcResult},
	types::{SubscriptionEmptyError, SubscriptionId, SubscriptionResult},
	SubscriptionSink,
};
use log::{debug, error};
use sc_client_api::{
	Backend, BlockBackend, BlockImportNotification, BlockchainEvents, CallExecutor, ChildInfo,
	ExecutorProvider, FinalityNotification, StorageKey, StorageProvider,
};
use sp_api::CallApiAt;
use sp_blockchain::{
	Backend as BlockChainBackend, Error as BlockChainError, HeaderBackend, HeaderMetadata, Info,
};
use sp_core::{hexdisplay::HexDisplay, storage::well_known_keys, Bytes};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header},
};
use std::{collections::HashSet, marker::PhantomData, sync::Arc};

const LOG_TARGET: &str = "rpc-spec-v2";

/// An API for chain head RPC calls.
pub struct ChainHead<BE, Block: BlockT, Client> {
	/// Substrate client.
	client: Arc<Client>,
	/// Backend of the chain.
	backend: Arc<BE>,
	/// Executor to spawn subscriptions.
	executor: SubscriptionTaskExecutor,
	/// Keep track of the pinned blocks for each subscription.
	subscriptions: Arc<SubscriptionManagement<Block>>,
	/// The hexadecimal encoded hash of the genesis block.
	genesis_hash: String,
	/// The maximum number of pinned blocks allowed per connection.
	max_pinned_blocks: usize,
	/// Phantom member to pin the block type.
	_phantom: PhantomData<Block>,
}

impl<BE, Block: BlockT, Client> ChainHead<BE, Block, Client> {
	/// Create a new [`ChainHead`].
	pub fn new<GenesisHash: AsRef<[u8]>>(
		client: Arc<Client>,
		backend: Arc<BE>,
		executor: SubscriptionTaskExecutor,
		genesis_hash: GenesisHash,
		max_pinned_blocks: usize,
	) -> Self {
		let genesis_hash = format!("0x{:?}", HexDisplay::from(&genesis_hash.as_ref()));

		Self {
			client,
			backend,
			executor,
			subscriptions: Arc::new(SubscriptionManagement::new()),
			genesis_hash,
			max_pinned_blocks,
			_phantom: PhantomData,
		}
	}

	/// Accept the subscription and return the subscription ID on success.
	fn accept_subscription(
		&self,
		sink: &mut SubscriptionSink,
	) -> Result<String, SubscriptionEmptyError> {
		// The subscription must be accepted before it can provide a valid subscription ID.
		sink.accept()?;

		let Some(sub_id) = sink.subscription_id() else {
			// This can only happen if the subscription was not accepted.
			return Err(SubscriptionEmptyError)
		};

		// Get the string representation for the subscription.
		let sub_id = match sub_id {
			SubscriptionId::Num(num) => num.to_string(),
			SubscriptionId::Str(id) => id.into_owned().into(),
		};

		Ok(sub_id)
	}
}

/// Generate the initial events reported by the RPC `follow` method.
///
/// This includes the "Initialized" event followed by the in-memory
/// blocks via "NewBlock" and the "BestBlockChanged".
fn generate_initial_events<BE, Block, Client>(
	data: &mut FollowData<BE, Block, Client>,
) -> Result<(Vec<FollowEvent<Block::Hash>>, HashSet<Block::Hash>), SubscriptionManagementError>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	BE: Backend<Block> + 'static,
	Client: HeaderBackend<Block> + CallApiAt<Block> + 'static,
{
	let client = &data.client;
	let backend = &data.backend;
	let start_info = &data.start_info;
	let handle = &data.sub_handle;
	let runtime_updates = data.runtime_updates;

	let ret = get_initial_blocks_with_forks(backend, start_info)?;
	let initial_blocks = ret.finalized_block_descendants;

	// The initialized event is the first one sent.
	let finalized_block_hash = start_info.finalized_hash;
	handle.pin_block(finalized_block_hash)?;

	let finalized_block_runtime =
		generate_runtime_event(client, runtime_updates, &BlockId::Hash(finalized_block_hash), None);

	let initialized_event = FollowEvent::Initialized(Initialized {
		finalized_block_hash,
		finalized_block_runtime,
		runtime_updates,
	});

	let mut in_memory_blocks = Vec::with_capacity(initial_blocks.len() + 1);

	in_memory_blocks.push(initialized_event);
	for (child, parent) in initial_blocks.into_iter() {
		handle.pin_block(child)?;

		let new_runtime = generate_runtime_event(
			client,
			data.runtime_updates,
			&BlockId::Hash(child),
			Some(&BlockId::Hash(parent)),
		);

		let event = FollowEvent::NewBlock(NewBlock {
			block_hash: child,
			parent_block_hash: parent,
			new_runtime,
			runtime_updates,
		});

		in_memory_blocks.push(event);
	}

	// Generate a new best block event.
	let best_block_hash = start_info.best_hash;
	if best_block_hash != finalized_block_hash {
		let best_block = FollowEvent::BestBlockChanged(BestBlockChanged { best_block_hash });
		data.best_block_cache = Some(best_block_hash);
		in_memory_blocks.push(best_block);
	};

	Ok((in_memory_blocks, ret.pruned_forks))
}

/// Parse hex-encoded string parameter as raw bytes.
///
/// If the parsing fails, the subscription is rejected.
fn parse_hex_param(
	sink: &mut SubscriptionSink,
	param: String,
) -> Result<Vec<u8>, SubscriptionEmptyError> {
	// Methods can accept empty parameters.
	if param.is_empty() {
		return Ok(Default::default())
	}

	match array_bytes::hex2bytes(&param) {
		Ok(bytes) => Ok(bytes),
		Err(_) => {
			let _ = sink.reject(ChainHeadRpcError::InvalidParam(param));
			Err(SubscriptionEmptyError)
		},
	}
}

/// Conditionally generate the runtime event of the given block.
fn generate_runtime_event<Client, Block>(
	client: &Arc<Client>,
	runtime_updates: bool,
	block: &BlockId<Block>,
	parent: Option<&BlockId<Block>>,
) -> Option<RuntimeEvent>
where
	Block: BlockT + 'static,
	Client: CallApiAt<Block> + 'static,
{
	// No runtime versions should be reported.
	if !runtime_updates {
		return None
	}

	let block_rt = match client.runtime_version_at(block) {
		Ok(rt) => rt,
		Err(err) => return Some(err.into()),
	};

	let parent = match parent {
		Some(parent) => parent,
		// Nothing to compare against, always report.
		None => return Some(RuntimeEvent::Valid(RuntimeVersionEvent { spec: block_rt })),
	};

	let parent_rt = match client.runtime_version_at(parent) {
		Ok(rt) => rt,
		Err(err) => return Some(err.into()),
	};

	// Report the runtime version change.
	if block_rt != parent_rt {
		Some(RuntimeEvent::Valid(RuntimeVersionEvent { spec: block_rt }))
	} else {
		None
	}
}

/// Internal representation of the initial blocks that should be
/// reported or ignored by the chainHead.
#[derive(Clone, Debug)]
struct InitialBlocks<Block: BlockT> {
	/// Children of the latest finalized block, for which the `NewBlock`
	/// event must be generated.
	///
	/// It is a tuple of (block hash, parent hash).
	finalized_block_descendants: Vec<(Block::Hash, Block::Hash)>,
	/// Blocks that should not be reported as pruned by the `Finalized` event.
	///
	/// Substrate database will perform the pruning of height N at
	/// the finalization N + 1. We could have the following block tree
	/// when the user subscribes to the `follow` method:
	///   [A] - [A1] - [A2] - [A3]
	///                 ^^ finalized
	///       - [A1] - [B1]
	///
	/// When the A3 block is finalized, B1 is reported as pruned, however
	/// B1 was never reported as `NewBlock` (and as such was never pinned).
	/// This is because the `NewBlock` events are generated for children of
	/// the finalized hash.
	pruned_forks: HashSet<Block::Hash>,
}

/// Get the in-memory blocks of the client, starting from the provided finalized hash.
fn get_initial_blocks_with_forks<Block, BE>(
	backend: &Arc<BE>,
	info: &Info<Block>,
) -> Result<InitialBlocks<Block>, SubscriptionManagementError>
where
	Block: BlockT + 'static,
	BE: Backend<Block> + 'static,
{
	let blockchain = backend.blockchain();
	let leaves = blockchain
		.leaves()
		.map_err(|err| SubscriptionManagementError::Custom(err.to_string()))?;
	let finalized = info.finalized_hash;
	let mut pruned_forks = HashSet::new();
	let mut finalized_block_descendants = Vec::new();
	for leaf in leaves {
		let tree_route = sp_blockchain::tree_route(blockchain, finalized, leaf)
			.map_err(|err| SubscriptionManagementError::Custom(err.to_string()))?;

		let blocks = tree_route.enacted().iter().map(|block| block.hash);
		if !tree_route.retracted().is_empty() {
			pruned_forks.extend(blocks);
		} else {
			// Ensure a `NewBlock` event is generated for all children of the
			// finalized block. Describe the tree route as (child_node, parent_node)
			let parents = std::iter::once(finalized).chain(blocks.clone());
			finalized_block_descendants.extend(blocks.zip(parents));
		}
	}

	// Keep unique blocks.
	let finalized_block_descendants: Vec<_> =
		finalized_block_descendants.into_iter().unique().collect();

	Ok(InitialBlocks { finalized_block_descendants, pruned_forks })
}

/// Submit the events from the provided stream to the RPC client
/// for as long as the `rx_stop` event was not called.
async fn submit_events<EventStream, BE, Block, Client>(
	data: FollowData<BE, Block, Client>,
	mut stream: EventStream,
	mut to_ignore: HashSet<Block::Hash>,
	sub_id: String,
) where
	EventStream: Stream<Item = NotificationType<Block>> + Unpin,
	Block: BlockT + 'static,
	Client: CallApiAt<Block>
		+ HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = BlockChainError>
		+ 'static,
{
	let mut stream_item = stream.next();
	let mut stop_event = data.rx_stop;
	let mut sink = data.sink;
	let mut best_block_cache = data.best_block_cache;

	while let Either::Left((Some(event), next_stop_event)) =
		futures_util::future::select(stream_item, stop_event).await
	{
		let events = match event {
			NotificationType::InitialEvents(events) => Ok(events),
			NotificationType::NewBlock(notification) => handle_import_blocks(
				&data.client,
				&data.sub_handle,
				data.runtime_updates,
				notification,
				&mut best_block_cache,
			),
			NotificationType::Finalized(notification) => handle_finalized_blocks(
				&data.client,
				&data.sub_handle,
				notification,
				&mut to_ignore,
				&data.start_info,
				&mut best_block_cache,
			),
		};

		let events = match events {
			Ok(events) => events,
			Err(err) => {
				debug!(target: LOG_TARGET, "Failed to handle stream notification {:?}", err);
				break
			},
		};

		for event in events {
			match sink.send(&event) {
				// Submitted successfully.
				Ok(true) => continue,
				// Client disconnected.
				Ok(false) => return,
				Err(_) => {
					// Failed to submit event.
					break
				},
			}
		}

		stream_item = stream.next();
		stop_event = next_stop_event;
	}

	let _ = sink.send(&FollowEvent::<String>::Stop);
	data.subscriptions.remove_subscription(&sub_id);
	debug!(target: LOG_TARGET, "[follow][id={:?}] Subscription removed", sub_id);
}

/// Generate the "NewBlock" event and potentially the "BestBlockChanged" event for
/// every notification.
fn handle_import_blocks<Client, Block>(
	client: &Arc<Client>,
	handle: &SubscriptionHandle<Block>,
	runtime_updates: bool,
	notification: BlockImportNotification<Block>,
	best_block_cache: &mut Option<Block::Hash>,
) -> Result<Vec<FollowEvent<Block::Hash>>, SubscriptionManagementError>
where
	Block: BlockT + 'static,
	Client: CallApiAt<Block> + 'static,
{
	let is_new_pin = handle.pin_block(notification.hash)?;
	// TODO: Also check number >= init info
	if !is_new_pin {
		// The block was already pinned by the initial block event in `generate_initial_events`.
		return Ok(vec![])
	}

	let new_runtime = generate_runtime_event(
		&client,
		runtime_updates,
		&BlockId::Hash(notification.hash),
		Some(&BlockId::Hash(*notification.header.parent_hash())),
	);

	// Note: `Block::Hash` will serialize to hexadecimal encoded string.
	let new_block = FollowEvent::NewBlock(NewBlock {
		block_hash: notification.hash,
		parent_block_hash: *notification.header.parent_hash(),
		new_runtime,
		runtime_updates,
	});

	if !notification.is_new_best {
		return Ok(vec![new_block])
	}

	// If this is the new best block, then we need to generate two events.
	let best_block_event =
		FollowEvent::BestBlockChanged(BestBlockChanged { best_block_hash: notification.hash });

	match *best_block_cache {
		Some(block_cache) => {
			// The RPC layer has not reported this block as best before.
			// Note: This handles the race with the finalized branch.
			if block_cache != notification.hash {
				*best_block_cache = Some(notification.hash);
				Ok(vec![new_block, best_block_event])
			} else {
				Ok(vec![new_block])
			}
		},
		None => {
			*best_block_cache = Some(notification.hash);
			Ok(vec![new_block, best_block_event])
		},
	}
}

/// Generate the "Finalized" event and potentially the "BestBlockChanged" for
/// every notification.
fn handle_finalized_blocks<Client, Block>(
	client: &Arc<Client>,
	handle: &SubscriptionHandle<Block>,
	notification: FinalityNotification<Block>,
	to_ignore: &mut HashSet<Block::Hash>,
	start_info: &Info<Block>,
	best_block_cache: &mut Option<Block::Hash>,
) -> Result<Vec<FollowEvent<Block::Hash>>, SubscriptionManagementError>
where
	Block: BlockT + 'static,
	Client: HeaderBackend<Block> + HeaderMetadata<Block, Error = BlockChainError> + 'static,
{
	let last_finalized = notification.hash;
	let finalized_number = client.number(last_finalized.clone()).unwrap().unwrap();
	// Check if the finalized hash has been reported by the initial events.
	if finalized_number < start_info.finalized_number {
		return Ok(vec![])
	}

	// We might not receive all new blocks reports, also pin the block here.
	handle.pin_block(last_finalized)?;

	// The tree route contains the exclusive path from the last finalized block
	// to the block reported by the notification. Ensure the finalized block is
	// properly reported to that path.
	let mut finalized_block_hashes = notification.tree_route.iter().cloned().collect::<Vec<_>>();
	finalized_block_hashes.push(last_finalized);

	// Report all pruned blocks from the notification that are not
	// part of the `pruned_forks`.
	let pruned_block_hashes: Vec<_> = {
		notification
			.stale_heads
			.iter()
			.filter(|hash| !to_ignore.remove(&hash))
			.cloned()
			.collect()
	};

	let finalized_event =
		FollowEvent::Finalized(Finalized { finalized_block_hashes, pruned_block_hashes });

	let pruned_block_hashes: Vec<_> = notification.stale_heads.iter().cloned().collect();

	match *best_block_cache {
		Some(block_cache) => {
			// Check if the current best block is also reported as pruned.
			let reported_pruned = pruned_block_hashes.iter().find(|&&hash| hash == block_cache);
			if reported_pruned.is_none() {
				return Ok(vec![finalized_event])
			}

			// The best block is reported as pruned. Therefore, we need to signal a new
			// best block event before submitting the finalized event.
			let best_block_hash = client.info().best_hash;
			if best_block_hash == block_cache {
				// The client doest not have any new information about the best block.
				// The information from `.info()` is updated from the DB as the last
				// step of the finalization and it should be up to date.
				// If the info is outdated, there is nothing the RPC can do for now.
				error!(target: LOG_TARGET, "Client does not contain different best block");
				Ok(vec![finalized_event])
			} else {
				let ancestor = sp_blockchain::lowest_common_ancestor(
					&**client,
					last_finalized,
					best_block_hash,
				)
				.map_err(|_| {
					SubscriptionManagementError::Custom("Could not find common ancestor".into())
				})?;

				// The client's best block must be a descendent of the last finalized block.
				// In other words, the lowest common ancestor must be the last finalized block.
				if ancestor.hash != last_finalized {
					return Err(SubscriptionManagementError::Custom(
						"The finalized block is not an ancestor of the best block".into(),
					))
				}

				// The RPC needs to also submit a new best block changed before the
				// finalized event.
				*best_block_cache = Some(best_block_hash);
				let best_block_event =
					FollowEvent::BestBlockChanged(BestBlockChanged { best_block_hash });
				Ok(vec![best_block_event, finalized_event])
			}
		},
		None => Ok(vec![finalized_event]),
	}
}

/// Internal representation of a block notification.
enum NotificationType<Block: BlockT> {
	/// The initial events generated from the node's memory.
	InitialEvents(Vec<FollowEvent<Block::Hash>>),
	/// The new block notification obtained from `import_notification_stream`.
	NewBlock(BlockImportNotification<Block>),
	/// The finalized block notification obtained from `finality_notification_stream`.
	Finalized(FinalityNotification<Block>),
}

/// Data for the `follow` method to generate the block events.
struct FollowData<BE, Block: BlockT, Client> {
	client: Arc<Client>,
	backend: Arc<BE>,
	subscriptions: Arc<SubscriptionManagement<Block>>,
	sub_handle: SubscriptionHandle<Block>,
	rx_stop: oneshot::Receiver<()>,
	sink: SubscriptionSink,
	runtime_updates: bool,
	/// The starting point from which the blocks were generated from the
	/// node's memory.
	start_info: Info<Block>,
	/// The best reported block by this subscription.
	best_block_cache: Option<Block::Hash>,
}

#[async_trait]
impl<BE, Block, Client> ChainHeadApiServer<Block::Hash> for ChainHead<BE, Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	BE: Backend<Block> + 'static,
	Client: BlockBackend<Block>
		+ ExecutorProvider<Block>
		+ HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = BlockChainError>
		+ BlockchainEvents<Block>
		+ CallApiAt<Block>
		+ StorageProvider<Block, BE>
		+ 'static,
{
	fn chain_head_unstable_follow(
		&self,
		mut sink: SubscriptionSink,
		runtime_updates: bool,
	) -> SubscriptionResult {
		let sub_id = match self.accept_subscription(&mut sink) {
			Ok(sub_id) => sub_id,
			Err(err) => {
				sink.close(ChainHeadRpcError::InvalidSubscriptionID);
				return Err(err)
			},
		};

		// Keep track of the subscription.
		let Some((rx_stop, sub_handle)) = self.subscriptions.insert_subscription(sub_id.clone(), runtime_updates, self.max_pinned_blocks) else {
			// Inserting the subscription can only fail if the JsonRPSee
			// generated a duplicate subscription ID.
			debug!(target: LOG_TARGET, "[follow][id={:?}] Subscription already accepted", sub_id);
			let _ = sink.send(&FollowEvent::<Block::Hash>::Stop);
			return Ok(())
		};
		debug!(target: LOG_TARGET, "[follow][id={:?}] Subscription accepted", sub_id);

		// Register for the new block and finalized notifications.
		let stream_import = self
			.client
			.import_notification_stream()
			.map(|notification| NotificationType::NewBlock(notification));

		let stream_finalized = self
			.client
			.finality_notification_stream()
			.map(|notification| NotificationType::Finalized(notification));

		let merged = tokio_stream::StreamExt::merge(stream_import, stream_finalized);

		let subscriptions = self.subscriptions.clone();
		let backend = self.backend.clone();
		let client = self.client.clone();
		let fut = async move {
			let start_info = client.info();
			let mut follow_data = FollowData {
				client,
				backend,
				subscriptions,
				sub_handle,
				rx_stop,
				sink,
				runtime_updates,
				start_info,
				best_block_cache: None,
			};

			let (initial_events, pruned_forks) = match generate_initial_events(&mut follow_data) {
				Ok(blocks) => blocks,
				Err(err) => {
					debug!(
						target: LOG_TARGET,
						"[follow][id={:?}] Failed to generate the initial events {:?}", sub_id, err
					);
					let _ = follow_data.sink.send(&FollowEvent::<Block::Hash>::Stop);
					follow_data.subscriptions.remove_subscription(&sub_id);
					return
				},
			};

			let initial = NotificationType::InitialEvents(initial_events);
			let stream = stream::once(futures::future::ready(initial)).chain(merged);

			submit_events(follow_data, stream.boxed(), pruned_forks, sub_id).await;
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_body(
		&self,
		mut sink: SubscriptionSink,
		follow_subscription: String,
		hash: Block::Hash,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();

		let fut = async move {
			let Some(handle) = subscriptions.get_subscription(&follow_subscription) else {
				// Invalid invalid subscription ID.
				let _ = sink.send(&ChainHeadEvent::<String>::Disjoint);
				return
			};

			// Block is not part of the subscription.
			if !handle.contains_block(&hash) {
				let _ = sink.reject(ChainHeadRpcError::InvalidBlock);
				return
			}

			let event = match client.block(hash) {
				Ok(Some(signed_block)) => {
					let extrinsics = signed_block.block.extrinsics();
					let result = format!("0x{:?}", HexDisplay::from(&extrinsics.encode()));
					ChainHeadEvent::Done(ChainHeadResult { result })
				},
				Ok(None) => {
					// The block's body was pruned. This subscription ID has become invalid.
					debug!(
						target: LOG_TARGET,
						"[body][id={:?}] Stopping subscription because hash={:?} was pruned",
						follow_subscription,
						hash
					);
					handle.stop();
					ChainHeadEvent::<String>::Disjoint
				},
				Err(error) => ChainHeadEvent::Error(ErrorEvent { error: error.to_string() }),
			};
			let _ = sink.send(&event);
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_header(
		&self,
		follow_subscription: String,
		hash: Block::Hash,
	) -> RpcResult<Option<String>> {
		let Some(handle) = self.subscriptions.get_subscription(&follow_subscription) else {
			// Invalid invalid subscription ID.
			return Ok(None)
		};

		// Block is not part of the subscription.
		if !handle.contains_block(&hash) {
			return Err(ChainHeadRpcError::InvalidBlock.into())
		}

		self.client
			.header(hash)
			.map(|opt_header| opt_header.map(|h| format!("0x{:?}", HexDisplay::from(&h.encode()))))
			.map_err(ChainHeadRpcError::FetchBlockHeader)
			.map_err(Into::into)
	}

	fn chain_head_unstable_genesis_hash(&self) -> RpcResult<String> {
		Ok(self.genesis_hash.clone())
	}

	fn chain_head_unstable_storage(
		&self,
		mut sink: SubscriptionSink,
		follow_subscription: String,
		hash: Block::Hash,
		key: String,
		child_key: Option<String>,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		let key = StorageKey(parse_hex_param(&mut sink, key)?);

		let child_key = child_key
			.map(|child_key| parse_hex_param(&mut sink, child_key))
			.transpose()?
			.map(ChildInfo::new_default_from_vec);

		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();

		let fut = async move {
			let Some(handle) = subscriptions.get_subscription(&follow_subscription) else {
				// Invalid invalid subscription ID.
				let _ = sink.send(&ChainHeadEvent::<String>::Disjoint);
				return
			};

			// Block is not part of the subscription.
			if !handle.contains_block(&hash) {
				let _ = sink.reject(ChainHeadRpcError::InvalidBlock);
				return
			}

			// The child key is provided, use the key to query the child trie.
			if let Some(child_key) = child_key {
				// The child key must not be prefixed with ":child_storage:" nor
				// ":child_storage:default:".
				if well_known_keys::is_default_child_storage_key(child_key.storage_key()) ||
					well_known_keys::is_child_storage_key(child_key.storage_key())
				{
					let _ = sink
						.send(&ChainHeadEvent::Done(ChainHeadResult { result: None::<String> }));
					return
				}

				let res = client
					.child_storage(hash, &child_key, &key)
					.map(|result| {
						let result =
							result.map(|storage| format!("0x{:?}", HexDisplay::from(&storage.0)));
						ChainHeadEvent::Done(ChainHeadResult { result })
					})
					.unwrap_or_else(|error| {
						ChainHeadEvent::Error(ErrorEvent { error: error.to_string() })
					});
				let _ = sink.send(&res);
				return
			}

			// The main key must not be prefixed with b":child_storage:" nor
			// b":child_storage:default:".
			if well_known_keys::is_default_child_storage_key(&key.0) ||
				well_known_keys::is_child_storage_key(&key.0)
			{
				let _ =
					sink.send(&ChainHeadEvent::Done(ChainHeadResult { result: None::<String> }));
				return
			}

			// Main root trie storage query.
			let res = client
				.storage(hash, &key)
				.map(|result| {
					let result =
						result.map(|storage| format!("0x{:?}", HexDisplay::from(&storage.0)));
					ChainHeadEvent::Done(ChainHeadResult { result })
				})
				.unwrap_or_else(|error| {
					ChainHeadEvent::Error(ErrorEvent { error: error.to_string() })
				});
			let _ = sink.send(&res);
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_call(
		&self,
		mut sink: SubscriptionSink,
		follow_subscription: String,
		hash: Block::Hash,
		function: String,
		call_parameters: String,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		let call_parameters = Bytes::from(parse_hex_param(&mut sink, call_parameters)?);

		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();

		let fut = async move {
			let Some(handle) = subscriptions.get_subscription(&follow_subscription) else {
				// Invalid invalid subscription ID.
				let _ = sink.send(&ChainHeadEvent::<String>::Disjoint);
				return
			};

			// Block is not part of the subscription.
			if !handle.contains_block(&hash) {
				let _ = sink.reject(ChainHeadRpcError::InvalidBlock);
				return
			}

			// Reject subscription if runtime_updates is false.
			if !handle.has_runtime_updates() {
				let _ = sink.reject(ChainHeadRpcError::InvalidParam(
					"The runtime updates flag must be set".into(),
				));
				return
			}

			let res = client
				.executor()
				.call(
					hash,
					&function,
					&call_parameters,
					client.execution_extensions().strategies().other,
				)
				.map(|result| {
					let result = format!("0x{:?}", HexDisplay::from(&result));
					ChainHeadEvent::Done(ChainHeadResult { result })
				})
				.unwrap_or_else(|error| {
					ChainHeadEvent::Error(ErrorEvent { error: error.to_string() })
				});

			let _ = sink.send(&res);
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_unpin(
		&self,
		follow_subscription: String,
		hash: Block::Hash,
	) -> RpcResult<()> {
		let Some(handle) = self.subscriptions.get_subscription(&follow_subscription) else {
			// Invalid invalid subscription ID.
			return Ok(())
		};

		if !handle.unpin_block(&hash) {
			return Err(ChainHeadRpcError::InvalidBlock.into())
		}

		Ok(())
	}
}
