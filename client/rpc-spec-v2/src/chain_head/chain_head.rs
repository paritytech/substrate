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
	stream::{self, Stream, StreamExt},
};
use futures_util::future::Either;
use jsonrpsee::{
	core::{async_trait, RpcResult, SubscriptionCallbackError, SubscriptionResult},
	types::{SubscriptionId, ErrorObjectOwned},
	DisconnectError, PendingSubscriptionSink, SubscriptionMessage, SubscriptionSink,
};
use log::{debug, error};
use sc_client_api::{
	Backend, BlockBackend, BlockImportNotification, BlockchainEvents, CallExecutor, ChildInfo,
	ExecutorProvider, FinalityNotification, StorageKey, StorageProvider,
};
use serde::Serialize;
use sp_api::CallApiAt;
use sp_blockchain::{
	Backend as BlockChainBackend, Error as BlockChainError, HeaderBackend, HeaderMetadata,
};
use sp_core::{hexdisplay::HexDisplay, storage::well_known_keys, Bytes};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header},
};
use std::{marker::PhantomData, sync::Arc};

/// An API for chain head RPC calls.
pub struct ChainHead<BE, Block: BlockT, Client> {
	/// Substrate client.
	client: Arc<Client>,
	/// Backend of the chain.
	backend: Arc<BE>,
	/// Executor to spawn subscriptions.
	_executor: SubscriptionTaskExecutor,
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
			_executor: executor,
			subscriptions: Arc::new(SubscriptionManagement::new()),
			genesis_hash,
			max_pinned_blocks,
			_phantom: PhantomData,
		}
	}

	/// Accept the subscription and return the subscription ID on success.
	async fn accept_subscription(
		&self,
		pending: PendingSubscriptionSink,
	) -> Result<(SubscriptionSink, String), SubscriptionCallbackError> {
		// The subscription must be accepted before it can provide a valid subscription ID.
		let sink = pending.accept().await?;

		// Get the string representation for the subscription.
		let sub_id = match sink.subscription_id() {
			SubscriptionId::Num(num) => num.to_string(),
			SubscriptionId::Str(id) => id.into_owned().into(),
		};

		Ok((sink, sub_id))
	}
}

/// Generate the initial events reported by the RPC `follow` method.
///
/// This includes the "Initialized" event followed by the in-memory
/// blocks via "NewBlock" and the "BestBlockChanged".
fn generate_initial_events<Block, BE, Client>(
	client: &Arc<Client>,
	backend: &Arc<BE>,
	handle: &SubscriptionHandle<Block>,
	runtime_updates: bool,
) -> Result<Vec<FollowEvent<Block::Hash>>, SubscriptionManagementError>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	BE: Backend<Block> + 'static,
	Client: HeaderBackend<Block> + CallApiAt<Block> + 'static,
{
	// The initialized event is the first one sent.
	let finalized_block_hash = client.info().finalized_hash;
	handle.pin_block(finalized_block_hash)?;

	let finalized_block_runtime = generate_runtime_event(
		&client,
		runtime_updates,
		&BlockId::Hash(finalized_block_hash),
		None,
	);

	let initialized_event = FollowEvent::Initialized(Initialized {
		finalized_block_hash,
		finalized_block_runtime,
		runtime_updates,
	});

	let initial_blocks = get_initial_blocks(&backend, finalized_block_hash);
	let mut in_memory_blocks = Vec::with_capacity(initial_blocks.len() + 1);

	in_memory_blocks.push(initialized_event);
	for (child, parent) in initial_blocks.into_iter() {
		handle.pin_block(child)?;

		let new_runtime = generate_runtime_event(
			&client,
			runtime_updates,
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
	let best_block_hash = client.info().best_hash;
	if best_block_hash != finalized_block_hash {
		let best_block = FollowEvent::BestBlockChanged(BestBlockChanged { best_block_hash });
		in_memory_blocks.push(best_block);
	};

	Ok(in_memory_blocks)
}


struct MaybePendingSubscription(Option<PendingSubscriptionSink>);

impl MaybePendingSubscription {
	pub fn new(p: PendingSubscriptionSink) -> Self {
		Self(Some(p))
	}
	
	pub async fn accept(&mut self) -> Result<SubscriptionSink, SubscriptionCallbackError> {
		if let Some(p) = self.0.take() {
			p.accept().await.map_err(|_| SubscriptionCallbackError::None)
		} else {
			Err(SubscriptionCallbackError::None)
		}
	}

	pub async fn reject(&mut self, err: impl Into<ErrorObjectOwned>) {
		if let Some(p) = self.0.take() {
			let _ = p.reject(err).await;
		}
	}
}



/// Parse hex-encoded string parameter as raw bytes.
///
/// If the parsing fails, the subscription is rejected.
async fn parse_hex_param(
	pending: &mut MaybePendingSubscription,
	param: String,
) -> Result<Vec<u8>, SubscriptionCallbackError> {
	// Methods can accept empty parameters.
	if param.is_empty() {
		return Ok(Vec::new())
	}

	match array_bytes::hex2bytes(&param) {
		Ok(bytes) => Ok(bytes),
		Err(_) => {
			let _ = pending.reject(ChainHeadRpcError::InvalidParam(param)).await;
			Err(SubscriptionCallbackError::None)
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

/// Get the in-memory blocks of the client, starting from the provided finalized hash.
///
/// Returns a tuple of block hash with parent hash.
fn get_initial_blocks<BE, Block>(
	backend: &Arc<BE>,
	parent_hash: Block::Hash,
) -> Vec<(Block::Hash, Block::Hash)>
where
	Block: BlockT + 'static,
	BE: Backend<Block> + 'static,
{
	let mut result = Vec::new();
	let mut next_hash = Vec::new();
	next_hash.push(parent_hash);

	while let Some(parent_hash) = next_hash.pop() {
		let Ok(blocks) = backend.blockchain().children(parent_hash) else {
			continue
		};

		for child_hash in blocks {
			result.push((child_hash, parent_hash));
			next_hash.push(child_hash);
		}
	}

	result
}

/// Submit the events from the provided stream to the RPC client
/// for as long as the `rx_stop` event was not called.
async fn submit_events<EventStream, T>(
	sink: &mut SubscriptionSink,
	mut stream: EventStream,
	rx_stop: oneshot::Receiver<()>,
) where
	EventStream: Stream<Item = T> + Unpin,
	T: Serialize,
{
	let mut stream_item = stream.next();
	let mut stop_event = rx_stop;

	while let Either::Left((Some(event), next_stop_event)) =
		futures_util::future::select(stream_item, stop_event).await
	{
		let msg = SubscriptionMessage::from_json(&event).expect("serialize should work");
		match sink.send(msg).await {
			Ok(_) => {
				stream_item = stream.next();
				stop_event = next_stop_event;
			},
			// Client disconnected.
			Err(DisconnectError(_)) => return,
		}
	}

	let msg = SubscriptionMessage::from_json(&FollowEvent::<String>::Stop)
		.expect("serialize should work");
	let _ = sink.send(msg).await;
}

/// Generate the "NewBlock" event and potentially the "BestBlockChanged" event for
/// every notification.
fn handle_import_blocks<Client, Block>(
	client: &Arc<Client>,
	handle: &SubscriptionHandle<Block>,
	runtime_updates: bool,
	notification: BlockImportNotification<Block>,
) -> Result<(FollowEvent<Block::Hash>, Option<FollowEvent<Block::Hash>>), SubscriptionManagementError>
where
	Block: BlockT + 'static,
	Client: CallApiAt<Block> + 'static,
{
	handle.pin_block(notification.hash)?;

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
		return Ok((new_block, None))
	}

	// If this is the new best block, then we need to generate two events.
	let best_block_event =
		FollowEvent::BestBlockChanged(BestBlockChanged { best_block_hash: notification.hash });

	let mut best_block_cache = handle.best_block_write();
	match *best_block_cache {
		Some(block_cache) => {
			// The RPC layer has not reported this block as best before.
			// Note: This handles the race with the finalized branch.
			if block_cache != notification.hash {
				*best_block_cache = Some(notification.hash);
				Ok((new_block, Some(best_block_event)))
			} else {
				Ok((new_block, None))
			}
		},
		None => {
			*best_block_cache = Some(notification.hash);
			Ok((new_block, Some(best_block_event)))
		},
	}
}

/// Generate the "Finalized" event and potentially the "BestBlockChanged" for
/// every notification.
fn handle_finalized_blocks<Client, Block>(
	client: &Arc<Client>,
	handle: &SubscriptionHandle<Block>,
	notification: FinalityNotification<Block>,
) -> Result<(FollowEvent<Block::Hash>, Option<FollowEvent<Block::Hash>>), SubscriptionManagementError>
where
	Block: BlockT + 'static,
	Client: HeaderBackend<Block> + HeaderMetadata<Block, Error = BlockChainError> + 'static,
{
	let last_finalized = notification.hash;
	// We might not receive all new blocks reports, also pin the block here.
	handle.pin_block(last_finalized)?;

	// The tree route contains the exclusive path from the last finalized block
	// to the block reported by the notification. Ensure the finalized block is
	// properly reported to that path.
	let mut finalized_block_hashes = notification.tree_route.iter().cloned().collect::<Vec<_>>();
	finalized_block_hashes.push(last_finalized);

	let pruned_block_hashes: Vec<_> = notification.stale_heads.iter().cloned().collect();

	let finalized_event = FollowEvent::Finalized(Finalized {
		finalized_block_hashes,
		pruned_block_hashes: pruned_block_hashes.clone(),
	});

	let mut best_block_cache = handle.best_block_write();
	match *best_block_cache {
		Some(block_cache) => {
			// Check if the current best block is also reported as pruned.
			let reported_pruned = pruned_block_hashes.iter().find(|&&hash| hash == block_cache);
			if reported_pruned.is_none() {
				return Ok((finalized_event, None))
			}

			// The best block is reported as pruned. Therefore, we need to signal a new
			// best block event before submitting the finalized event.
			let best_block_hash = client.info().best_hash;
			if best_block_hash == block_cache {
				// The client doest not have any new information about the best block.
				// The information from `.info()` is updated from the DB as the last
				// step of the finalization and it should be up to date. Also, the
				// displaced nodes (list of nodes reported) should be reported with
				// an offset of 32 blocks for substrate.
				// If the info is outdated, there is nothing the RPC can do for now.
				error!(target: "rpc-spec-v2", "Client does not contain different best block");
				Ok((finalized_event, None))
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
				Ok((finalized_event, Some(best_block_event)))
			}
		},
		None => Ok((finalized_event, None)),
	}
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
	async fn chain_head_unstable_follow(
		&self,
		pending: PendingSubscriptionSink,
		runtime_updates: bool,
	) -> SubscriptionResult {
		let (mut sink, sub_id) = self.accept_subscription(pending).await?;

		// Keep track of the subscription.
		let Some((rx_stop, sub_handle)) = self.subscriptions.insert_subscription(sub_id.clone(), runtime_updates, self.max_pinned_blocks) else {
			// Inserting the subscription can only fail if the JsonRPSee
			// generated a duplicate subscription ID.
			debug!(target: "rpc-spec-v2", "[follow][id={:?}] Subscription already accepted", sub_id);
			let msg = SubscriptionMessage::from_json(&FollowEvent::<Block::Hash>::Stop).expect("serialize infallible; qed");
			let _ = sink.send(msg).await;
			return Ok(())
		};
		debug!(target: "rpc-spec-v2", "[follow][id={:?}] Subscription accepted", sub_id);

		let client = self.client.clone();
		let handle = sub_handle.clone();
		let subscription_id = sub_id.clone();

		let stream_import = self
			.client
			.import_notification_stream()
			.map(move |notification| {
				match handle_import_blocks(&client, &handle, runtime_updates, notification) {
					Ok((new_block, None)) => stream::iter(vec![new_block]),
					Ok((new_block, Some(best_block))) => stream::iter(vec![new_block, best_block]),
					Err(_) => {
						debug!(target: "rpc-spec-v2", "[follow][id={:?}] Failed to handle block import notification.", subscription_id);
						handle.stop();
						stream::iter(vec![])
					},
				}
			})
			.flatten();

		let client = self.client.clone();
		let handle = sub_handle.clone();
		let subscription_id = sub_id.clone();

		let stream_finalized = self
			.client
			.finality_notification_stream()
			.map(move |notification| {
				match handle_finalized_blocks(&client, &handle, notification) {
					Ok((finalized_event, None)) => stream::iter(vec![finalized_event]),
					Ok((finalized_event, Some(best_block))) =>
						stream::iter(vec![best_block, finalized_event]),
					Err(_) => {
						debug!(target: "rpc-spec-v2", "[follow][id={:?}] Failed to import finalized blocks", subscription_id);
						handle.stop();
						stream::iter(vec![])
					},
				}
			})
			.flatten();

		let merged = tokio_stream::StreamExt::merge(stream_import, stream_finalized);

		
			let Ok(initial_events) = generate_initial_events(&self.client, &self.backend, &sub_handle, runtime_updates) else {
				// Stop the subscription if we exceeded the maximum number of blocks pinned.
				debug!(target: "rpc-spec-v2", "[follow][id={:?}] Exceeded max pinned blocks from initial events", sub_id);
				let msg = SubscriptionMessage::from_json(&FollowEvent::<Block::Hash>::Stop).expect("serialize infallible; qed");
				let _ = sink.send(msg).await;
				return Ok(())
			};

			let stream = stream::iter(initial_events).chain(merged);

			submit_events(&mut sink, stream.boxed(), rx_stop).await;
			// The client disconnected or called the unsubscribe method.
			self.subscriptions.remove_subscription(&sub_id);
			debug!(target: "rpc-spec-v2", "[follow][id={:?}] Subscription removed", sub_id);



		Ok(())
	}

	async fn chain_head_unstable_body(
		&self,
		pending: PendingSubscriptionSink,
		follow_subscription: String,
		hash: Block::Hash,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();

		let Some(handle) = subscriptions.get_subscription(&follow_subscription) else {
			// Invalid invalid subscription ID.
			let msg = SubscriptionMessage::from_json(&ChainHeadEvent::<String>::Disjoint)?;
			let sink = pending.accept().await?;	
			let _ = sink.send(msg);
			return Err(SubscriptionCallbackError::None);
		};

		// Block is not part of the subscription.
		if !handle.contains_block(&hash) {
			let _ = pending.reject(ChainHeadRpcError::InvalidBlock).await;
			return Err(SubscriptionCallbackError::None)
		}

		let sink = pending.accept().await?;

		let event = match client.block(hash) {
			Ok(Some(signed_block)) => {
				let extrinsics = signed_block.block.extrinsics();
				let result = format!("0x{:?}", HexDisplay::from(&extrinsics.encode()));
				ChainHeadEvent::Done(ChainHeadResult { result })
			},
			Ok(None) => {
				// The block's body was pruned. This subscription ID has become invalid.
				debug!(target: "rpc-spec-v2", "[body][id={:?}] Stopping subscription because hash={:?} was pruned", follow_subscription, hash);
				handle.stop();
				ChainHeadEvent::<String>::Disjoint
			},
			Err(error) => ChainHeadEvent::Error(ErrorEvent { error: error.to_string() }),
		};
		let msg = SubscriptionMessage::from_json(&event).expect("serialize infallible; qed");
		let _ = sink.send(msg).await;

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

	async fn chain_head_unstable_storage(
		&self,
		pending: PendingSubscriptionSink,
		follow_subscription: String,
		hash: Block::Hash,
		key: String,
		child_key: Option<String>,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		
		let mut pending = MaybePendingSubscription::new(pending);
		let key = StorageKey(parse_hex_param(&mut pending, key).await?);

		let child_key = match child_key {
			Some(k) => Some(ChildInfo::new_default_from_vec(parse_hex_param(&mut pending, k).await?)),
			None => None,
		};

		let Some(handle) = self.subscriptions.get_subscription(&follow_subscription) else {
			let sink = pending.accept().await?;
			// Invalid invalid subscription ID.
			let _ = sink.send(SubscriptionMessage::from_json(&ChainHeadEvent::<String>::Disjoint)?).await;
			return Ok(());
		};

			// Block is not part of the subscription.
			if !handle.contains_block(&hash) {
				let _ = pending.reject(ChainHeadRpcError::InvalidBlock);
				return Ok(());
			}

			let sink = pending.accept().await?;

			// The child key is provided, use the key to query the child trie.
			if let Some(child_key) = child_key {
				// The child key must not be prefixed with ":child_storage:" nor
				// ":child_storage:default:".
				if well_known_keys::is_default_child_storage_key(child_key.storage_key()) ||
					well_known_keys::is_child_storage_key(child_key.storage_key())
				{
					let msg = SubscriptionMessage::from_json(&ChainHeadEvent::Done(ChainHeadResult { result: None::<String> }))?;
					let _ = sink
						.send(msg).await;
					return Ok(());
				}

				let res = self.client
					.child_storage(hash, &child_key, &key)
					.map(|result| {
						let result =
							result.map(|storage| format!("0x{:?}", HexDisplay::from(&storage.0)));
						ChainHeadEvent::Done(ChainHeadResult { result })
					})
					.unwrap_or_else(|error| {
						ChainHeadEvent::Error(ErrorEvent { error: error.to_string() })
					});
				let _ = sink.send(SubscriptionMessage::from_json(&res)?).await;
				return Ok(());
			}

			// The main key must not be prefixed with b":child_storage:" nor
			// b":child_storage:default:".
			if well_known_keys::is_default_child_storage_key(&key.0) ||
				well_known_keys::is_child_storage_key(&key.0)
			{
				let msg = SubscriptionMessage::from_json(&ChainHeadEvent::Done(ChainHeadResult { result: None::<String> }))?;
				let _ =
					sink.send(msg).await;
				return Ok(());
			}

			// Main root trie storage query.
			let res = self.client
				.storage(hash, &key)
				.map(|result| {
					let result =
						result.map(|storage| format!("0x{:?}", HexDisplay::from(&storage.0)));
					ChainHeadEvent::Done(ChainHeadResult { result })
				})
				.unwrap_or_else(|error| {
					ChainHeadEvent::Error(ErrorEvent { error: error.to_string() })
				});
			let _ = sink.send(SubscriptionMessage::from_json(&res)?).await;
		
	
		Ok(())
	}

	async fn chain_head_unstable_call(
		&self,
		pending: PendingSubscriptionSink,
		follow_subscription: String,
		hash: Block::Hash,
		function: String,
		call_parameters: String,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		let mut pending = MaybePendingSubscription::new(pending);
		let bytes = parse_hex_param(&mut pending, call_parameters).await?;
		let call_parameters = Bytes::from(bytes);


			let Some(handle) = self.subscriptions.get_subscription(&follow_subscription) else {
				// Invalid invalid subscription ID.
				let sink = pending.accept().await?;
				let _ = sink.send(SubscriptionMessage::from_json(&ChainHeadEvent::<String>::Disjoint)?).await;
				return Ok(());
			};

			// Block is not part of the subscription.
			if !handle.contains_block(&hash) {
				let _ = pending.reject(ChainHeadRpcError::InvalidBlock);
				return Ok(());
			}

			// Reject subscription if runtime_updates is false.
			if !handle.has_runtime_updates() {
				let _ = pending.reject(ChainHeadRpcError::InvalidParam(
					"The runtime updates flag must be set".into(),
				));
				return Ok(());
			}

			let sink = pending.accept().await?;

			let res = self.client
				.executor()
				.call(
					hash,
					&function,
					&call_parameters,
					self.client.execution_extensions().strategies().other,
				)
				.map(|result| {
					let result = format!("0x{:?}", HexDisplay::from(&result));
					ChainHeadEvent::Done(ChainHeadResult { result })
				})
				.unwrap_or_else(|error| {
					ChainHeadEvent::Error(ErrorEvent { error: error.to_string() })
				});

			let _ = sink.send(SubscriptionMessage::from_json(&res)?).await;
	
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
