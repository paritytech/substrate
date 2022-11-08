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
		subscription::{SubscriptionError, SubscriptionManagement},
	},
	SubscriptionTaskExecutor,
};
use codec::Encode;
use futures::{
	future::FutureExt,
	stream::{self, Stream, StreamExt},
};
use jsonrpsee::{
	core::{async_trait, RpcResult},
	types::{SubscriptionEmptyError, SubscriptionResult},
	SubscriptionSink,
};
use log::error;
use parking_lot::RwLock;
use sc_client_api::{
	Backend, BlockBackend, BlockImportNotification, BlockchainEvents, CallExecutor, ChildInfo,
	ExecutorProvider, FinalityNotification, StorageKey, StorageProvider,
};
use serde::Serialize;
use sp_api::CallApiAt;
use sp_blockchain::HeaderBackend;
use sp_core::{hexdisplay::HexDisplay, Bytes};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header},
};
use std::{marker::PhantomData, sync::Arc};

use futures::channel::oneshot;
use futures_util::future::Either;

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
	/// Best block reported by the RPC layer.
	/// This is used to determine if the previously reported best
	/// block is also pruned with the current finalization. In that
	/// case, the RPC should report a new best block before reporting
	/// the finalization event.
	best_block: Arc<RwLock<Option<Block::Hash>>>,
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
	) -> Self {
		let genesis_hash = format!("0x{}", hex::encode(genesis_hash));

		Self {
			client,
			backend,
			executor,
			subscriptions: Arc::new(SubscriptionManagement::new()),
			genesis_hash,
			best_block: Default::default(),
			_phantom: PhantomData,
		}
	}

	/// Accept the subscription and return the subscription ID on success.
	///
	/// Also keep track of the subscription ID internally.
	fn accept_subscription(
		&self,
		sink: &mut SubscriptionSink,
	) -> Result<String, SubscriptionEmptyError> {
		// The subscription must be accepted before it can provide a valid subscription ID.
		sink.accept()?;

		// TODO: Jsonrpsee needs release + merge in substrate
		// let sub_id = match sink.subscription_id() {
		// 	Some(id) => id,
		// 	// This can only happen if the subscription was not accepted.
		// 	None => {
		// 		let err = ErrorObject::owned(PARSE_ERROR_CODE, "invalid subscription ID", None);
		// 		sink.close(err);
		// 		return Err(SubscriptionEmptyError)
		// 	}
		// };
		// // Get the string representation for the subscription.
		// let sub_id = match serde_json::to_string(&sub_id) {
		// 	Ok(sub_id) => sub_id,
		// 	Err(err) => {
		// 		sink.close(err);
		// 		return Err(SubscriptionEmptyError)
		// 	},
		// };

		let sub_id: String = "A".into();
		Ok(sub_id)
	}
}

impl<BE, Block: BlockT, Client> ChainHead<BE, Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	BE: Backend<Block> + 'static,
	Client: HeaderBackend<Block> + CallApiAt<Block> + 'static,
{
	/// Generate the initial events reported by the RPC `follow` method.
	///
	/// This includes the "Initialized" event followed by the in-memory
	/// blocks via "NewBlock" and the "BestBlockChanged".
	fn generate_initial_events(
		&self,
		sub_id: &String,
		runtime_updates: bool,
	) -> Vec<FollowEvent<Block::Hash>> {
		// The initialized event is the first one sent.
		let finalized_block_hash = self.client.info().finalized_hash;
		let finalized_block_runtime = generate_runtime_event(
			&self.client,
			runtime_updates,
			&BlockId::Hash(finalized_block_hash),
			None,
		);

		let _ = self.subscriptions.pin_block(&sub_id, finalized_block_hash);

		let initialized_event = FollowEvent::Initialized(Initialized {
			finalized_block_hash,
			finalized_block_runtime,
			runtime_updates,
		});

		let mut initial_blocks = Vec::new();
		get_initial_blocks(&self.backend, finalized_block_hash, &mut initial_blocks);
		let sub_id = sub_id.clone();
		let mut in_memory_blocks: Vec<_> = std::iter::once(initialized_event)
			.chain(initial_blocks.into_iter().map(|(child, parent)| {
				let new_runtime = generate_runtime_event(
					&self.client,
					runtime_updates,
					&BlockId::Hash(child),
					Some(&BlockId::Hash(parent)),
				);

				let _ = self.subscriptions.pin_block(&sub_id, child);

				FollowEvent::NewBlock(NewBlock {
					block_hash: child,
					parent_block_hash: parent,
					new_runtime,
					runtime_updates,
				})
			}))
			.collect();

		// Generate a new best block event.
		let best_block_hash = self.client.info().best_hash;
		if best_block_hash != finalized_block_hash {
			let best_block = FollowEvent::BestBlockChanged(BestBlockChanged { best_block_hash });
			in_memory_blocks.push(best_block);
		};

		in_memory_blocks
	}
}

fn parse_hex_param(
	sink: &mut SubscriptionSink,
	param: String,
) -> Result<Vec<u8>, SubscriptionEmptyError> {
	match array_bytes::hex2bytes(&param) {
		Ok(bytes) => Ok(bytes),
		Err(_) => {
			let _ = sink.reject(ChainHeadRpcError::InvalidParam(param));
			Err(SubscriptionEmptyError)
		},
	}
}

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

fn get_initial_blocks<BE, Block>(
	backend: &Arc<BE>,
	parent_hash: Block::Hash,
	result: &mut Vec<(Block::Hash, Block::Hash)>,
) where
	Block: BlockT + 'static,
	BE: Backend<Block> + 'static,
{
	use sp_blockchain::Backend;

	match backend.blockchain().children(parent_hash) {
		Ok(blocks) =>
			for child_hash in blocks {
				result.push((child_hash, parent_hash));
				get_initial_blocks(backend, child_hash, result);
			},
		Err(_) => (),
	}
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

	loop {
		match futures_util::future::select(stream_item, stop_event).await {
			// Pipe from the event stream.
			Either::Left((Some(event), next_stop_event)) => {
				if let Err(_) = sink.send(&event) {
					// Sink failed to submit the event.
					let _ = sink.send(&FollowEvent::<String>::Stop);
					break
				}

				stream_item = stream.next();
				stop_event = next_stop_event;
			},
			// Event stream does not produce any more events or the stop
			// event was triggered.
			Either::Left((None, _)) | Either::Right((_, _)) => {
				let _ = sink.send(&FollowEvent::<String>::Stop);
				break
			},
		}
	}
}

/// Generate the "NewBlock" event and potentially the "BestBlockChanged" event for
/// every notification.
fn handle_import_blocks<Client, Block>(
	client: &Arc<Client>,
	subscriptions: &Arc<SubscriptionManagement<Block>>,
	best_block: &Arc<RwLock<Option<Block::Hash>>>,
	sub_id: &String,
	runtime_updates: bool,
	notification: BlockImportNotification<Block>,
) -> (FollowEvent<Block::Hash>, Option<FollowEvent<Block::Hash>>)
where
	Block: BlockT + 'static,
	Client: CallApiAt<Block> + 'static,
{
	let new_runtime = generate_runtime_event(
		&client,
		runtime_updates,
		&BlockId::Hash(notification.hash),
		Some(&BlockId::Hash(*notification.header.parent_hash())),
	);

	let _ = subscriptions.pin_block(&sub_id, notification.hash);

	// Note: `Block::Hash` will serialize to hexadecimal encoded string.
	let new_block = FollowEvent::NewBlock(NewBlock {
		block_hash: notification.hash,
		parent_block_hash: *notification.header.parent_hash(),
		new_runtime,
		runtime_updates,
	});

	if !notification.is_new_best {
		return (new_block, None)
	}

	// If this is the new best block, then we need to generate two events.
	let best_block_event =
		FollowEvent::BestBlockChanged(BestBlockChanged { best_block_hash: notification.hash });

	let mut best_block_cache = best_block.write();
	match *best_block_cache {
		Some(block_cache) => {
			// The RPC layer has not reported this block as best before.
			// Note: This handles the race with the finalized branch.
			if block_cache != notification.hash {
				*best_block_cache = Some(notification.hash);
				(new_block, Some(best_block_event))
			} else {
				(new_block, None)
			}
		},
		None => {
			*best_block_cache = Some(notification.hash);
			(new_block, Some(best_block_event))
		},
	}
}

/// Generate the "Finalized" event and potentially the "BestBlockChanged" for
/// every notification.
fn handle_finalized_blocks<Client, Block>(
	client: &Arc<Client>,
	subscriptions: &Arc<SubscriptionManagement<Block>>,
	best_block: &Arc<RwLock<Option<Block::Hash>>>,
	sub_id: &String,
	notification: FinalityNotification<Block>,
) -> (FollowEvent<Block::Hash>, Option<FollowEvent<Block::Hash>>)
where
	Block: BlockT + 'static,
	Client: HeaderBackend<Block> + 'static,
{
	// We might not receive all new blocks reports, also pin the block here.
	let _ = subscriptions.pin_block(&sub_id, notification.hash);

	// The tree route contains the exclusive path from the latest finalized block
	// to the block reported by the notification. Ensure the finalized block is
	// properly reported to that path.
	let mut finalized_block_hashes = notification.tree_route.iter().cloned().collect::<Vec<_>>();
	finalized_block_hashes.push(notification.hash);

	let pruned_block_hashes: Vec<_> = notification.stale_heads.iter().cloned().collect();

	let finalized_event = FollowEvent::Finalized(Finalized {
		finalized_block_hashes,
		pruned_block_hashes: pruned_block_hashes.clone(),
	});

	let mut best_block_cache = best_block.write();
	match *best_block_cache {
		Some(block_cache) => {
			// Check if the current best block is also reported as pruned.
			let reported_pruned = pruned_block_hashes.iter().find(|&&hash| hash == block_cache);
			if reported_pruned.is_none() {
				return (finalized_event, None)
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
				(finalized_event, None)
			} else {
				// The RPC needs to also submit a new best block changed before the
				// finalized event.
				*best_block_cache = Some(best_block_hash);
				let best_block_event =
					FollowEvent::BestBlockChanged(BestBlockChanged { best_block_hash });
				(finalized_event, Some(best_block_event))
			}
		},
		None => (finalized_event, None),
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
		let sub_id = self.accept_subscription(&mut sink)?;
		// Keep track of the subscription.
		let Ok(rx_stop) = self.subscriptions.insert_subscription(sub_id.clone()) else {
			// Inserting the subscription can only fail if the JsonRPSee
			// generated a duplicate subscription ID.
			let _ = sink.send(&FollowEvent::<Block::Hash>::Stop);
			return Ok(())
		};

		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();
		let best_reported_block = self.best_block.clone();
		let sub_id_import = sub_id.clone();

		let stream_import = self
			.client
			.import_notification_stream()
			.map(move |notification| {
				match handle_import_blocks(
					&client,
					&subscriptions,
					&best_reported_block,
					&sub_id_import,
					runtime_updates,
					notification,
				) {
					(new_block, None) => stream::iter(vec![new_block]),
					(new_block, Some(best_block)) => stream::iter(vec![new_block, best_block]),
				}
			})
			.flatten();

		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();
		let sub_id_finalized = sub_id.clone();
		let best_reported_block = self.best_block.clone();

		let stream_finalized = self
			.client
			.finality_notification_stream()
			.map(move |notification| {
				match handle_finalized_blocks(
					&client,
					&subscriptions,
					&best_reported_block,
					&sub_id_finalized,
					notification,
				) {
					(finalized_event, None) => stream::iter(vec![finalized_event]),
					(finalized_event, Some(best_block)) =>
						stream::iter(vec![best_block, finalized_event]),
				}
			})
			.flatten();

		let merged = tokio_stream::StreamExt::merge(stream_import, stream_finalized);

		let initial_events = self.generate_initial_events(&sub_id, runtime_updates);
		let stream = stream::iter(initial_events).chain(merged);

		let subscriptions = self.subscriptions.clone();
		let fut = async move {
			submit_events(&mut sink, stream.boxed(), rx_stop).await;
			// The client disconnected or called the unsubscribe method.
			subscriptions.remove_subscription(&sub_id);
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
			let res = match subscriptions.contains(&follow_subscription, &hash) {
				Err(SubscriptionError::InvalidBlock) => {
					let _ = sink.reject(ChainHeadRpcError::InvalidBlock);
					return
				},
				Err(SubscriptionError::InvalidSubId) => ChainHeadEvent::<String>::Disjoint,
				Ok(()) => match client.block(&BlockId::Hash(hash)) {
					Ok(Some(signed_block)) => {
						let extrinsics = signed_block.block.extrinsics();
						let result = format!("0x{}", HexDisplay::from(&extrinsics.encode()));
						ChainHeadEvent::Done(ChainHeadResult { result })
					},
					Ok(None) => {
						// The block's body was pruned. This subscription ID has become invalid.
						let _ = subscriptions.stop(&follow_subscription);
						ChainHeadEvent::<String>::Disjoint
					},
					Err(error) => ChainHeadEvent::Error(ErrorEvent { error: error.to_string() }),
				},
			};

			let stream = stream::once(async move { res });
			sink.pipe_from_stream(stream.boxed()).await;
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_header(
		&self,
		follow_subscription: String,
		hash: Block::Hash,
	) -> RpcResult<Option<String>> {
		match self.subscriptions.contains(&follow_subscription, &hash) {
			Err(SubscriptionError::InvalidBlock) =>
				return Err(ChainHeadRpcError::InvalidBlock.into()),
			Err(SubscriptionError::InvalidSubId) => return Ok(None),
			_ => (),
		};

		self.client
			.header(BlockId::Hash(hash))
			.map(|opt_header| opt_header.map(|h| format!("0x{}", HexDisplay::from(&h.encode()))))
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
			let res = match subscriptions.contains(&follow_subscription, &hash) {
				Err(SubscriptionError::InvalidBlock) => {
					let _ = sink.reject(ChainHeadRpcError::InvalidBlock);
					return
				},
				Err(SubscriptionError::InvalidSubId) => ChainHeadEvent::<Option<String>>::Disjoint,
				Ok(()) => {
					if let Some(child_key) = child_key {
						// The child key is provided, use the key to query the child trie.
						client
							.child_storage(&hash, &child_key, &key)
							.map(|result| {
								let result = result
									.map(|storage| format!("0x{}", HexDisplay::from(&storage.0)));
								ChainHeadEvent::Done(ChainHeadResult { result })
							})
							.unwrap_or_else(|error| {
								ChainHeadEvent::Error(ErrorEvent { error: error.to_string() })
							})
					} else {
						client
							.storage(&hash, &key)
							.map(|result| {
								let result = result
									.map(|storage| format!("0x{}", HexDisplay::from(&storage.0)));
								ChainHeadEvent::Done(ChainHeadResult { result })
							})
							.unwrap_or_else(|error| {
								ChainHeadEvent::Error(ErrorEvent { error: error.to_string() })
							})
					}
				},
			};

			let stream = stream::once(async move { res });
			sink.pipe_from_stream(stream.boxed()).await;
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
			let res = match subscriptions.contains(&follow_subscription, &hash) {
				// TODO: Reject subscription if runtime_updates is false.
				Err(SubscriptionError::InvalidBlock) => {
					let _ = sink.reject(ChainHeadRpcError::InvalidBlock);
					return
				},
				Err(SubscriptionError::InvalidSubId) => ChainHeadEvent::<String>::Disjoint,
				Ok(()) => {
					match client.executor().call(
						&BlockId::Hash(hash),
						&function,
						&call_parameters,
						client.execution_extensions().strategies().other,
						None,
					) {
						Ok(result) => {
							let result = format!("0x{}", HexDisplay::from(&result));
							ChainHeadEvent::Done(ChainHeadResult { result })
						},
						Err(error) =>
							ChainHeadEvent::Error(ErrorEvent { error: error.to_string() }),
					}
				},
			};

			let stream = stream::once(async move { res });
			sink.pipe_from_stream(stream.boxed()).await;
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_unpin(
		&self,
		follow_subscription: String,
		hash: Block::Hash,
	) -> RpcResult<()> {
		match self.subscriptions.unpin_block(&follow_subscription, &hash) {
			Err(SubscriptionError::InvalidBlock) => Err(ChainHeadRpcError::InvalidBlock.into()),
			_ => Ok(()),
		}
	}
}
