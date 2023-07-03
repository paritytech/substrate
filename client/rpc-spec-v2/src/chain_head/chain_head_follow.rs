// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Implementation of the `chainHead_follow` method.

use crate::chain_head::{
	chain_head::LOG_TARGET,
	event::{
		BestBlockChanged, Finalized, FollowEvent, Initialized, NewBlock, RuntimeEvent,
		RuntimeVersionEvent,
	},
	subscription::{SubscriptionManagement, SubscriptionManagementError},
};
use futures::{
	channel::oneshot,
	stream::{self, Stream, StreamExt},
};
use futures_util::future::Either;
use jsonrpsee::SubscriptionSink;
use log::{debug, error};
use sc_client_api::{
	Backend, BlockBackend, BlockImportNotification, BlockchainEvents, FinalityNotification,
};
use sp_api::CallApiAt;
use sp_blockchain::{
	Backend as BlockChainBackend, Error as BlockChainError, HeaderBackend, HeaderMetadata, Info,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use std::{collections::HashSet, sync::Arc};

/// Generates the events of the `chainHead_follow` method.
pub struct ChainHeadFollower<BE: Backend<Block>, Block: BlockT, Client> {
	/// Substrate client.
	client: Arc<Client>,
	/// Backend of the chain.
	backend: Arc<BE>,
	/// Subscriptions handle.
	sub_handle: Arc<SubscriptionManagement<Block, BE>>,
	/// Subscription was started with the runtime updates flag.
	with_runtime: bool,
	/// Subscription ID.
	sub_id: String,
	/// The best reported block by this subscription.
	best_block_cache: Option<Block::Hash>,
}

impl<BE: Backend<Block>, Block: BlockT, Client> ChainHeadFollower<BE, Block, Client> {
	/// Create a new [`ChainHeadFollower`].
	pub fn new(
		client: Arc<Client>,
		backend: Arc<BE>,
		sub_handle: Arc<SubscriptionManagement<Block, BE>>,
		with_runtime: bool,
		sub_id: String,
	) -> Self {
		Self { client, backend, sub_handle, with_runtime, sub_id, best_block_cache: None }
	}
}

/// A block notification.
enum NotificationType<Block: BlockT> {
	/// The initial events generated from the node's memory.
	InitialEvents(Vec<FollowEvent<Block::Hash>>),
	/// The new block notification obtained from `import_notification_stream`.
	NewBlock(BlockImportNotification<Block>),
	/// The finalized block notification obtained from `finality_notification_stream`.
	Finalized(FinalityNotification<Block>),
}

/// The initial blocks that should be reported or ignored by the chainHead.
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

/// The startup point from which chainHead started to generate events.
struct StartupPoint<Block: BlockT> {
	/// Best block hash.
	pub best_hash: Block::Hash,
	/// The head of the finalized chain.
	pub finalized_hash: Block::Hash,
	/// Last finalized block number.
	pub finalized_number: NumberFor<Block>,
}

impl<Block: BlockT> From<Info<Block>> for StartupPoint<Block> {
	fn from(info: Info<Block>) -> Self {
		StartupPoint::<Block> {
			best_hash: info.best_hash,
			finalized_hash: info.finalized_hash,
			finalized_number: info.finalized_number,
		}
	}
}

impl<BE, Block, Client> ChainHeadFollower<BE, Block, Client>
where
	Block: BlockT + 'static,
	BE: Backend<Block> + 'static,
	Client: BlockBackend<Block>
		+ HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = BlockChainError>
		+ BlockchainEvents<Block>
		+ CallApiAt<Block>
		+ 'static,
{
	/// Conditionally generate the runtime event of the given block.
	fn generate_runtime_event(
		&self,
		block: Block::Hash,
		parent: Option<Block::Hash>,
	) -> Option<RuntimeEvent> {
		// No runtime versions should be reported.
		if !self.with_runtime {
			return None
		}

		let block_rt = match self.client.runtime_version_at(block) {
			Ok(rt) => rt,
			Err(err) => return Some(err.into()),
		};

		let parent = match parent {
			Some(parent) => parent,
			// Nothing to compare against, always report.
			None => return Some(RuntimeEvent::Valid(RuntimeVersionEvent { spec: block_rt })),
		};

		let parent_rt = match self.client.runtime_version_at(parent) {
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
	fn get_init_blocks_with_forks(
		&self,
		startup_point: &StartupPoint<Block>,
	) -> Result<InitialBlocks<Block>, SubscriptionManagementError> {
		let blockchain = self.backend.blockchain();
		let leaves = blockchain.leaves()?;
		let finalized = startup_point.finalized_hash;
		let mut pruned_forks = HashSet::new();
		let mut finalized_block_descendants = Vec::new();
		let mut unique_descendants = HashSet::new();
		for leaf in leaves {
			let tree_route = sp_blockchain::tree_route(blockchain, finalized, leaf)?;

			let blocks = tree_route.enacted().iter().map(|block| block.hash);
			if !tree_route.retracted().is_empty() {
				pruned_forks.extend(blocks);
			} else {
				// Ensure a `NewBlock` event is generated for all children of the
				// finalized block. Describe the tree route as (child_node, parent_node)
				// Note: the order of elements matters here.
				let parents = std::iter::once(finalized).chain(blocks.clone());

				for pair in blocks.zip(parents) {
					if unique_descendants.insert(pair) {
						finalized_block_descendants.push(pair);
					}
				}
			}
		}

		Ok(InitialBlocks { finalized_block_descendants, pruned_forks })
	}

	/// Generate the initial events reported by the RPC `follow` method.
	///
	/// Returns the initial events that should be reported directly, together with pruned
	/// block hashes that should be ignored by the `Finalized` event.
	fn generate_init_events(
		&mut self,
		startup_point: &StartupPoint<Block>,
	) -> Result<(Vec<FollowEvent<Block::Hash>>, HashSet<Block::Hash>), SubscriptionManagementError>
	{
		let init = self.get_init_blocks_with_forks(startup_point)?;

		let initial_blocks = init.finalized_block_descendants;

		// The initialized event is the first one sent.
		let finalized_block_hash = startup_point.finalized_hash;
		self.sub_handle.pin_block(&self.sub_id, finalized_block_hash)?;

		let finalized_block_runtime = self.generate_runtime_event(finalized_block_hash, None);

		let initialized_event = FollowEvent::Initialized(Initialized {
			finalized_block_hash,
			finalized_block_runtime,
			with_runtime: self.with_runtime,
		});

		let mut finalized_block_descendants = Vec::with_capacity(initial_blocks.len() + 1);

		finalized_block_descendants.push(initialized_event);
		for (child, parent) in initial_blocks.into_iter() {
			self.sub_handle.pin_block(&self.sub_id, child)?;

			let new_runtime = self.generate_runtime_event(child, Some(parent));

			let event = FollowEvent::NewBlock(NewBlock {
				block_hash: child,
				parent_block_hash: parent,
				new_runtime,
				with_runtime: self.with_runtime,
			});

			finalized_block_descendants.push(event);
		}

		// Generate a new best block event.
		let best_block_hash = startup_point.best_hash;
		if best_block_hash != finalized_block_hash {
			let best_block = FollowEvent::BestBlockChanged(BestBlockChanged { best_block_hash });
			self.best_block_cache = Some(best_block_hash);
			finalized_block_descendants.push(best_block);
		};

		Ok((finalized_block_descendants, init.pruned_forks))
	}

	/// Generate the "NewBlock" event and potentially the "BestBlockChanged" event for the
	/// given block hash.
	fn generate_import_events(
		&mut self,
		block_hash: Block::Hash,
		parent_block_hash: Block::Hash,
		is_best_block: bool,
	) -> Vec<FollowEvent<Block::Hash>> {
		let new_runtime = self.generate_runtime_event(block_hash, Some(parent_block_hash));

		let new_block = FollowEvent::NewBlock(NewBlock {
			block_hash,
			parent_block_hash,
			new_runtime,
			with_runtime: self.with_runtime,
		});

		if !is_best_block {
			return vec![new_block]
		}

		// If this is the new best block, then we need to generate two events.
		let best_block_event =
			FollowEvent::BestBlockChanged(BestBlockChanged { best_block_hash: block_hash });

		match self.best_block_cache {
			Some(block_cache) => {
				// The RPC layer has not reported this block as best before.
				// Note: This handles the race with the finalized branch.
				if block_cache != block_hash {
					self.best_block_cache = Some(block_hash);
					vec![new_block, best_block_event]
				} else {
					vec![new_block]
				}
			},
			None => {
				self.best_block_cache = Some(block_hash);
				vec![new_block, best_block_event]
			},
		}
	}

	/// Handle the import of new blocks by generating the appropriate events.
	fn handle_import_blocks(
		&mut self,
		notification: BlockImportNotification<Block>,
		startup_point: &StartupPoint<Block>,
	) -> Result<Vec<FollowEvent<Block::Hash>>, SubscriptionManagementError> {
		// The block was already pinned by the initial block events or by the finalized event.
		if !self.sub_handle.pin_block(&self.sub_id, notification.hash)? {
			return Ok(Default::default())
		}

		// Ensure we are only reporting blocks after the starting point.
		if *notification.header.number() < startup_point.finalized_number {
			return Ok(Default::default())
		}

		Ok(self.generate_import_events(
			notification.hash,
			*notification.header.parent_hash(),
			notification.is_new_best,
		))
	}

	/// Generates new block events from the given finalized hashes.
	///
	/// It may be possible that the `Finalized` event fired before the `NewBlock`
	/// event. In that case, for each finalized hash that was not reported yet
	/// generate the `NewBlock` event. For the final finalized hash we must also
	/// generate one `BestBlock` event.
	fn generate_finalized_events(
		&mut self,
		finalized_block_hashes: &[Block::Hash],
	) -> Result<Vec<FollowEvent<Block::Hash>>, SubscriptionManagementError> {
		let mut events = Vec::new();

		// Nothing to be done if no finalized hashes are provided.
		let Some(first_hash) = finalized_block_hashes.get(0) else { return Ok(Default::default()) };

		// Find the parent header.
		let Some(first_header) = self.client.header(*first_hash)? else {
			return Err(SubscriptionManagementError::BlockHeaderAbsent)
		};

		let parents =
			std::iter::once(first_header.parent_hash()).chain(finalized_block_hashes.iter());
		for (i, (hash, parent)) in finalized_block_hashes.iter().zip(parents).enumerate() {
			// Check if the block was already reported and thus, is already pinned.
			if !self.sub_handle.pin_block(&self.sub_id, *hash)? {
				continue
			}

			// Generate `NewBlock` events for all blocks beside the last block in the list
			if i + 1 != finalized_block_hashes.len() {
				// Generate only the `NewBlock` event for this block.
				events.extend(self.generate_import_events(*hash, *parent, false));
			} else {
				// If we end up here and the `best_block` is a descendent of the finalized block
				// (last block in the list), it means that there were skipped notifications.
				// Otherwise `pin_block` would had returned `true`.
				//
				// When the node falls out of sync and then syncs up to the tip of the chain, it can
				// happen that we skip notifications. Then it is better to terminate the connection
				// instead of trying to send notifications for all missed blocks.
				if let Some(best_block_hash) = self.best_block_cache {
					let ancestor = sp_blockchain::lowest_common_ancestor(
						&*self.client,
						*hash,
						best_block_hash,
					)?;

					if ancestor.hash == *hash {
						return Err(SubscriptionManagementError::Custom(
							"A descendent of the finalized block was already reported".into(),
						))
					}
				}

				// Let's generate the `NewBlock` and `NewBestBlock` events for the block.
				events.extend(self.generate_import_events(*hash, *parent, true))
			}
		}

		Ok(events)
	}

	/// Get all pruned block hashes from the provided stale heads.
	///
	/// The result does not include hashes from `to_ignore`.
	fn get_pruned_hashes(
		&self,
		stale_heads: &[Block::Hash],
		last_finalized: Block::Hash,
		to_ignore: &mut HashSet<Block::Hash>,
	) -> Result<Vec<Block::Hash>, SubscriptionManagementError> {
		let blockchain = self.backend.blockchain();
		let mut pruned = Vec::new();

		for stale_head in stale_heads {
			let tree_route = sp_blockchain::tree_route(blockchain, last_finalized, *stale_head)?;

			// Collect only blocks that are not part of the canonical chain.
			pruned.extend(tree_route.enacted().iter().filter_map(|block| {
				if !to_ignore.remove(&block.hash) {
					Some(block.hash)
				} else {
					None
				}
			}))
		}

		Ok(pruned)
	}

	/// Handle the finalization notification by generating the `Finalized` event.
	///
	/// If the block of the notification was not reported yet, this method also
	/// generates the events similar to `handle_import_blocks`.
	fn handle_finalized_blocks(
		&mut self,
		notification: FinalityNotification<Block>,
		to_ignore: &mut HashSet<Block::Hash>,
		startup_point: &StartupPoint<Block>,
	) -> Result<Vec<FollowEvent<Block::Hash>>, SubscriptionManagementError> {
		let last_finalized = notification.hash;

		// Ensure we are only reporting blocks after the starting point.
		if *notification.header.number() < startup_point.finalized_number {
			return Ok(Default::default())
		}

		// The tree route contains the exclusive path from the last finalized block to the block
		// reported by the notification. Ensure the finalized block is also reported.
		let mut finalized_block_hashes = notification.tree_route.to_vec();
		finalized_block_hashes.push(last_finalized);

		// If the finalized hashes were not reported yet, generate the `NewBlock` events.
		let mut events = self.generate_finalized_events(&finalized_block_hashes)?;

		// Report all pruned blocks from the notification that are not
		// part of the fork we need to ignore.
		let pruned_block_hashes =
			self.get_pruned_hashes(&notification.stale_heads, last_finalized, to_ignore)?;

		let finalized_event = FollowEvent::Finalized(Finalized {
			finalized_block_hashes,
			pruned_block_hashes: pruned_block_hashes.clone(),
		});

		match self.best_block_cache {
			Some(block_cache) => {
				// If the best block wasn't pruned, we are done here.
				if !pruned_block_hashes.iter().any(|hash| *hash == block_cache) {
					events.push(finalized_event);
					return Ok(events)
				}

				// The best block is reported as pruned. Therefore, we need to signal a new
				// best block event before submitting the finalized event.
				let best_block_hash = self.client.info().best_hash;
				if best_block_hash == block_cache {
					// The client doest not have any new information about the best block.
					// The information from `.info()` is updated from the DB as the last
					// step of the finalization and it should be up to date.
					// If the info is outdated, there is nothing the RPC can do for now.
					error!(
						target: LOG_TARGET,
						"[follow][id={:?}] Client does not contain different best block",
						self.sub_id,
					);
					events.push(finalized_event);
					Ok(events)
				} else {
					// The RPC needs to also submit a new best block changed before the
					// finalized event.
					self.best_block_cache = Some(best_block_hash);
					let best_block_event =
						FollowEvent::BestBlockChanged(BestBlockChanged { best_block_hash });
					events.extend([best_block_event, finalized_event]);
					Ok(events)
				}
			},
			None => {
				events.push(finalized_event);
				Ok(events)
			},
		}
	}

	/// Submit the events from the provided stream to the RPC client
	/// for as long as the `rx_stop` event was not called.
	async fn submit_events<EventStream>(
		&mut self,
		startup_point: &StartupPoint<Block>,
		mut stream: EventStream,
		mut to_ignore: HashSet<Block::Hash>,
		mut sink: SubscriptionSink,
		rx_stop: oneshot::Receiver<()>,
	) where
		EventStream: Stream<Item = NotificationType<Block>> + Unpin,
	{
		let mut stream_item = stream.next();
		let mut stop_event = rx_stop;

		while let Either::Left((Some(event), next_stop_event)) =
			futures_util::future::select(stream_item, stop_event).await
		{
			let events = match event {
				NotificationType::InitialEvents(events) => Ok(events),
				NotificationType::NewBlock(notification) =>
					self.handle_import_blocks(notification, &startup_point),
				NotificationType::Finalized(notification) =>
					self.handle_finalized_blocks(notification, &mut to_ignore, &startup_point),
			};

			let events = match events {
				Ok(events) => events,
				Err(err) => {
					debug!(
						target: LOG_TARGET,
						"[follow][id={:?}] Failed to handle stream notification {:?}",
						self.sub_id,
						err
					);
					let _ = sink.send(&FollowEvent::<String>::Stop);
					return
				},
			};

			for event in events {
				let result = sink.send(&event);

				// Migration note: the new version of jsonrpsee returns Result<(), DisconnectError>
				// The logic from `Err(err)` should be moved when building the new
				// `SubscriptionMessage`.

				// For now, jsonrpsee returns:
				// Ok(true): message sent
				// Ok(false): client disconnected or subscription closed
				// Err(err): serder serialization error of the event
				if let Err(err) = result {
					// Failed to submit event.
					debug!(
						target: LOG_TARGET,
						"[follow][id={:?}] Failed to send event {:?}", self.sub_id, err
					);

					let _ = sink.send(&FollowEvent::<String>::Stop);
					return
				}

				if let Ok(false) = result {
					// Client disconnected or subscription was closed.
					return
				}
			}

			stream_item = stream.next();
			stop_event = next_stop_event;
		}

		// If we got here either the substrate streams have closed
		// or the `Stop` receiver was triggered.
		let _ = sink.send(&FollowEvent::<String>::Stop);
	}

	/// Generate the block events for the `chainHead_follow` method.
	pub async fn generate_events(
		&mut self,
		mut sink: SubscriptionSink,
		rx_stop: oneshot::Receiver<()>,
	) {
		// Register for the new block and finalized notifications.
		let stream_import = self
			.client
			.import_notification_stream()
			.map(|notification| NotificationType::NewBlock(notification));

		let stream_finalized = self
			.client
			.finality_notification_stream()
			.map(|notification| NotificationType::Finalized(notification));

		let startup_point = StartupPoint::from(self.client.info());
		let (initial_events, pruned_forks) = match self.generate_init_events(&startup_point) {
			Ok(blocks) => blocks,
			Err(err) => {
				debug!(
					target: LOG_TARGET,
					"[follow][id={:?}] Failed to generate the initial events {:?}",
					self.sub_id,
					err
				);
				let _ = sink.send(&FollowEvent::<Block::Hash>::Stop);
				return
			},
		};

		let initial = NotificationType::InitialEvents(initial_events);
		let merged = tokio_stream::StreamExt::merge(stream_import, stream_finalized);
		let stream = stream::once(futures::future::ready(initial)).chain(merged);

		self.submit_events(&startup_point, stream.boxed(), pruned_forks, sink, rx_stop)
			.await;
	}
}
