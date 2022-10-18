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

//! Blockchain API backend for full nodes.

use crate::{
	chain_head::{api::ChainHeadApiServer, subscription::SubscriptionManagement},
	SubscriptionTaskExecutor,
};
use serde::{Deserialize, Serialize};
use std::{
	collections::{hash_map::Entry, HashMap, HashSet},
	marker::PhantomData,
	sync::{Arc, Mutex},
};

use futures::{
	future::{self, FutureExt},
	stream::{self, Stream, StreamExt},
};
use jsonrpsee::{core::async_trait, types::SubscriptionResult, SubscriptionSink};
use sc_client_api::{
	Backend, BlockBackend, BlockchainEvents, StorageData, StorageKey, StorageProvider,
};
use sp_api::CallApiAt;
use sp_blockchain::HeaderBackend;
use sp_runtime::{
	generic::{BlockId, SignedBlock},
	traits::{Block as BlockT, Header, NumberFor},
};
use sp_version::RuntimeVersion;

/// An API for chain head RPC calls.
pub struct ChainHead<BE, Block: BlockT, Client> {
	/// Substrate client.
	client: Arc<Client>,
	/// Executor to spawn subscriptions.
	executor: SubscriptionTaskExecutor,

	/// Keep track of the pinned blocks for each subscription.
	subscriptions: Arc<SubscriptionManagement<Block>>,

	// pinned_blocks: Arc<Mutex<Vec<T>>>,
	/// Phantom member to pin the block type.
	_phantom: PhantomData<(Block, BE)>,
}

impl<BE, Block: BlockT, Client> ChainHead<BE, Block, Client> {
	/// Creates a new [`ChainHead`].
	pub fn new(client: Arc<Client>, executor: SubscriptionTaskExecutor) -> Self {
		Self {
			client,
			executor,
			subscriptions: Arc::new(SubscriptionManagement::new()),
			_phantom: PhantomData,
		}
	}
}

#[async_trait]
impl<BE, Block, Client>
	ChainHeadApiServer<NumberFor<Block>, Block::Hash, Block::Header, SignedBlock<Block>>
	for ChainHead<BE, Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	BE: Backend<Block> + 'static,
	Client: BlockBackend<Block>
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
		// TODO: get this from jsonrpsee
		let sub_id = "A0".to_string();

		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();

		self.subscriptions.insert_subscription(sub_id.clone());

		let sub_id_import = sub_id.clone();

		let stream_import = self
			.client
			.import_notification_stream()
			.map(move |notification| {
				let new_runtime = if runtime_updates {
					match (
						client.runtime_version_at(&BlockId::Hash(notification.hash)),
						client
							.runtime_version_at(&BlockId::Hash(*notification.header.parent_hash())),
					) {
						(Ok(spec), Ok(parent_spec)) =>
							if spec != parent_spec {
								Some(RuntimeEvent::Valid(RuntimeVersionEvent { spec }))
							} else {
								None
							},
						(Err(err), _) | (_, Err(err)) =>
							Some(RuntimeEvent::Invalid(RuntimeErrorEvent {
								error: format!("Api error: {}", err),
							})),
					}
				} else {
					None
				};

				println!("\n - PINNING: {:?} - {:?}", sub_id_import, notification.hash);

				if let Err(_) = subscriptions.pin_block(&sub_id_import, notification.hash.clone()) {
					println!("\n - PINNING: {:?} - {:?} FAILED", sub_id_import, notification.hash);
					// TODO: signal drop error.
				}

				let new_block = FollowEvent::NewBlock(NewBlock {
					block_hash: notification.hash,
					parent_hash: *notification.header.parent_hash(),
					new_runtime,
				});

				if !notification.is_new_best {
					return stream::iter(vec![new_block])
				}

				// If this is the new best block, then we need to generate two events.
				let best_block = FollowEvent::BestBlockChanged(BestBlockChanged {
					best_block_hash: notification.hash,
				});
				stream::iter(vec![new_block, best_block])
			})
			.flatten();

		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();
		let sub_id_import = sub_id.clone();

		let stream_finalized =
			self.client.finality_notification_stream().map(move |notification| {
				// We might not receive all new blocks reports, therefore we make sure to include it
				// here.
				if let Err(_) = subscriptions.pin_block(&sub_id_import, notification.hash.clone()) {
					// TODO: signal drop error.
				}

				FollowEvent::Finalized(Finalized { block_hash: notification.hash })
			});

		let merged = tokio_stream::StreamExt::merge(stream_import, stream_finalized);

		// The initialized event is the first one sent.
		let finalized_block_hash = self.client.info().finalized_hash;
		let finalized_block_runtime = if runtime_updates {
			Some(match self.client.runtime_version_at(&BlockId::Hash(finalized_block_hash)) {
				Ok(spec) => RuntimeEvent::Valid(RuntimeVersionEvent { spec }),
				Err(err) => RuntimeEvent::Invalid(RuntimeErrorEvent {
					error: format!("Api error: {}", err),
				}),
			})
		} else {
			None
		};

		if let Err(_) = self.subscriptions.pin_block(&sub_id, finalized_block_hash.clone()) {
			// TODO: signal drop error.
		}

		let stream = stream::once(async move {
			FollowEvent::Initialized(Initialized { finalized_block_hash, finalized_block_runtime })
		})
		.chain(merged);

		let fut = async move {
			sink.pipe_from_stream(stream.boxed()).await;
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	// mut sink: SubscriptionSink, runtime_updates: bool) -> SubscriptionResult {
	fn chainHead_unstable_body(
		&self,
		mut sink: SubscriptionSink,
		follow_subscription: String,
		hash: Block::Hash,
		network_config: Option<()>,
	) -> SubscriptionResult {
		// TODO: get this from jsonrpsee
		let sub_id = "A0".to_string();

		// let res = match self.client.block(&BlockId::hash(hash)) {
		// 	Ok(Some(block)) => BodyEvent::Done(block),
		// 	_ => BodyEvent::<SignedBlock<Block>>::Inaccessible,
		// };

		let res = if self.subscriptions.contains(&sub_id, &hash).is_err() {
			BodyEvent::<SignedBlock<Block>>::Disjoint
		} else {
			match self.client.block(&BlockId::hash(hash)) {
				Ok(Some(block)) => BodyEvent::Done(block),
				_ => BodyEvent::<SignedBlock<Block>>::Inaccessible,
			}
		};

		let stream = stream::once(async move { res });
		let fut = async move {
			sink.pipe_from_stream(stream.boxed()).await;
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chainHead_unstable_storage(
		&self,
		mut sink: SubscriptionSink,
		follow_subscription: String,
		hash: Block::Hash,
		key: StorageKey,
		network_config: Option<()>,
	) -> SubscriptionResult {
		// TODO: get this from jsonrpsee
		let sub_id = "A0".to_string();

		let res = if self.subscriptions.contains(&sub_id, &hash).is_err() {
			BodyEvent::<StorageData>::Disjoint
		} else {
			match self.client.storage(&BlockId::hash(hash), &key) {
				Ok(Some(block)) => BodyEvent::Done(block),
				_ => BodyEvent::<StorageData>::Inaccessible,
			}
		};

		let stream = stream::once(async move { res });
		let fut = async move {
			sink.pipe_from_stream(stream.boxed()).await;
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}
}

/// The transaction could not be processed due to an error.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RuntimeErrorEvent {
	/// Reason of the error.
	pub error: String,
}

/// The transaction could not be processed due to an error.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RuntimeVersionEvent {
	/// Reason of the error.
	pub spec: RuntimeVersion,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "type")]
pub enum RuntimeEvent {
	Valid(RuntimeVersionEvent),
	Invalid(RuntimeErrorEvent),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Initialized<Hash> {
	/// The hash of the imported block.
	pub finalized_block_hash: Hash,
	pub finalized_block_runtime: Option<RuntimeEvent>,
}

/// The transaction was included in a block of the chain.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NewBlock<Hash> {
	/// The hash of the imported block.
	pub block_hash: Hash,
	/// The parent hash of the imported block.
	pub parent_hash: Hash,
	pub new_runtime: Option<RuntimeEvent>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BestBlockChanged<Hash> {
	pub best_block_hash: Hash,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Finalized<Hash> {
	/// The hash of the finalized block.
	pub block_hash: Hash,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "event")]
pub enum FollowEvent<Hash> {
	Initialized(Initialized<Hash>),
	NewBlock(NewBlock<Hash>),
	BestBlockChanged(BestBlockChanged<Hash>),
	Finalized(Finalized<Hash>),
	Stop,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "event", content = "value")]
pub enum BodyEvent<Body> {
	Done(Body),
	Inaccessible,
	Disjoint,
}
