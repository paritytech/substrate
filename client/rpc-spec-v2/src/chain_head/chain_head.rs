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

use crate::{chain_head::api::ChainHeadApiServer, SubscriptionTaskExecutor};
use serde::{Deserialize, Serialize};
use std::{marker::PhantomData, sync::Arc};

use futures::{
	future::{self, FutureExt},
	stream::{self, Stream, StreamExt},
};
use jsonrpsee::{core::async_trait, types::SubscriptionResult, SubscriptionSink};
use sc_client_api::{BlockBackend, BlockchainEvents};
use sp_blockchain::HeaderBackend;
use sp_runtime::{
	generic::{BlockId, SignedBlock},
	traits::{Block as BlockT, Header, NumberFor},
};

/// An API for chain head RPC calls.
pub struct ChainHead<Block: BlockT, Client> {
	/// Substrate client.
	client: Arc<Client>,
	/// Executor to spawn subscriptions.
	executor: SubscriptionTaskExecutor,
	/// Phantom member to pin the block type.
	_phantom: PhantomData<Block>,
}

impl<Block: BlockT, Client> ChainHead<Block, Client> {
	/// Creates a new [`ChainHead`].
	pub fn new(client: Arc<Client>, executor: SubscriptionTaskExecutor) -> Self {
		Self { client, executor, _phantom: PhantomData }
	}
}

#[async_trait]
impl<Block, Client>
	ChainHeadApiServer<NumberFor<Block>, Block::Hash, Block::Header, SignedBlock<Block>>
	for ChainHead<Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	Client: BlockBackend<Block> + HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	fn follow(&self, mut sink: SubscriptionSink) -> SubscriptionResult {
		let stream_import = self
			.client
			.import_notification_stream()
			.map(|notification| {
				let new_block = FollowEvent::NewBlock(NewBlock {
					block_hash: notification.hash,
					parent_hash: *notification.header.parent_hash(),
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

		let stream_finalized = self.client.finality_notification_stream().map(|notification| {
			FollowEvent::Finalized(Finalized { block_hash: notification.hash })
		});

		let merged = tokio_stream::StreamExt::merge(stream_import, stream_finalized);

		// TODO: client().runtime_version_at()

		let fut = async move {
			sink.pipe_from_stream(merged.boxed()).await;
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Initialized<Hash> {
	/// The hash of the imported block.
	pub finalized_block_hash: Hash,
}

/// The transaction was included in a block of the chain.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NewBlock<Hash> {
	/// The hash of the imported block.
	pub block_hash: Hash,
	/// The parent hash of the imported block.
	pub parent_hash: Hash,
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
