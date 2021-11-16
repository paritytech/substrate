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

//! Blockchain API backend for full nodes.

use super::{client_err, ChainBackend, Error};
use crate::SubscriptionTaskExecutor;
use std::{marker::PhantomData, sync::Arc};

use futures::{
	stream::{self, Stream, StreamExt},
	future,
	task::Spawn,
};
use jsonrpsee::ws_server::SubscriptionSink;
use sc_client_api::{BlockBackend, BlockchainEvents};
use sp_blockchain::HeaderBackend;
use sp_runtime::{
	generic::{BlockId, SignedBlock},
	traits::Block as BlockT,
};

/// Blockchain API backend for full nodes. Reads all the data from local database.
pub struct FullChain<Block: BlockT, Client> {
	/// Substrate client.
	client: Arc<Client>,
	/// phantom member to pin the block type
	_phantom: PhantomData<Block>,
	/// Subscription executor.
	executor: SubscriptionTaskExecutor,
}

impl<Block: BlockT, Client> FullChain<Block, Client> {
	/// Create new Chain API RPC handler.
	pub fn new(client: Arc<Client>, executor: SubscriptionTaskExecutor) -> Self {
		Self { client, executor, _phantom: PhantomData }
	}
}

#[async_trait::async_trait]
impl<Block, Client> ChainBackend<Client, Block> for FullChain<Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	Client: BlockBackend<Block> + HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	fn client(&self) -> &Arc<Client> {
		&self.client
	}

	async fn header(&self, hash: Option<Block::Hash>) -> Result<Option<Block::Header>, Error> {
		self.client.header(BlockId::Hash(self.unwrap_or_best(hash))).map_err(client_err)
	}

	async fn block(&self, hash: Option<Block::Hash>) -> Result<Option<SignedBlock<Block>>, Error> {
		self.client.block(&BlockId::Hash(self.unwrap_or_best(hash))).map_err(client_err)
	}

	fn subscribe_all_heads(&self, sink: SubscriptionSink) -> Result<(), Error> {
		subscribe_headers(
			&self.client,
			self.executor.clone(),
			"chain_subscribeAllHeads",
			sink,
			|| self.client().info().best_hash,
			|| {
				self.client()
					.import_notification_stream()
					.map(|notification| notification.header)
			},
		)
	}

	fn subscribe_new_heads(&self, sink: SubscriptionSink) -> Result<(), Error> {
		subscribe_headers(
			&self.client,
			self.executor.clone(),
			"chain_subscribeNewHeads",
			sink,
			|| self.client().info().best_hash,
			|| {
				self.client()
					.import_notification_stream()
					.filter(|notification| future::ready(notification.is_new_best))
					.map(|notification| notification.header)
			},
		)
	}

	fn subscribe_finalized_heads(&self, sink: SubscriptionSink) -> Result<(), Error> {
		subscribe_headers(
			&self.client,
			self.executor.clone(),
			"chain_subscribeFinalizedHeads",
			sink,
			|| self.client().info().finalized_hash,
			|| {
				self.client()
					.finality_notification_stream()
					.map(|notification| notification.header)
			},
		)
	}
}

/// Subscribe to new headers.
fn subscribe_headers<Block, Client, F, G, S>(
	client: &Arc<Client>,
	executor: SubscriptionTaskExecutor,
	method: &'static str,
	mut sink: SubscriptionSink,
	best_block_hash: G,
	stream: F,
) -> Result<(), Error>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	Client: HeaderBackend<Block> + 'static,
	F: FnOnce() -> S,
	G: FnOnce() -> Block::Hash,
	S: Stream<Item = Block::Header> + Send + 'static,
{
		// send current head right at the start.
		let maybe_header = client
			.header(BlockId::Hash(best_block_hash()))
			.map_err(client_err)
			.and_then(|header| {
				header.ok_or_else(|| Error::Other("Best header missing.".to_string()))
			})
			.map_err(|e| {
				log::warn!("Best header error {:?}", e);
				e
			})
			.ok();

		// send further subscriptions
		let stream = stream();

		// NOTE: by the time we set up the stream there might be a new best block and so there is a risk
		// that the stream has a hole in it. The alternative would be to look up the best block *after*
		// we set up the stream and chain it to the stream. Consuming code would need to handle
		// duplicates at the beginning of the stream though.
		let fut = async move {
			stream::iter(maybe_header)
				.chain(stream)
				.take_while(|storage| {
					future::ready(sink.send(&storage).map_or_else(
						|e| {
							log::debug!("Could not send data to subscription: {} error: {:?}", method, e);
							false
						},
						|_| true,
					))
				})
				.for_each(|_| future::ready(()))
				.await;
			};

		executor.spawn_obj(Box::pin(fut).into()).map_err(|e| Error::Client(Box::new(e)))
}
