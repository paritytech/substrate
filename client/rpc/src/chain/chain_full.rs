// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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
	future::{self, FutureExt},
	stream::{self, Stream, StreamExt},
};
use jsonrpsee::PendingSubscription;
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

impl<Block, Client> ChainBackend<Client, Block> for FullChain<Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	Client: BlockBackend<Block> + HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	fn client(&self) -> &Arc<Client> {
		&self.client
	}

	fn header(&self, hash: Option<Block::Hash>) -> Result<Option<Block::Header>, Error> {
		self.client.header(BlockId::Hash(self.unwrap_or_best(hash))).map_err(client_err)
	}

	fn block(&self, hash: Option<Block::Hash>) -> Result<Option<SignedBlock<Block>>, Error> {
		self.client.block(&BlockId::Hash(self.unwrap_or_best(hash))).map_err(client_err)
	}

	fn subscribe_all_heads(&self, sink: PendingSubscription) {
		subscribe_headers(
			&self.client,
			&self.executor,
			sink,
			|| self.client().info().best_hash,
			|| {
				self.client()
					.import_notification_stream()
					.map(|notification| notification.header)
			},
		)
	}

	fn subscribe_new_heads(&self, sink: PendingSubscription) {
		subscribe_headers(
			&self.client,
			&self.executor,
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

	fn subscribe_finalized_heads(&self, sink: PendingSubscription) {
		subscribe_headers(
			&self.client,
			&self.executor,
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
	executor: &SubscriptionTaskExecutor,
	pending: PendingSubscription,
	best_block_hash: G,
	stream: F,
) where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	Client: HeaderBackend<Block> + 'static,
	F: FnOnce() -> S,
	G: FnOnce() -> Block::Hash,
	S: Stream<Item = Block::Header> + Send + Unpin + 'static,
{
	// send current head right at the start.
	let maybe_header = client
		.header(BlockId::Hash(best_block_hash()))
		.map_err(client_err)
		.and_then(|header| header.ok_or_else(|| Error::Other("Best header missing.".into())))
		.map_err(|e| log::warn!("Best header error {:?}", e))
		.ok();

	// NOTE: by the time we set up the stream there might be a new best block and so there is a risk
	// that the stream has a hole in it. The alternative would be to look up the best block *after*
	// we set up the stream and chain it to the stream. Consuming code would need to handle
	// duplicates at the beginning of the stream though.
	let stream = stream::iter(maybe_header).chain(stream());

	let fut = async move {
		if let Some(mut sink) = pending.accept() {
			sink.pipe_from_stream(stream).await;
		}
	};

	executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
}
