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

//! Blockchain API backend for light nodes.

use futures::{future::ready, FutureExt, TryFutureExt};
use jsonrpc_pubsub::manager::SubscriptionManager;
use std::sync::Arc;

use sc_client_api::light::{Fetcher, RemoteBlockchain, RemoteBodyRequest};
use sp_runtime::{
	generic::{BlockId, SignedBlock},
	traits::Block as BlockT,
};

use super::{client_err, error::FutureResult, ChainBackend};
use sc_client_api::BlockchainEvents;
use sp_blockchain::HeaderBackend;

/// Blockchain API backend for light nodes. Reads all the data from local
/// database, if available, or fetches it from remote node otherwise.
pub struct LightChain<Block: BlockT, Client, F> {
	/// Substrate client.
	client: Arc<Client>,
	/// Current subscriptions.
	subscriptions: SubscriptionManager,
	/// Remote blockchain reference
	remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
	/// Remote fetcher reference.
	fetcher: Arc<F>,
}

impl<Block: BlockT, Client, F: Fetcher<Block>> LightChain<Block, Client, F> {
	/// Create new Chain API RPC handler.
	pub fn new(
		client: Arc<Client>,
		subscriptions: SubscriptionManager,
		remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
		fetcher: Arc<F>,
	) -> Self {
		Self { client, subscriptions, remote_blockchain, fetcher }
	}
}

impl<Block, Client, F> ChainBackend<Client, Block> for LightChain<Block, Client, F>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	Client: BlockchainEvents<Block> + HeaderBackend<Block> + Send + Sync + 'static,
	F: Fetcher<Block> + Send + Sync + 'static,
{
	fn client(&self) -> &Arc<Client> {
		&self.client
	}

	fn subscriptions(&self) -> &SubscriptionManager {
		&self.subscriptions
	}

	fn header(&self, hash: Option<Block::Hash>) -> FutureResult<Option<Block::Header>> {
		let hash = self.unwrap_or_best(hash);

		let fetcher = self.fetcher.clone();
		let maybe_header = sc_client_api::light::future_header(
			&*self.remote_blockchain,
			&*fetcher,
			BlockId::Hash(hash),
		);

		maybe_header.then(move |result| ready(result.map_err(client_err))).boxed()
	}

	fn block(&self, hash: Option<Block::Hash>) -> FutureResult<Option<SignedBlock<Block>>> {
		let fetcher = self.fetcher.clone();
		self.header(hash)
			.and_then(move |header| async move {
				match header {
					Some(header) => {
						let body = fetcher
							.remote_body(RemoteBodyRequest {
								header: header.clone(),
								retry_count: Default::default(),
							})
							.await;

						body.map(|body| {
							Some(SignedBlock {
								block: Block::new(header, body),
								justifications: None,
							})
						})
						.map_err(client_err)
					},
					None => Ok(None),
				}
			})
			.boxed()
	}
}
