// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Blockchain API backend for light nodes.

use std::sync::Arc;
use futures::{future::ready, FutureExt, TryFutureExt};
use rpc::futures::future::{result, Future, Either};

use api::Subscriptions;
use client::{
	self, Client,
	light::{
		fetcher::{Fetcher, RemoteBodyRequest},
		blockchain::RemoteBlockchain,
	},
};
use primitives::{H256, Blake2Hasher};
use sp_runtime::{
	generic::{BlockId, SignedBlock},
	traits::{Block as BlockT},
};

use super::{ChainBackend, client_err, error::FutureResult};

/// Blockchain API backend for light nodes. Reads all the data from local
/// database, if available, or fetches it from remote node otherwise.
pub struct LightChain<B, E, Block: BlockT, RA, F> {
	/// Substrate client.
	client: Arc<Client<B, E, Block, RA>>,
	/// Current subscriptions.
	subscriptions: Subscriptions,
	/// Remote blockchain reference
	remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
	/// Remote fetcher reference.
	fetcher: Arc<F>,
}

impl<B, E, Block: BlockT, RA, F: Fetcher<Block>> LightChain<B, E, Block, RA, F> {
	/// Create new Chain API RPC handler.
	pub fn new(
		client: Arc<Client<B, E, Block, RA>>,
		subscriptions: Subscriptions,
		remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
		fetcher: Arc<F>,
	) -> Self {
		Self {
			client,
			subscriptions,
			remote_blockchain,
			fetcher,
		}
	}
}

impl<B, E, Block, RA, F> ChainBackend<B, E, Block, RA> for LightChain<B, E, Block, RA, F> where
	Block: BlockT<Hash=H256> + 'static,
	B: client_api::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: client::CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	RA: Send + Sync + 'static,
	F: Fetcher<Block> + Send + Sync + 'static,
{
	fn client(&self) -> &Arc<Client<B, E, Block, RA>> {
		&self.client
	}

	fn subscriptions(&self) -> &Subscriptions {
		&self.subscriptions
	}

	fn header(&self, hash: Option<Block::Hash>) -> FutureResult<Option<Block::Header>> {
		let hash = self.unwrap_or_best(hash);

		let fetcher = self.fetcher.clone();
		let maybe_header = client::light::blockchain::future_header(
			&*self.remote_blockchain,
			&*fetcher,
			BlockId::Hash(hash),
		);

		Box::new(maybe_header.then(move |result|
			ready(result.map_err(client_err)),
		).boxed().compat())
	}

	fn block(&self, hash: Option<Block::Hash>)
		-> FutureResult<Option<SignedBlock<Block>>>
	{
		let fetcher = self.fetcher.clone();
		let block = self.header(hash)
			.and_then(move |header| match header {
				Some(header) => Either::A(fetcher
					.remote_body(RemoteBodyRequest {
						header: header.clone(),
						retry_count: Default::default(),
					})
					.boxed()
					.compat()
					.map(move |body| Some(SignedBlock {
						block: Block::new(header, body),
						justification: None,
					}))
					.map_err(client_err)
				),
				None => Either::B(result(Ok(None))),
			});

		Box::new(block)
	}
}
