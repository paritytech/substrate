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

//! Blockchain API backend for full nodes.

use std::sync::Arc;
use rpc::futures::future::result;

use api::Subscriptions;
use client_api::{CallExecutor, backend::Backend};
use client::Client;
use primitives::{H256, Blake2Hasher};
use sr_primitives::{
	generic::{BlockId, SignedBlock},
	traits::{Block as BlockT},
};

use super::{ChainBackend, client_err, error::FutureResult};

/// Blockchain API backend for full nodes. Reads all the data from local database.
pub struct FullChain<B, E, Block: BlockT, RA> {
	/// Substrate client.
	client: Arc<Client<B, E, Block, RA>>,
	/// Current subscriptions.
	subscriptions: Subscriptions,
}

impl<B, E, Block: BlockT, RA> FullChain<B, E, Block, RA> {
	/// Create new Chain API RPC handler.
	pub fn new(client: Arc<Client<B, E, Block, RA>>, subscriptions: Subscriptions) -> Self {
		Self {
			client,
			subscriptions,
		}
	}
}

impl<B, E, Block, RA> ChainBackend<B, E, Block, RA> for FullChain<B, E, Block, RA> where
	Block: BlockT<Hash=H256> + 'static,
	B: Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	RA: Send + Sync + 'static,
{
	fn client(&self) -> &Arc<Client<B, E, Block, RA>> {
		&self.client
	}

	fn subscriptions(&self) -> &Subscriptions {
		&self.subscriptions
	}

	fn header(&self, hash: Option<Block::Hash>) -> FutureResult<Option<Block::Header>> {
		Box::new(result(self.client
			.header(&BlockId::Hash(self.unwrap_or_best(hash)))
			.map_err(client_err)
		))
	}

	fn block(&self, hash: Option<Block::Hash>)
		-> FutureResult<Option<SignedBlock<Block>>>
	{
		Box::new(result(self.client
			.block(&BlockId::Hash(self.unwrap_or_best(hash)))
			.map_err(client_err)
		))
	}
}
