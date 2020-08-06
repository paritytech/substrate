// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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
use jsonrpc_pubsub::manager::SubscriptionManager;

use sc_client_api::{BlockchainEvents, BlockBackend};
use sp_runtime::{generic::{BlockId, SignedBlock}, traits::{Block as BlockT}};

use super::{ChainBackend, client_err, error::FutureResult};
use std::marker::PhantomData;
use sp_blockchain::HeaderBackend;

/// Blockchain API backend for full nodes. Reads all the data from local database.
pub struct FullChain<Block: BlockT, Client> {
	/// Substrate client.
	client: Arc<Client>,
	/// Current subscriptions.
	subscriptions: SubscriptionManager,
	/// phantom member to pin the block type
	_phantom: PhantomData<Block>,
}

impl<Block: BlockT, Client> FullChain<Block, Client> {
	/// Create new Chain API RPC handler.
	pub fn new(client: Arc<Client>, subscriptions: SubscriptionManager) -> Self {
		Self {
			client,
			subscriptions,
			_phantom: PhantomData,
		}
	}
}

impl<Block, Client> ChainBackend<Client, Block> for FullChain<Block, Client> where
	Block: BlockT + 'static,
	Client: BlockBackend<Block> + HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	fn client(&self) -> &Arc<Client> {
		&self.client
	}

	fn subscriptions(&self) -> &SubscriptionManager {
		&self.subscriptions
	}

	fn header(&self, hash: Option<Block::Hash>) -> FutureResult<Option<Block::Header>> {
		Box::new(result(self.client
			.header(BlockId::Hash(self.unwrap_or_best(hash)))
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
