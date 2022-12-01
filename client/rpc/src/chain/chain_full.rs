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

use super::{client_err, error::FutureResult, ChainBackend};
use futures::FutureExt;
use jsonrpc_pubsub::manager::SubscriptionManager;
use sc_client_api::{BlockBackend, BlockchainEvents};
use sp_blockchain::HeaderBackend;
use sp_runtime::{
	generic::{BlockId, SignedBlock},
	traits::Block as BlockT,
};
use std::{marker::PhantomData, sync::Arc};

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
		Self { client, subscriptions, _phantom: PhantomData }
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

	fn subscriptions(&self) -> &SubscriptionManager {
		&self.subscriptions
	}

	fn header(&self, hash: Option<Block::Hash>) -> FutureResult<Option<Block::Header>> {
		let res = self.client.header(BlockId::Hash(self.unwrap_or_best(hash))).map_err(client_err);
		async move { res }.boxed()
	}

	fn block(&self, hash: Option<Block::Hash>) -> FutureResult<Option<SignedBlock<Block>>> {
		let res = self.client.block(&BlockId::Hash(self.unwrap_or_best(hash))).map_err(client_err);
		async move { res }.boxed()
	}
}
