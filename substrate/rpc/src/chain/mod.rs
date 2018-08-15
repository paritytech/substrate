// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Substrate blockchain API.

use std::sync::Arc;

use client::{self, Client, BlockchainEvents};
use jsonrpc_macros::pubsub;
use jsonrpc_pubsub::SubscriptionId;
use rpc::Result as RpcResult;
use rpc::futures::{stream, Future, Sink, Stream};
use runtime_primitives::generic::{BlockId, SignedBlock};
use runtime_primitives::traits::Block as BlockT;
use tokio::runtime::TaskExecutor;
use primitives::{KeccakHasher, RlpCodec};

use subscriptions::Subscriptions;

mod error;
#[cfg(test)]
mod tests;

use self::error::Result;

build_rpc_trait! {
	/// Polkadot blockchain API
	pub trait ChainApi<Hash, Header, Extrinsic> {
		type Metadata;

		/// Get header of a relay chain block.
		#[rpc(name = "chain_getHeader")]
		fn header(&self, Hash) -> Result<Option<Header>>;

		/// Get header and body of a relay chain block.
		#[rpc(name = "chain_getBlock")]
		fn block(&self, Hash) -> Result<Option<SignedBlock<Header, Extrinsic, Hash>>>;

		/// Get hash of the head.
		#[rpc(name = "chain_getHead")]
		fn head(&self) -> Result<Hash>;

		#[pubsub(name = "chain_newHead")] {
			/// New head subscription
			#[rpc(name = "chain_subscribeNewHead", alias = ["subscribe_newHead", ])]
			fn subscribe_new_head(&self, Self::Metadata, pubsub::Subscriber<Header>);

			/// Unsubscribe from new head subscription.
			#[rpc(name = "chain_unsubscribeNewHead", alias = ["unsubscribe_newHead", ])]
			fn unsubscribe_new_head(&self, SubscriptionId) -> RpcResult<bool>;
		}
	}
}

/// Chain API with subscriptions support.
pub struct Chain<B, E, Block: BlockT> {
	/// Substrate client.
	client: Arc<Client<B, E, Block>>,
	/// Current subscriptions.
	subscriptions: Subscriptions,
}

impl<B, E, Block: BlockT> Chain<B, E, Block> {
	/// Create new Chain API RPC handler.
	pub fn new(client: Arc<Client<B, E, Block>>, executor: TaskExecutor) -> Self {
		Self {
			client,
			subscriptions: Subscriptions::new(executor),
		}
	}
}

impl<B, E, Block> ChainApi<Block::Hash, Block::Header, Block::Extrinsic> for Chain<B, E, Block> where
	Block: BlockT + 'static,
	B: client::backend::Backend<Block, KeccakHasher, RlpCodec> + Send + Sync + 'static,
	E: client::CallExecutor<Block, KeccakHasher, RlpCodec> + Send + Sync + 'static,
{
	type Metadata = ::metadata::Metadata;

	fn header(&self, hash: Block::Hash) -> Result<Option<Block::Header>> {
		Ok(self.client.header(&BlockId::Hash(hash))?)
	}

	fn block(&self, hash: Block::Hash) -> Result<Option<SignedBlock<Block::Header, Block::Extrinsic, Block::Hash>>> {
		Ok(self.client.block(&BlockId::Hash(hash))?)
	}

	fn head(&self) -> Result<Block::Hash> {
		Ok(self.client.info()?.chain.best_hash)
	}

	fn subscribe_new_head(&self, _metadata: Self::Metadata, subscriber: pubsub::Subscriber<Block::Header>) {
		self.subscriptions.add(subscriber, |sink| {
			// send current head right at the start.
			let header = self.head()
				.and_then(|hash| self.header(hash))
				.and_then(|header| {
					header.ok_or_else(|| self::error::ErrorKind::Unimplemented.into())
				})
				.map_err(Into::into);

			// send further subscriptions
			let stream = self.client.import_notification_stream()
				.filter(|notification| notification.is_new_best)
				.map(|notification| Ok(notification.header))
				.map_err(|e| warn!("Block notification stream error: {:?}", e));

			sink
				.sink_map_err(|e| warn!("Error sending notifications: {:?}", e))
				.send_all(
					stream::iter_result(vec![Ok(header)])
						.chain(stream)
				)
				// we ignore the resulting Stream (if the first stream is over we are unsubscribed)
				.map(|_| ())
		});
	}

	fn unsubscribe_new_head(&self, id: SubscriptionId) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}
}
