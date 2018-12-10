// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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
use jsonrpc_macros::{pubsub, Trailing};
use jsonrpc_pubsub::SubscriptionId;
use primitives::{H256, Blake2Hasher};
use rpc::Result as RpcResult;
use rpc::futures::{stream, Future, Sink, Stream};
use runtime_primitives::generic::{BlockId, SignedBlock};
use runtime_primitives::traits::{Block as BlockT, Header, NumberFor};

use subscriptions::Subscriptions;

mod error;
#[cfg(test)]
mod tests;

use self::error::Result;

build_rpc_trait! {
	/// Substrate blockchain API
	pub trait ChainApi<Hash, Header, Number, SignedBlock> {
		type Metadata;

		/// Get header of a relay chain block.
		#[rpc(name = "chain_getHeader")]
		fn header(&self, Trailing<Hash>) -> Result<Option<Header>>;

		/// Get header and body of a relay chain block.
		#[rpc(name = "chain_getBlock")]
		fn block(&self, Trailing<Hash>) -> Result<Option<SignedBlock>>;

		/// Get hash of the n-th block in the canon chain.
		///
		/// By default returns latest block hash.
		#[rpc(name = "chain_getBlockHash", alias = ["chain_getHead", ])]
		fn block_hash(&self, Trailing<Number>) -> Result<Option<Hash>>;

		/// Get hash of the last finalised block in the canon chain.
		#[rpc(name = "chain_getFinalisedHead")]
		fn finalised_head(&self) -> Result<Hash>;

		#[pubsub(name = "chain_newHead")] {
			/// New head subscription
			#[rpc(name = "chain_subscribeNewHead", alias = ["subscribe_newHead", ])]
			fn subscribe_new_head(&self, Self::Metadata, pubsub::Subscriber<Header>);

			/// Unsubscribe from new head subscription.
			#[rpc(name = "chain_unsubscribeNewHead", alias = ["unsubscribe_newHead", ])]
			fn unsubscribe_new_head(&self, Self::Metadata, SubscriptionId) -> RpcResult<bool>;
		}

		#[pubsub(name = "chain_finalisedHead")] {
			/// New head subscription
			#[rpc(name = "chain_subscribeFinalisedHeads")]
			fn subscribe_finalised_heads(&self, Self::Metadata, pubsub::Subscriber<Header>);

			/// Unsubscribe from new head subscription.
			#[rpc(name = "chain_unsubscribeFinalisedHeads")]
			fn unsubscribe_finalised_heads(&self, Self::Metadata, SubscriptionId) -> RpcResult<bool>;
		}
	}
}

/// Chain API with subscriptions support.
pub struct Chain<B, E, Block: BlockT, RA> {
	/// Substrate client.
	client: Arc<Client<B, E, Block, RA>>,
	/// Current subscriptions.
	subscriptions: Subscriptions,
}

impl<B, E, Block: BlockT, RA> Chain<B, E, Block, RA> {
	/// Create new Chain API RPC handler.
	pub fn new(client: Arc<Client<B, E, Block, RA>>, subscriptions: Subscriptions) -> Self {
		Self {
			client,
			subscriptions,
		}
	}
}

impl<B, E, Block, RA> Chain<B, E, Block, RA> where
	Block: BlockT<Hash=H256> + 'static,
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: client::CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	RA: Send + Sync + 'static
{
	fn unwrap_or_best(&self, hash: Trailing<Block::Hash>) -> Result<Block::Hash> {
		Ok(match hash.into() {
			None => self.client.info()?.chain.best_hash,
			Some(hash) => hash,
		})
	}

	fn subscribe_headers<F, G, S, ERR>(
		&self,
		subscriber: pubsub::Subscriber<Block::Header>,
		best_block_hash: G,
		stream: F,
	) where
		F: FnOnce() -> S,
		G: FnOnce() -> Result<Option<Block::Hash>>,
		ERR: ::std::fmt::Debug,
		S: Stream<Item=Block::Header, Error=ERR> + Send + 'static,
	{
		self.subscriptions.add(subscriber, |sink| {
			// send current head right at the start.
			let header = best_block_hash()
				.and_then(|hash| self.header(hash.into()))
				.and_then(|header| {
					header.ok_or_else(|| self::error::ErrorKind::Unimplemented.into())
				})
				.map_err(Into::into);

			// send further subscriptions
			let stream = stream()
				.map(|res| Ok(res))
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
}

impl<B, E, Block, RA> ChainApi<Block::Hash, Block::Header, NumberFor<Block>, SignedBlock<Block>> for Chain<B, E, Block, RA> where
	Block: BlockT<Hash=H256> + 'static,
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: client::CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
	RA: Send + Sync + 'static
{
	type Metadata = ::metadata::Metadata;

	fn header(&self, hash: Trailing<Block::Hash>) -> Result<Option<Block::Header>> {
		let hash = self.unwrap_or_best(hash)?;
		Ok(self.client.header(&BlockId::Hash(hash))?)
	}

	fn block(&self, hash: Trailing<Block::Hash>)
		-> Result<Option<SignedBlock<Block>>>
	{
		let hash = self.unwrap_or_best(hash)?;
		Ok(self.client.block(&BlockId::Hash(hash))?)
	}

	fn block_hash(&self, number: Trailing<NumberFor<Block>>) -> Result<Option<Block::Hash>> {
		Ok(match number.into() {
			None => Some(self.client.info()?.chain.best_hash),
			Some(number) => self.client.header(&BlockId::number(number))?.map(|h| h.hash()),
		})
	}

	fn finalised_head(&self) -> Result<Block::Hash> {
		Ok(self.client.info()?.chain.finalized_hash)
	}

	fn subscribe_new_head(&self, _metadata: Self::Metadata, subscriber: pubsub::Subscriber<Block::Header>) {
		self.subscribe_headers(
			subscriber,
			|| self.block_hash(None.into()),
			|| self.client.import_notification_stream()
				.filter(|notification| notification.is_new_best)
				.map(|notification| notification.header),
		)
	}

	fn unsubscribe_new_head(&self, _metadata: Self::Metadata, id: SubscriptionId) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}

	fn subscribe_finalised_heads(&self, _meta: Self::Metadata, subscriber: pubsub::Subscriber<Block::Header>) {
		self.subscribe_headers(
			subscriber,
			|| Ok(Some(self.client.info()?.chain.finalized_hash)),
			|| self.client.finality_notification_stream()
				.map(|notification| notification.header),
		)
	}

	fn unsubscribe_finalised_heads(&self, _metadata: Self::Metadata, id: SubscriptionId) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}
}
