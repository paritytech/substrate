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
use jsonrpc_macros::{pubsub, Trailing};
use jsonrpc_pubsub::SubscriptionId;
use rpc::Result as RpcResult;
use rpc::futures::{stream, Future, Sink, Stream};
use runtime_primitives::generic::{BlockId, SignedBlock};
use runtime_primitives::traits::{Block as BlockT, Header, NumberFor};
use runtime_version::RuntimeVersion;
use primitives::{Blake2Hasher};

use subscriptions::Subscriptions;

mod error;
#[cfg(test)]
mod tests;

use self::error::Result;

build_rpc_trait! {
	/// Substrate blockchain API
	pub trait ChainApi<Hash, Header, Number, Extrinsic> {
		type Metadata;

		/// Get header of a relay chain block.
		#[rpc(name = "chain_getHeader")]
		fn header(&self, Trailing<Hash>) -> Result<Option<Header>>;

		/// Get header and body of a relay chain block.
		#[rpc(name = "chain_getBlock")]
		fn block(&self, Trailing<Hash>) -> Result<Option<SignedBlock<Header, Extrinsic, Hash>>>;

		/// Get hash of the n-th block in the canon chain.
		///
		/// By default returns latest block hash.
		#[rpc(name = "chain_getBlockHash", alias = ["chain_getHead", ])]
		fn block_hash(&self, Trailing<Number>) -> Result<Option<Hash>>;

		/// Get the runtime version.
		#[rpc(name = "chain_getRuntimeVersion")]
		fn runtime_version(&self, Trailing<Hash>) -> Result<RuntimeVersion>;

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
	pub fn new(client: Arc<Client<B, E, Block>>, subscriptions: Subscriptions) -> Self {
		Self {
			client,
			subscriptions,
		}
	}
}

impl<B, E, Block> Chain<B, E, Block> where
	Block: BlockT + 'static,
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: client::CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
{
	fn unwrap_or_best(&self, hash: Trailing<Block::Hash>) -> Result<Block::Hash> {
		Ok(match hash.into() {
			None => self.client.info()?.chain.best_hash,
			Some(hash) => hash,
		})
	}
}

impl<B, E, Block> ChainApi<Block::Hash, Block::Header, NumberFor<Block>, Block::Extrinsic> for Chain<B, E, Block> where
	Block: BlockT + 'static,
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: client::CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static,
{
	type Metadata = ::metadata::Metadata;

	fn header(&self, hash: Trailing<Block::Hash>) -> Result<Option<Block::Header>> {
		let hash = self.unwrap_or_best(hash)?;
		Ok(self.client.header(&BlockId::Hash(hash))?)
	}

	fn block(&self, hash: Trailing<Block::Hash>) -> Result<Option<SignedBlock<Block::Header, Block::Extrinsic, Block::Hash>>> {
		let hash = self.unwrap_or_best(hash)?;
		Ok(self.client.block(&BlockId::Hash(hash))?)
	}

	fn block_hash(&self, number: Trailing<NumberFor<Block>>) -> Result<Option<Block::Hash>> {
		Ok(match number.into() {
			None => Some(self.client.info()?.chain.best_hash),
			Some(number) => self.client.header(&BlockId::number(number))?.map(|h| h.hash()),
		})
	}

	fn runtime_version(&self, at: Trailing<Block::Hash>) -> Result<RuntimeVersion> {
		let at = self.unwrap_or_best(at)?;
		Ok(self.client.runtime_version_at(&BlockId::Hash(at))?)
	}

	fn subscribe_new_head(&self, _metadata: Self::Metadata, subscriber: pubsub::Subscriber<Block::Header>) {
		self.subscriptions.add(subscriber, |sink| {
			// send current head right at the start.
			let header = self.block_hash(None.into())
				.and_then(|hash| self.header(hash.into()))
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
