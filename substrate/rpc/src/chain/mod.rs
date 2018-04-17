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

use primitives::block;
use client::{self, Client, BlockchainEvents};
use state_machine;

use jsonrpc_macros::pubsub;
use jsonrpc_pubsub::SubscriptionId;
use rpc::Result as RpcResult;
use rpc::futures::{Future, Sink, Stream};
use tokio_core::reactor::Remote;

use subscriptions::Subscriptions;

mod error;
#[cfg(test)]
mod tests;

use self::error::{Result, ResultExt};

build_rpc_trait! {
	/// Polkadot blockchain API
	pub trait ChainApi {
		type Metadata;

		/// Get header of a relay chain block.
		#[rpc(name = "chain_getHeader")]
		fn header(&self, block::HeaderHash) -> Result<Option<block::Header>>;

		/// Get hash of the head.
		#[rpc(name = "chain_getHead")]
		fn head(&self) -> Result<block::HeaderHash>;

		#[pubsub(name = "chain_newHead")] {
			/// Hello subscription
			#[rpc(name = "subscribe_newHead")]
			fn subscribe_new_head(&self, Self::Metadata, pubsub::Subscriber<block::Header>);

			/// Unsubscribe from hello subscription.
			#[rpc(name = "unsubscribe_newHead")]
			fn unsubscribe_new_head(&self, SubscriptionId) -> RpcResult<bool>;
		}
	}
}

/// Chain API with subscriptions support.
pub struct Chain<B, E> {
	/// Substrate client.
	client: Arc<Client<B, E>>,
	/// Current subscriptions.
	subscriptions: Subscriptions,
}

impl<B, E> Chain<B, E> {
	/// Create new Chain API RPC handler.
	pub fn new(client: Arc<Client<B, E>>, remote: Remote) -> Self {
		Chain {
			client,
			subscriptions: Subscriptions::new(remote),
		}
	}
}

impl<B, E> ChainApi for Chain<B, E> where
	B: client::backend::Backend + Send + Sync + 'static,
	E: state_machine::CodeExecutor + Send + Sync + 'static,
	client::error::Error: From<<<B as client::backend::Backend>::State as state_machine::backend::Backend>::Error>,
{
	type Metadata = ::metadata::Metadata;

	fn header(&self, hash: block::HeaderHash) -> Result<Option<block::Header>> {
		self.client.header(&block::Id::Hash(hash)).chain_err(|| "Blockchain error")
	}

	fn head(&self) -> Result<block::HeaderHash> {
		Ok(self.client.info().chain_err(|| "Blockchain error")?.chain.best_hash)
	}

	fn subscribe_new_head(&self, _metadata: Self::Metadata, subscriber: pubsub::Subscriber<block::Header>) {
		self.subscriptions.add(subscriber, |sink| {
			let stream = self.client.import_notification_stream()
				.filter(|notification| notification.is_new_best)
				.map(|notification| Ok(notification.header))
				.map_err(|e| warn!("Block notification stream error: {:?}", e));
			sink
				.sink_map_err(|e| warn!("Error sending notifications: {:?}", e))
				.send_all(stream)
				// we ignore the resulting Stream (if the first stream is over we are unsubscribed)
				.map(|_| ())
		});
	}

	fn unsubscribe_new_head(&self, id: SubscriptionId) -> RpcResult<bool> {
		Ok(self.subscriptions.cancel(id))
	}
}
