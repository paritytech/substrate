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
use client::{BlockchainEvents, ChainHead, ChainData};

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
pub struct Chain {
	/// Chain head shared instance.
	chain_head: Arc<ChainHead>,
	/// Chain data shared instance.
	chain_data: Arc<ChainData>,
	/// Blockchain events shared instance.
	chain_events: Arc<BlockchainEvents>,
	/// Current subscriptions.
	subscriptions: Subscriptions,
}

impl Chain {
	/// Create new Chain API RPC handler.
	pub fn new(chain_head: Arc<ChainHead>, chain_data: Arc<ChainData>, chain_events: Arc<BlockchainEvents>, remote: Remote) -> Self {
		Chain {
			chain_head,
			chain_data,
			chain_events,
			subscriptions: Subscriptions::new(remote),
		}
	}
}

impl ChainApi for Chain {
	type Metadata = ::metadata::Metadata;

	fn header(&self, hash: block::HeaderHash) -> Result<Option<block::Header>> {
		self.chain_data.header(&block::Id::Hash(hash)).chain_err(|| "Blockchain error")
	}

	fn head(&self) -> Result<block::HeaderHash> {
		self.chain_head.best_block_hash().chain_err(|| "Blockchain error")
	}

	fn subscribe_new_head(&self, _metadata: Self::Metadata, subscriber: pubsub::Subscriber<block::Header>) {
		self.subscriptions.add(subscriber, |sink| {
			let stream = self.chain_events.import_notification_stream()
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
