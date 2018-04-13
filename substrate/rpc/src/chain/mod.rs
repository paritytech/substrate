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
use client;
use state_machine;

use jsonrpc_pubsub::SubscriptionId;
use jsonrpc_macros::pubsub;

mod error;

#[cfg(test)]
mod tests;

use self::error::{Result, ResultExt};
use rpc::Result as RpcResult;

build_rpc_trait! {
	/// Polkadot blockchain API
	pub trait ChainApi {
		type Metadata;

		/// Get header of a relay chain block.
		#[rpc(name = "chain_getHeader")]
		fn header(&self, block::HeaderHash) -> Result<Option<block::Header>>;

		#[pubsub(name = "chain_newHeader")] {
			/// Hello subscription
			#[rpc(name = "subscribe_newHeader")]
			fn subscribe(&self, Self::Metadata, pubsub::Subscriber<block::Header>);

			/// Unsubscribe from hello subscription.
			#[rpc(name = "unsubscribe_newHeader")]
			fn unsubscribe(&self, SubscriptionId) -> RpcResult<bool>;
		}
	}
}

impl<B, E> ChainApi for Arc<client::Client<B, E>> where
	B: client::backend::Backend + Send + Sync + 'static,
	E: state_machine::CodeExecutor + Send + Sync + 'static,
	client::error::Error: From<<<B as client::backend::Backend>::State as state_machine::backend::Backend>::Error>,
{
	type Metadata = ::metadata::Metadata;

	fn header(&self, hash: block::HeaderHash) -> Result<Option<block::Header>> {
		client::Client::header(self, &block::Id::Hash(hash)).chain_err(|| "Blockchain error")
	}

	fn subscribe(&self, _metadata: Self::Metadata, subscriber: pubsub::Subscriber<block::Header>) {

	}

	fn unsubscribe(&self, id: SubscriptionId) -> RpcResult<bool> {
		unimplemented!()
	}
}
