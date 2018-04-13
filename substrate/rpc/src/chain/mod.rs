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
use client::{self, Client};
use state_machine;

use jsonrpc_pubsub::SubscriptionId;
use jsonrpc_macros::pubsub;
use rpc::futures::Future;

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

impl<B, E> ChainApi for Arc<Client<B, E>> where
	B: client::backend::Backend + Send + Sync + 'static,
	E: state_machine::CodeExecutor + Send + Sync + 'static,
	client::error::Error: From<<<B as client::backend::Backend>::State as state_machine::backend::Backend>::Error>,
{
	type Metadata = ::metadata::Metadata;

	fn header(&self, hash: block::HeaderHash) -> Result<Option<block::Header>> {
		client::Client::header(self, &block::Id::Hash(hash)).chain_err(|| "Blockchain error")
	}

	fn head(&self) -> Result<block::HeaderHash> {
		Ok(self.info().chain_err(|| "Blockchain error")?.chain.best_hash)
	}

	fn subscribe_new_head(&self, _metadata: Self::Metadata, subscriber: pubsub::Subscriber<block::Header>) {
		let (tx, rx) = ::std::sync::mpsc::sync_channel(1);
		let client = self.clone();
		let handle = ::std::thread::spawn(move || {
			let sink = subscriber.assign_id(1.into()).unwrap();
			let mut last_value = None;
			loop {
				if let Ok(()) = rx.recv_timeout(::std::time::Duration::from_millis(100)) {
					return;
				}
				let head = client.head().and_then(|h| client.header(h)).ok();
				if last_value != head {
					last_value = head.clone();
					if let Some(Some(head)) = head {
						sink.notify(Ok(head)).wait().unwrap();
					}
				}
			}
		});
	}

	fn unsubscribe_new_head(&self, id: SubscriptionId) -> RpcResult<bool> {
		unimplemented!()
	}
}
