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

//! Substrate block-author/full-node API.

use std::sync::Arc;

use client::{self, Client};
use codec::{Encode, Decode};
use transaction_pool::{
	txpool::{
		ChainApi as PoolChainApi,
		BlockHash,
		ExHash,
		IntoPoolError,
		Pool,
		watcher::Status,
	},
};
use jsonrpc_macros::pubsub;
use jsonrpc_pubsub::SubscriptionId;
use primitives::{Bytes, Blake2Hasher, H256};
use rpc::futures::{Sink, Stream, Future};
use runtime_primitives::{generic, traits};
use subscriptions::Subscriptions;

pub mod error;

#[cfg(test)]
mod tests;

use self::error::Result;

build_rpc_trait! {
	/// Substrate authoring RPC API
	pub trait AuthorApi<Hash, BlockHash> {
		type Metadata;

		/// Submit hex-encoded extrinsic for inclusion in block.
		#[rpc(name = "author_submitExtrinsic")]
		fn submit_extrinsic(&self, Bytes) -> Result<Hash>;

		/// Returns all pending extrinsics, potentially grouped by sender.
		#[rpc(name = "author_pendingExtrinsics")]
		fn pending_extrinsics(&self) -> Result<Vec<Bytes>>;

		#[pubsub(name = "author_extrinsicUpdate")] {
			/// Submit an extrinsic to watch.
			#[rpc(name = "author_submitAndWatchExtrinsic")]
			fn watch_extrinsic(&self, Self::Metadata, pubsub::Subscriber<Status<Hash, BlockHash>>, Bytes);

			/// Unsubscribe from extrinsic watching.
			#[rpc(name = "author_unwatchExtrinsic")]
			fn unwatch_extrinsic(&self, Self::Metadata, SubscriptionId) -> Result<bool>;
		}

	}
}

/// Authoring API
pub struct Author<B, E, P, RA> where P: PoolChainApi + Sync + Send + 'static {
	/// Substrate client
	client: Arc<Client<B, E, <P as PoolChainApi>::Block, RA>>,
	/// Extrinsic pool
	pool: Arc<Pool<P>>,
	/// Subscriptions manager
	subscriptions: Subscriptions,
}

impl<B, E, P, RA> Author<B, E, P, RA> where P: PoolChainApi + Sync + Send + 'static {
	/// Create new instance of Authoring API.
	pub fn new(
		client: Arc<Client<B, E, <P as PoolChainApi>::Block, RA>>,
		pool: Arc<Pool<P>>,
		subscriptions: Subscriptions,
	) -> Self {
		Author {
			client,
			pool,
			subscriptions,
		}
	}
}

impl<B, E, P, RA> AuthorApi<ExHash<P>, BlockHash<P>> for Author<B, E, P, RA> where
	B: client::backend::Backend<<P as PoolChainApi>::Block, Blake2Hasher> + Send + Sync + 'static,
	E: client::CallExecutor<<P as PoolChainApi>::Block, Blake2Hasher> + Send + Sync + 'static,
	P: PoolChainApi + Sync + Send + 'static,
	P::Block: traits::Block<Hash=H256>,
	P::Error: 'static,
	RA: Send + Sync + 'static
{
	type Metadata = ::metadata::Metadata;

	fn submit_extrinsic(&self, ext: Bytes) -> Result<ExHash<P>> {
		let xt = Decode::decode(&mut &ext[..]).ok_or(error::Error::from(error::ErrorKind::BadFormat))?;
		let best_block_hash = self.client.info()?.chain.best_hash;
		self.pool
			.submit_one(&generic::BlockId::hash(best_block_hash), xt)
			.map_err(|e| e.into_pool_error()
				.map(Into::into)
				.unwrap_or_else(|e| error::ErrorKind::Verification(Box::new(e)).into())
			)
	}

	fn pending_extrinsics(&self) -> Result<Vec<Bytes>> {
		Ok(self.pool.ready().map(|tx| tx.data.encode().into()).collect())
	}

	fn watch_extrinsic(&self, _metadata: Self::Metadata, subscriber: pubsub::Subscriber<Status<ExHash<P>, BlockHash<P>>>, xt: Bytes) {
		let submit = || -> Result<_> {
			let best_block_hash = self.client.info()?.chain.best_hash;
			let dxt = <<P as PoolChainApi>::Block as traits::Block>::Extrinsic::decode(&mut &xt[..]).ok_or(error::Error::from(error::ErrorKind::BadFormat))?;
			self.pool
				.submit_and_watch(&generic::BlockId::hash(best_block_hash), dxt)
				.map_err(|e| e.into_pool_error()
					.map(Into::into)
					.unwrap_or_else(|e| error::ErrorKind::Verification(Box::new(e)).into())
				)
		};

		let watcher = match submit() {
			Ok(watcher) => watcher,
			Err(err) => {
				// reject the subscriber (ignore errors - we don't care if subscriber is no longer there).
				let _ = subscriber.reject(err.into());
				return;
			},
		};

		self.subscriptions.add(subscriber, move |sink| {
			sink
				.sink_map_err(|e| warn!("Error sending notifications: {:?}", e))
				.send_all(watcher.into_stream().map(Ok))
				.map(|_| ())
		})
	}

	fn unwatch_extrinsic(&self, _metadata: Self::Metadata, id: SubscriptionId) -> Result<bool> {
		Ok(self.subscriptions.cancel(id))
	}
}
