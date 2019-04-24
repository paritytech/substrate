// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//! Substrate block-author/full-node API.

use std::sync::Arc;

use log::warn;
use client::{self, Client};
use parity_codec::{Encode, Decode};
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
use jsonrpc_derive::rpc;
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId};
use primitives::{Bytes, Blake2Hasher, H256};
use crate::rpc::futures::{Sink, Stream, Future};
use runtime_primitives::{generic, traits};
use crate::subscriptions::Subscriptions;

pub mod error;

#[cfg(test)]
mod tests;

use self::error::Result;

/// Substrate authoring RPC API
#[rpc]
pub trait AuthorApi<Hash, BlockHash> {
	/// RPC metadata
	type Metadata;

	/// Submit hex-encoded extrinsic for inclusion in block.
	#[rpc(name = "author_submitExtrinsic")]
	fn submit_extrinsic(&self, extrinsic: Bytes) -> Result<Hash>;

	/// Returns all pending extrinsics, potentially grouped by sender.
	#[rpc(name = "author_pendingExtrinsics")]
	fn pending_extrinsics(&self) -> Result<Vec<Bytes>>;

	/// Submit an extrinsic to watch.
	#[pubsub(subscription = "author_extrinsicUpdate", subscribe, name = "author_submitAndWatchExtrinsic")]
	fn watch_extrinsic(&self, metadata: Self::Metadata, subscriber: Subscriber<Status<Hash, BlockHash>>, bytes: Bytes);

	/// Unsubscribe from extrinsic watching.
	#[pubsub(subscription = "author_extrinsicUpdate", unsubscribe, name = "author_unwatchExtrinsic")]
	fn unwatch_extrinsic(&self, metadata: Option<Self::Metadata>, id: SubscriptionId) -> Result<bool>;
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
	type Metadata = crate::metadata::Metadata;

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

	fn watch_extrinsic(&self, _metadata: Self::Metadata, subscriber: Subscriber<Status<ExHash<P>, BlockHash<P>>>, xt: Bytes) {
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

	fn unwatch_extrinsic(&self, _metadata: Option<Self::Metadata>, id: SubscriptionId) -> Result<bool> {
		Ok(self.subscriptions.cancel(id))
	}
}
