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

//! Substrate block-author/full-node API.

use std::sync::Arc;

use client::{self, Client};
use codec::Codec;
use extrinsic_pool::{
	api::{Error, ExtrinsicPool},
	watcher::Status,
};
use jsonrpc_macros::pubsub;
use jsonrpc_pubsub::SubscriptionId;
use primitives::Bytes;
use rpc::futures::{Sink, Stream, Future};
use runtime_primitives::{generic, traits};
use subscriptions::Subscriptions;
use tokio::runtime::TaskExecutor;

pub mod error;

#[cfg(test)]
mod tests;

use self::error::Result;

build_rpc_trait! {
	/// Substrate authoring RPC API
	pub trait AuthorApi<Hash, Extrinsic, PendingExtrinsics> {
		type Metadata;

		/// Submit extrinsic for inclusion in block.
		#[rpc(name = "author_submitRichExtrinsic")]
		fn submit_rich_extrinsic(&self, Extrinsic) -> Result<Hash>;
		/// Submit hex-encoded extrinsic for inclusion in block.
		#[rpc(name = "author_submitExtrinsic")]
		fn submit_extrinsic(&self, Bytes) -> Result<Hash>;

		/// Returns all pending extrinsics, potentially grouped by sender.
		#[rpc(name = "author_pendingExtrinsics")]
		fn pending_extrinsics(&self) -> Result<PendingExtrinsics>;

		#[pubsub(name = "author_extrinsicUpdate")] {
			/// Submit an extrinsic to watch.
			#[rpc(name = "author_submitAndWatchExtrinsic")]
			fn watch_extrinsic(&self, Self::Metadata, pubsub::Subscriber<Status<Hash>>, Bytes);

			/// Unsubscribe from extrinsic watching.
			#[rpc(name = "author_unwatchExtrinsic")]
			fn unwatch_extrinsic(&self, SubscriptionId) -> Result<bool>;
		}
	}
}

/// Authoring API
pub struct Author<B, E, Block: traits::Block, P> {
	/// Substrate client
	client: Arc<Client<B, E, Block>>,
	/// Extrinsic pool
	pool: Arc<P>,
	/// Subscriptions manager
	subscriptions: Subscriptions,
}

impl<B, E, Block: traits::Block, P> Author<B, E, Block, P> {
	/// Create new instance of Authoring API.
	pub fn new(client: Arc<Client<B, E, Block>>, pool: Arc<P>, executor: TaskExecutor) -> Self {
		Author {
			client,
			pool,
			subscriptions: Subscriptions::new(executor),
		}
	}
}

impl<B, E, Block, P, Ex, Hash, InPool> AuthorApi<Hash, Ex, InPool> for Author<B, E, Block, P> where
	B: client::backend::Backend<Block> + Send + Sync + 'static,
	E: client::CallExecutor<Block> + Send + Sync + 'static,
	Block: traits::Block + 'static,
	Hash: traits::MaybeSerializeDebug + Send + Sync + 'static,
	InPool: traits::MaybeSerializeDebug + Send + Sync + 'static,
	P: ExtrinsicPool<Ex, generic::BlockId<Block>, Hash, InPool=InPool>,
	P::Error: 'static,
	Ex: Codec,
{
	type Metadata = ::metadata::Metadata;

	fn submit_extrinsic(&self, xt: Bytes) -> Result<Hash> {
		let dxt = Ex::decode(&mut &xt[..]).ok_or(error::Error::from(error::ErrorKind::BadFormat))?;
		self.submit_rich_extrinsic(dxt)
	}

	fn submit_rich_extrinsic(&self, xt: Ex) -> Result<Hash> {
		let best_block_hash = self.client.info()?.chain.best_hash;
		self.pool
			.submit(generic::BlockId::hash(best_block_hash), vec![xt])
			.map(|mut res| res.pop().expect("One extrinsic passed; one result back; qed"))
			.map_err(|e| e.into_pool_error()
				.map(Into::into)
				.unwrap_or_else(|e| error::ErrorKind::Verification(Box::new(e)).into())
			)
	}

	fn pending_extrinsics(&self) -> Result<InPool> {
		Ok(self.pool.all())
	}

	fn watch_extrinsic(&self, _metadata: Self::Metadata, subscriber: pubsub::Subscriber<Status<Hash>>, xt: Bytes) {

		let submit = || -> Result<_> {
			let best_block_hash = self.client.info()?.chain.best_hash;
			let dxt = Ex::decode(&mut &xt[..]).ok_or(error::Error::from(error::ErrorKind::BadFormat))?;
			self.pool
				.submit_and_watch(generic::BlockId::hash(best_block_hash), dxt)
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

	fn unwatch_extrinsic(&self, id: SubscriptionId) -> Result<bool> {
		Ok(self.subscriptions.cancel(id))
	}
}

