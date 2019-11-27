// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

#[cfg(test)]
mod tests;

use std::{sync::Arc, convert::TryInto};
use futures::future::{FutureExt, TryFutureExt};
use log::warn;

use client::Client;
use sp_blockchain::Error as ClientError;

use rpc::futures::{
	Sink, Future,
	future::result,
};
use futures::{StreamExt as _, compat::Compat, future::ready};
use api::Subscriptions;
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId};
use codec::{Encode, Decode};
use primitives::{Bytes, Blake2Hasher, H256, traits::BareCryptoStorePtr};
use sr_primitives::{generic, traits::{self, ProvideRuntimeApi}};
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
use session::SessionKeys;

/// Re-export the API for backward compatibility.
pub use api::author::*;
use self::error::{Error, FutureResult, Result};

/// Authoring API
pub struct Author<B, E, P, RA> where P: PoolChainApi + Sync + Send + 'static {
	/// Substrate client
	client: Arc<Client<B, E, <P as PoolChainApi>::Block, RA>>,
	/// Transactions pool
	pool: Arc<Pool<P>>,
	/// Subscriptions manager
	subscriptions: Subscriptions,
	/// The key store.
	keystore: BareCryptoStorePtr,
}

impl<B, E, P, RA> Author<B, E, P, RA> where P: PoolChainApi + Sync + Send + 'static {
	/// Create new instance of Authoring API.
	pub fn new(
		client: Arc<Client<B, E, <P as PoolChainApi>::Block, RA>>,
		pool: Arc<Pool<P>>,
		subscriptions: Subscriptions,
		keystore: BareCryptoStorePtr,
	) -> Self {
		Author {
			client,
			pool,
			subscriptions,
			keystore,
		}
	}
}

impl<B, E, P, RA> AuthorApi<ExHash<P>, BlockHash<P>> for Author<B, E, P, RA> where
	B: client_api::backend::Backend<<P as PoolChainApi>::Block, Blake2Hasher> + Send + Sync + 'static,
	E: client_api::CallExecutor<<P as PoolChainApi>::Block, Blake2Hasher> + Send + Sync + 'static,
	P: PoolChainApi + Sync + Send + 'static,
	P::Block: traits::Block<Hash=H256>,
	P::Error: 'static,
	RA: Send + Sync + 'static,
	Client<B, E, P::Block, RA>: ProvideRuntimeApi,
	<Client<B, E, P::Block, RA> as ProvideRuntimeApi>::Api:
		SessionKeys<P::Block, Error = ClientError>,
{
	type Metadata = crate::metadata::Metadata;

	fn insert_key(
		&self,
		key_type: String,
		suri: String,
		public: Bytes,
	) -> Result<()> {
		let key_type = key_type.as_str().try_into().map_err(|_| Error::BadKeyType)?;
		let mut keystore = self.keystore.write();
		keystore.insert_unknown(key_type, &suri, &public[..])
			.map_err(|_| Error::KeyStoreUnavailable)?;
		Ok(())
	}

	fn rotate_keys(&self) -> Result<Bytes> {
		let best_block_hash = self.client.info().chain.best_hash;
		self.client.runtime_api().generate_session_keys(
			&generic::BlockId::Hash(best_block_hash),
			None,
		).map(Into::into).map_err(|e| Error::Client(Box::new(e)))
	}

	fn submit_extrinsic(&self, ext: Bytes) -> FutureResult<ExHash<P>> {
		let xt = match Decode::decode(&mut &ext[..]) {
			Ok(xt) => xt,
			Err(err) => return Box::new(result(Err(err.into()))),
		};
		let best_block_hash = self.client.info().chain.best_hash;
		Box::new(self.pool
			.submit_one(&generic::BlockId::hash(best_block_hash), xt)
			.compat()
			.map_err(|e| e.into_pool_error()
				.map(Into::into)
				.unwrap_or_else(|e| error::Error::Verification(Box::new(e)).into()))
		)
	}

	fn pending_extrinsics(&self) -> Result<Vec<Bytes>> {
		Ok(self.pool.ready().map(|tx| tx.data.encode().into()).collect())
	}

	fn remove_extrinsic(
		&self,
		bytes_or_hash: Vec<hash::ExtrinsicOrHash<ExHash<P>>>,
	) -> Result<Vec<ExHash<P>>> {
		let hashes = bytes_or_hash.into_iter()
			.map(|x| match x {
				hash::ExtrinsicOrHash::Hash(h) => Ok(h),
				hash::ExtrinsicOrHash::Extrinsic(bytes) => {
					let xt = Decode::decode(&mut &bytes[..])?;
					Ok(self.pool.hash_of(&xt))
				},
			})
			.collect::<Result<Vec<_>>>()?;

		Ok(
			self.pool.remove_invalid(&hashes)
				.into_iter()
				.map(|tx| tx.hash.clone())
				.collect()
		)
	}

	fn watch_extrinsic(&self,
		_metadata: Self::Metadata,
		subscriber: Subscriber<Status<ExHash<P>, BlockHash<P>>>,
		xt: Bytes,
	) {
		let submit = || -> Result<_> {
			let best_block_hash = self.client.info().chain.best_hash;
			let dxt = <<P as PoolChainApi>::Block as traits::Block>::Extrinsic::decode(&mut &xt[..])
				.map_err(error::Error::from)?;
			Ok(
				self.pool
					.submit_and_watch(&generic::BlockId::hash(best_block_hash), dxt)
					.map_err(|e| e.into_pool_error()
						.map(error::Error::from)
						.unwrap_or_else(|e| error::Error::Verification(Box::new(e)).into())
					)
			)
		};

		let subscriptions = self.subscriptions.clone();
		let future = ready(submit())
			.and_then(|res| res)
			// convert the watcher into a `Stream`
			.map(|res| res.map(|watcher| watcher.into_stream().map(|v| Ok::<_, ()>(Ok(v)))))
			// now handle the import result,
			// start a new subscrition
			.map(move |result| match result {
				Ok(watcher) => {
					subscriptions.add(subscriber, move |sink| {
						sink
							.sink_map_err(|_| unimplemented!())
							.send_all(Compat::new(watcher))
							.map(|_| ())
					});
				},
				Err(err) => {
					warn!("Failed to submit extrinsic: {}", err);
					// reject the subscriber (ignore errors - we don't care if subscriber is no longer there).
					let _ = subscriber.reject(err.into());
				},
			});

		let res = self.subscriptions.executor()
			.execute(Box::new(Compat::new(future.map(|_| Ok(())))));
		if res.is_err() {
			warn!("Error spawning subscription RPC task.");
		}
	}

	fn unwatch_extrinsic(&self, _metadata: Option<Self::Metadata>, id: SubscriptionId) -> Result<bool> {
		Ok(self.subscriptions.cancel(id))
	}
}
