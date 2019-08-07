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

pub mod error;
pub mod hash;

#[cfg(test)]
mod tests;

use std::{sync::Arc, convert::TryInto};

use client::{self, Client};
use crate::rpc::futures::{Sink, Stream, Future};
use crate::subscriptions::Subscriptions;
use jsonrpc_derive::rpc;
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId};
use log::warn;
use codec::{Encode, Decode};
use primitives::{
	Bytes, Blake2Hasher, H256, ed25519, sr25519, crypto::{Pair, Public, key_types},
	traits::BareCryptoStorePtr,
};
use sr_primitives::{generic, traits::{self, ProvideRuntimeApi}};
use self::error::{Error, Result};
use transaction_pool::{
	txpool::{
		ChainApi as PoolChainApi,
		BlockHash,
		ExHash,
		IntoPoolError,
		Pool,
		watcher::Status,
		SubmitExtrinsic,
	},
};
use session::SessionKeys;

pub use self::gen_client::Client as AuthorClient;

/// Substrate authoring RPC API
#[rpc]
pub trait AuthorApi<Hash, BlockHash> {
	/// RPC metadata
	type Metadata;

	/// Submit hex-encoded extrinsic for inclusion in block.
	#[rpc(name = "author_submitExtrinsic")]
	fn submit_extrinsic(&self, extrinsic: Bytes) -> Result<Hash>;

	/// Insert a key into the keystore.
	#[rpc(name = "author_insertKey")]
	fn insert_key(&self,
		key_type: String,
		suri: String,
		maybe_public: Option<Bytes>
	) -> Result<Bytes>;

	/// Generate new session keys and returns the corresponding public keys.
	#[rpc(name = "author_rotateKeys")]
	fn rotate_keys(&self) -> Result<Bytes>;

	/// Returns all pending extrinsics, potentially grouped by sender.
	#[rpc(name = "author_pendingExtrinsics")]
	fn pending_extrinsics(&self) -> Result<Vec<Bytes>>;

	/// Remove given extrinsic from the pool and temporarily ban it to prevent reimporting.
	#[rpc(name = "author_removeExtrinsic")]
	fn remove_extrinsic(&self,
		bytes_or_hash: Vec<hash::ExtrinsicOrHash<Hash>>
	) -> Result<Vec<Hash>>;

	/// Submit an extrinsic to watch.
	#[pubsub(
		subscription = "author_extrinsicUpdate",
		subscribe,
		name = "author_submitAndWatchExtrinsic"
	)]
	fn watch_extrinsic(&self,
		metadata: Self::Metadata,
		subscriber: Subscriber<Status<Hash, BlockHash>>,
		bytes: Bytes
	);

	/// Unsubscribe from extrinsic watching.
	#[pubsub(
		subscription = "author_extrinsicUpdate",
		unsubscribe,
		name = "author_unwatchExtrinsic"
	)]
	fn unwatch_extrinsic(&self,
		metadata: Option<Self::Metadata>,
		id: SubscriptionId
	) -> Result<bool>;
}

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
	B: client::backend::Backend<<P as PoolChainApi>::Block, Blake2Hasher> + Send + Sync + 'static,
	E: client::CallExecutor<<P as PoolChainApi>::Block, Blake2Hasher> + Send + Sync + 'static,
	P: PoolChainApi + Sync + Send + 'static,
	P::Block: traits::Block<Hash=H256>,
	P::Error: 'static,
	RA: Send + Sync + 'static,
	Client<B, E, P::Block, RA>: ProvideRuntimeApi,
	<Client<B, E, P::Block, RA> as ProvideRuntimeApi>::Api: SessionKeys<P::Block>,
{
	type Metadata = crate::metadata::Metadata;

	fn insert_key(
		&self,
		key_type: String,
		suri: String,
		maybe_public: Option<Bytes>,
	) -> Result<Bytes> {
		let key_type = key_type.as_str().try_into().map_err(|_| Error::BadKeyType)?;
		let mut keystore = self.keystore.write();
		let maybe_password = keystore.password();
		let public = match maybe_public {
			Some(public) => public.0,
			None => {
				let maybe_public = match key_type {
					key_types::BABE | key_types::IM_ONLINE | key_types::SR25519 =>
						sr25519::Pair::from_string(&suri, maybe_password)
							.map(|pair| pair.public().to_raw_vec()),
					key_types::GRANDPA | key_types::ED25519 =>
						ed25519::Pair::from_string(&suri, maybe_password)
							.map(|pair| pair.public().to_raw_vec()),
					_ => Err(Error::UnsupportedKeyType)?,
				};
				maybe_public.map_err(|_| Error::BadSeedPhrase)?
			}
		};
		keystore.insert_unknown(key_type, &suri, &public[..])
			.map_err(|_| Error::KeyStoreUnavailable)?;
		Ok(public.into())
	}

	fn rotate_keys(&self) -> Result<Bytes> {
		let best_block_hash = self.client.info().chain.best_hash;
		self.client.runtime_api().generate_session_keys(
			&generic::BlockId::Hash(best_block_hash),
			None,
		).map(Into::into).map_err(Into::into)
	}

	fn submit_extrinsic(&self, ext: Bytes) -> Result<ExHash<P>> {
		let xt = Decode::decode(&mut &ext[..])?;
		let best_block_hash = self.client.info().chain.best_hash;
		self.pool
			.submit_one(&generic::BlockId::hash(best_block_hash), xt)
			.map_err(|e| e.into_pool_error()
				.map(Into::into)
				.unwrap_or_else(|e| error::Error::Verification(Box::new(e)).into())
			)
	}

	fn pending_extrinsics(&self) -> Result<Vec<Bytes>> {
		Ok(self.pool.ready().map(|tx| tx.data.encode().into()).collect())
	}

	fn remove_extrinsic(&self,
		bytes_or_hash: Vec<hash::ExtrinsicOrHash<ExHash<P>>>
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
		xt: Bytes
	) {
		let submit = || -> Result<_> {
			let best_block_hash = self.client.info().chain.best_hash;
			let dxt = <<P as PoolChainApi>::Block as traits::Block>::Extrinsic::decode(&mut &xt[..])?;
			self.pool
				.submit_and_watch(&generic::BlockId::hash(best_block_hash), dxt)
				.map_err(|e| e.into_pool_error()
					.map(Into::into)
					.unwrap_or_else(|e| error::Error::Verification(Box::new(e)).into())
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
