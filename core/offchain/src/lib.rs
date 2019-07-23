// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Substrate offchain workers.
//!
//! The offchain workers is a special function of the runtime that
//! gets executed after block is imported. During execution
//! it's able to asynchronously submit extrinsics that will either
//! be propagated to other nodes added to the next block
//! produced by the node as unsigned transactions.
//!
//! Offchain workers can be used for computation-heavy tasks
//! that are not feasible for execution during regular block processing.
//! It can either be tasks that no consensus is required for,
//! or some form of consensus over the data can be built on-chain
//! for instance via:
//! 1. Challenge period for incorrect computations
//! 2. Majority voting for results
//! 3. etc

#![warn(missing_docs)]

use std::{
	collections::HashMap,
	fmt,
	marker::PhantomData,
	sync::Arc,
};

use client::runtime_api::ApiExt;
use log::{debug, warn};
use primitives::{
	ExecutionContext,
	crypto::{self, Public},
};
use runtime_primitives::{
	generic::BlockId,
	traits::{self, ProvideRuntimeApi},
};
use futures::future::Future;
use transaction_pool::txpool::{Pool, ChainApi};
use network::NetworkStateInfo;

mod api;

pub mod testing;

pub use offchain_primitives::OffchainWorkerApi;

/// Trait that allows boxing keys for the offchain api.
pub trait OffchainKey {
	/// Return the public key as a byte vector.
	fn public(&self) -> Result<Vec<u8>, ()>;
	/// Sign data and return the signature as a byte vector.
	fn sign(&self, data: &[u8]) -> Result<Vec<u8>, ()>;
	/// Verify if the msg matches the signature.
	fn verify(&self, msg: &[u8], signature: &[u8]) -> Result<bool, ()>;
}

impl<T: crypto::Pair> OffchainKey for T {
	fn public(&self) -> Result<Vec<u8>, ()> {
		Ok(<Self as crypto::Pair>::public(&self).to_raw_vec())
	}

	fn sign(&self, data: &[u8]) -> Result<Vec<u8>, ()> {
		let sig = <Self as crypto::Pair>::sign(&self, data);
		let bytes: &[u8] = sig.as_ref();
		Ok(bytes.to_vec())
	}

	fn verify(&self, msg: &[u8], signature: &[u8]) -> Result<bool, ()> {
		Ok(Self::verify_weak(signature, msg, <Self as crypto::Pair>::public(&self)))
	}
}

/// The trait to implement a key provider.
pub trait AuthorityKeyProvider<BlockT: traits::Block> {
	/// Returns the key configured at a given block id.
	fn authority_key(&self, at: &BlockId<BlockT>) -> Option<Box<dyn OffchainKey>>;
}

/// Handles registering and querying `AuthorityKeyProvider` implementations.
pub struct AuthorityKeyProviders<BlockT: traits::Block> {
	providers: HashMap<crypto::KeyProviderId, Box<dyn AuthorityKeyProvider<BlockT>>>
}

impl<BlockT: traits::Block> AuthorityKeyProviders<BlockT> {
	/// Creates a new AuthorityKeyProviders.
	pub fn new() -> Self {
		Self {
			providers: Default::default()
		}
	}

	/// Register an AuthorityKeyProvider.
	pub fn register(
		&mut self,
		kind: crypto::KeyProviderId,
		provider: impl AuthorityKeyProvider<BlockT> + 'static,
	) {
		self.providers.insert(kind, Box::new(provider));
	}

	/// Query the registered AuthorityKeyProvider's for a key.
	pub fn authority_key(
		&self,
		kind: crypto::KeyProviderId,
		at: &BlockId<BlockT>,
	) -> Option<Box<dyn OffchainKey>> {
		self.providers.get(&kind)
			.map(|provider| provider.authority_key(at))
			.unwrap_or(None)
	}
}

/// An offchain workers manager.
pub struct OffchainWorkers<
	Client,
	Storage,
	Block: traits::Block,
> {
	client: Arc<Client>,
	db: Storage,
	key_provider: Arc<AuthorityKeyProviders<Block>>,
	keys_password: crypto::Protected<String>,
	_block: PhantomData<Block>,
}

impl<Client, Storage, Block: traits::Block> OffchainWorkers<
	Client,
	Storage,
	Block,
> {
	/// Creates new `OffchainWorkers`.
	pub fn new(
		client: Arc<Client>,
		db: Storage,
		key_provider: Arc<AuthorityKeyProviders<Block>>,
		keys_password: crypto::Protected<String>,
	) -> Self {
		Self {
			client,
			db,
			key_provider,
			keys_password,
			_block: PhantomData,
		}
	}
}

impl<Client, Storage, Block: traits::Block> fmt::Debug for OffchainWorkers<
	Client,
	Storage,
	Block,
> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_tuple("OffchainWorkers").finish()
	}
}

impl<Client, Storage, Block> OffchainWorkers<
	Client,
	Storage,
	Block,
> where
	Block: traits::Block,
	Client: ProvideRuntimeApi + Send + Sync + 'static,
	Client::Api: OffchainWorkerApi<Block>,
	Storage: client::backend::OffchainStorage + 'static,
{
	/// Start the offchain workers after given block.
	#[must_use]
	pub fn on_block_imported<A>(
		&self,
		number: &<Block::Header as traits::Header>::Number,
		pool: &Arc<Pool<A>>,
		network_state: Arc<dyn NetworkStateInfo + Send + Sync>,
	) -> impl Future<Item = (), Error = ()> where
		A: ChainApi<Block=Block> + 'static,
	{
		let runtime = self.client.runtime_api();
		let at = BlockId::number(*number);
		let has_api = runtime.has_api::<dyn OffchainWorkerApi<Block>>(&at);
		debug!("Checking offchain workers at {:?}: {:?}", at, has_api);

		if has_api.unwrap_or(false) {
			let (api, runner) = api::AsyncApi::new(
				pool.clone(),
				self.db.clone(),
				self.keys_password.clone(),
				self.key_provider.clone(),
				at.clone(),
				network_state.clone(),
			);
			debug!("Spawning offchain workers at {:?}", at);
			let number = *number;
			let client = self.client.clone();
			spawn_worker(move || {
				let runtime = client.runtime_api();
				let api = Box::new(api);
				debug!("Running offchain workers at {:?}", at);
				let run = runtime.offchain_worker_with_context(
					&at,
					ExecutionContext::OffchainWorker(api),
					number
				);
				if let Err(e) =	run {
					log::error!("Error running offchain workers at {:?}: {:?}", at, e);
				}
			});
			futures::future::Either::A(runner.process())
		} else {
			futures::future::Either::B(futures::future::ok(()))
		}
	}
}

/// Spawns a new offchain worker.
///
/// We spawn offchain workers for each block in a separate thread,
/// since they can run for a significant amount of time
/// in a blocking fashion and we don't want to block the runtime.
///
/// Note that we should avoid that if we switch to future-based runtime in the future,
/// alternatively:
/// TODO [ToDr] (#1458) we can consider using a thread pool instead.
fn spawn_worker(f: impl FnOnce() -> () + Send + 'static) {
	std::thread::spawn(f);
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures::Future;
	use primitives::ed25519;
	use network::{Multiaddr, PeerId};

	struct MockNetworkStateInfo();

	impl NetworkStateInfo for MockNetworkStateInfo {
		fn external_addresses(&self) -> Vec<Multiaddr> {
			Vec::new()
		}

		fn peer_id(&self) -> PeerId {
			PeerId::random()
		}
	}

	#[derive(Clone)]
	pub(crate) struct TestProvider<Block> {
		_marker: PhantomData<Block>,
		key: ed25519::Pair,
	}

	impl<T> TestProvider<T> {
		pub fn new(key: ed25519::Pair) -> Self {
			Self {
				_marker: PhantomData,
				key,
			}
		}
	}

	impl<Block: traits::Block> AuthorityKeyProvider<Block> for TestProvider<Block> {
		fn authority_key(&self, _: &BlockId<Block>) -> Option<Box<dyn OffchainKey>> {
			Some(Box::new(self.key.clone()))
		}
	}

	#[test]
	fn should_call_into_runtime_and_produce_extrinsic() {
		// given
		let _ = env_logger::try_init();
		let runtime = tokio::runtime::Runtime::new().unwrap();
		let client = Arc::new(test_client::new());
		let pool = Arc::new(Pool::new(Default::default(), ::transaction_pool::ChainApi::new(client.clone())));
		let db = client_db::offchain::LocalStorage::new_test();
		let mock = Arc::new(MockNetworkStateInfo());

		// when
		let offchain = OffchainWorkers::new(
			client,
			db,
			Arc::new(AuthorityKeyProviders::new()),
			"".to_owned().into()
		);
		runtime.executor().spawn(offchain.on_block_imported(&0u64, &pool, mock.clone()));

		// then
		runtime.shutdown_on_idle().wait().unwrap();
		assert_eq!(pool.status().ready, 1);
		assert_eq!(pool.ready().next().unwrap().is_propagateable(), false);
	}
}
