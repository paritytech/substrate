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
	fmt,
	marker::PhantomData,
	sync::Arc,
};

use client::runtime_api::ApiExt;
use log::{debug, warn};
use primitives::{
	ExecutionContext,
	crypto,
};
use sr_primitives::{
	generic::BlockId,
	traits::{self, ProvideRuntimeApi},
};
use futures::future::Future;
use transaction_pool::txpool::{Pool, ChainApi};
use network::NetworkStateInfo;

mod api;

pub mod testing;

pub use offchain_primitives::OffchainWorkerApi;

/// Provides currently configured authority key.
pub trait AuthorityKeyProvider<Block: traits::Block>: Clone + 'static {
	/// The crypto used by the block authoring algorithm.
	type ConsensusPair: crypto::Pair;
	/// The crypto used by the finality gadget.
	type FinalityPair: crypto::Pair;

	/// Returns currently configured authority key.
	fn authority_key(&self, block_id: &BlockId<Block>) -> Option<Self::ConsensusPair>;

	/// Returns currently configured finality gadget authority key.
	fn fg_authority_key(&self, block_id: &BlockId<Block>) -> Option<Self::FinalityPair>;
}

/// An offchain workers manager.
pub struct OffchainWorkers<
	Client,
	Storage,
	KeyProvider,
	Block: traits::Block,
> {
	client: Arc<Client>,
	db: Storage,
	authority_key: KeyProvider,
	keys_password: crypto::Protected<String>,
	_block: PhantomData<Block>,
}

impl<Client, Storage, KeyProvider, Block: traits::Block> OffchainWorkers<
	Client,
	Storage,
	KeyProvider,
	Block,
> {
	/// Creates new `OffchainWorkers`.
	pub fn new(
		client: Arc<Client>,
		db: Storage,
		authority_key: KeyProvider,
		keys_password: crypto::Protected<String>,
	) -> Self {
		Self {
			client,
			db,
			authority_key,
			keys_password,
			_block: PhantomData,
		}
	}
}

impl<Client, Storage, KeyProvider, Block: traits::Block> fmt::Debug for OffchainWorkers<
	Client,
	Storage,
	KeyProvider,
	Block,
> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_tuple("OffchainWorkers").finish()
	}
}

impl<Client, Storage, KeyProvider, Block> OffchainWorkers<
	Client,
	Storage,
	KeyProvider,
	Block,
> where
	Block: traits::Block,
	Client: ProvideRuntimeApi + Send + Sync + 'static,
	Client::Api: OffchainWorkerApi<Block>,
	KeyProvider: AuthorityKeyProvider<Block> + Send,
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
				self.authority_key.clone(),
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
	use primitives::{ed25519, sr25519};
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
		pub(crate) sr_key: Option<sr25519::Pair>,
		pub(crate) ed_key: Option<ed25519::Pair>,
	}

	impl<Block: traits::Block> Default for TestProvider<Block> {
		fn default() -> Self {
			Self {
				_marker: PhantomData,
				sr_key: None,
				ed_key: None,
			}
		}
	}

	impl<Block: traits::Block> AuthorityKeyProvider<Block> for TestProvider<Block> {
		type ConsensusPair = ed25519::Pair;
		type FinalityPair = sr25519::Pair;

		fn authority_key(&self, _: &BlockId<Block>) -> Option<Self::ConsensusPair> {
			self.ed_key.clone()
		}

		fn fg_authority_key(&self, _: &BlockId<Block>) -> Option<Self::FinalityPair> {
			self.sr_key.clone()
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
		let offchain = OffchainWorkers::new(client, db, TestProvider::default(), "".to_owned().into());
		runtime.executor().spawn(offchain.on_block_imported(&0u64, &pool, mock.clone()));

		// then
		runtime.shutdown_on_idle().wait().unwrap();
		assert_eq!(pool.status().ready, 1);
		assert_eq!(pool.ready().next().unwrap().is_propagateable(), false);
	}
}
