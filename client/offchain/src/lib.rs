// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Substrate offchain workers.
//!
//! The offchain workers is a special function of the runtime that
//! gets executed after block is imported. During execution
//! it's able to asynchronously submit extrinsics that will either
//! be propagated to other nodes or added to the next block
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

use std::{fmt, sync::Arc};

use futures::{
	future::{ready, Future},
	prelude::*,
};
use parking_lot::Mutex;
use sc_client_api::BlockchainEvents;
use sc_network::{NetworkPeers, NetworkStateInfo};
use sc_transaction_pool_api::OffchainTransactionPoolFactory;
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_core::{offchain, traits::SpawnNamed};
use sp_externalities::Extension;
use sp_keystore::{KeystoreExt, KeystorePtr};
use sp_runtime::traits::{self, Header};
use threadpool::ThreadPool;

mod api;

pub use sp_core::offchain::storage::OffchainDb;
pub use sp_offchain::{OffchainWorkerApi, STORAGE_PREFIX};

const LOG_TARGET: &str = "offchain-worker";

/// NetworkProvider provides [`OffchainWorkers`] with all necessary hooks into the
/// underlying Substrate networking.
pub trait NetworkProvider: NetworkStateInfo + NetworkPeers {}

impl<T> NetworkProvider for T where T: NetworkStateInfo + NetworkPeers {}

/// Special type that implements [`OffchainStorage`](offchain::OffchainStorage).
///
/// This type can not be constructed and should only be used when passing `None` as `offchain_db` to
/// [`OffchainWorkerOptions`] to make the compiler happy.
#[derive(Clone)]
pub enum NoOffchainStorage {}

impl offchain::OffchainStorage for NoOffchainStorage {
	fn set(&mut self, _: &[u8], _: &[u8], _: &[u8]) {
		unimplemented!("`NoOffchainStorage` can not be constructed!")
	}

	fn remove(&mut self, _: &[u8], _: &[u8]) {
		unimplemented!("`NoOffchainStorage` can not be constructed!")
	}

	fn get(&self, _: &[u8], _: &[u8]) -> Option<Vec<u8>> {
		unimplemented!("`NoOffchainStorage` can not be constructed!")
	}

	fn compare_and_set(&mut self, _: &[u8], _: &[u8], _: Option<&[u8]>, _: &[u8]) -> bool {
		unimplemented!("`NoOffchainStorage` can not be constructed!")
	}
}

/// Options for [`OffchainWorkers`]
pub struct OffchainWorkerOptions<RA, Block: traits::Block, Storage, CE> {
	/// Provides access to the runtime api.
	pub runtime_api_provider: Arc<RA>,
	/// Provides access to the keystore.
	pub keystore: Option<KeystorePtr>,
	/// Provides access to the offchain database.
	///
	/// Use [`NoOffchainStorage`] as type when passing `None` to have some type that works.
	pub offchain_db: Option<Storage>,
	/// Provides access to the transaction pool.
	pub transaction_pool: Option<OffchainTransactionPoolFactory<Block>>,
	/// Provides access to network information.
	pub network_provider: Arc<dyn NetworkProvider + Send + Sync>,
	/// Is the node running as validator?
	pub is_validator: bool,
	/// Enable http requests from offchain workers?
	///
	/// If not enabled, any http request will panic.
	pub enable_http_requests: bool,
	/// Callback to create custom [`Extension`]s that should be registered for the
	/// `offchain_worker` runtime call.
	///
	/// These [`Extension`]s are registered along-side the default extensions and are accessible in
	/// the host functions.
	///
	/// # Example:
	///
	/// ```nocompile
	/// custom_extensions: |block_hash| {
	///     vec![MyCustomExtension::new()]
	/// }
	/// ```
	pub custom_extensions: CE,
}

/// An offchain workers manager.
pub struct OffchainWorkers<RA, Block: traits::Block, Storage> {
	runtime_api_provider: Arc<RA>,
	thread_pool: Mutex<ThreadPool>,
	shared_http_client: api::SharedClient,
	enable_http_requests: bool,
	keystore: Option<KeystorePtr>,
	offchain_db: Option<OffchainDb<Storage>>,
	transaction_pool: Option<OffchainTransactionPoolFactory<Block>>,
	network_provider: Arc<dyn NetworkProvider + Send + Sync>,
	is_validator: bool,
	custom_extensions: Box<dyn Fn(Block::Hash) -> Vec<Box<dyn Extension>> + Send>,
}

impl<RA, Block: traits::Block, Storage> OffchainWorkers<RA, Block, Storage> {
	/// Creates new [`OffchainWorkers`].
	pub fn new<CE: Fn(Block::Hash) -> Vec<Box<dyn Extension>> + Send + 'static>(
		OffchainWorkerOptions {
			runtime_api_provider,
			keystore,
			offchain_db,
			transaction_pool,
			network_provider,
			is_validator,
			enable_http_requests,
			custom_extensions,
		}: OffchainWorkerOptions<RA, Block, Storage, CE>,
	) -> Self {
		Self {
			runtime_api_provider,
			thread_pool: Mutex::new(ThreadPool::with_name(
				"offchain-worker".into(),
				num_cpus::get(),
			)),
			shared_http_client: api::SharedClient::new(),
			enable_http_requests,
			keystore,
			offchain_db: offchain_db.map(OffchainDb::new),
			transaction_pool,
			is_validator,
			network_provider,
			custom_extensions: Box::new(custom_extensions),
		}
	}
}

impl<RA, Block: traits::Block, Storage: offchain::OffchainStorage> fmt::Debug
	for OffchainWorkers<RA, Block, Storage>
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_tuple("OffchainWorkers").finish()
	}
}

impl<RA, Block, Storage> OffchainWorkers<RA, Block, Storage>
where
	Block: traits::Block,
	RA: ProvideRuntimeApi<Block> + Send + Sync + 'static,
	RA::Api: OffchainWorkerApi<Block>,
	Storage: offchain::OffchainStorage + 'static,
{
	/// Run the offchain workers on every block import.
	pub async fn run<BE: BlockchainEvents<Block>>(
		self,
		import_events: Arc<BE>,
		spawner: impl SpawnNamed,
	) {
		import_events
			.import_notification_stream()
			.for_each(move |n| {
				if n.is_new_best {
					spawner.spawn(
						"offchain-on-block",
						Some("offchain-worker"),
						self.on_block_imported(&n.header).boxed(),
					);
				} else {
					tracing::debug!(
						target: LOG_TARGET,
						"Skipping offchain workers for non-canon block: {:?}",
						n.header,
					)
				}

				ready(())
			})
			.await;
	}

	/// Start the offchain workers after given block.
	#[must_use]
	fn on_block_imported(&self, header: &Block::Header) -> impl Future<Output = ()> {
		let runtime = self.runtime_api_provider.runtime_api();
		let hash = header.hash();
		let has_api_v1 = runtime.has_api_with::<dyn OffchainWorkerApi<Block>, _>(hash, |v| v == 1);
		let has_api_v2 = runtime.has_api_with::<dyn OffchainWorkerApi<Block>, _>(hash, |v| v == 2);
		let version = match (has_api_v1, has_api_v2) {
			(_, Ok(true)) => 2,
			(Ok(true), _) => 1,
			err => {
				let help =
					"Consider turning off offchain workers if they are not part of your runtime.";
				tracing::error!(
					target: LOG_TARGET,
					"Unsupported Offchain Worker API version: {:?}. {}.",
					err,
					help
				);
				0
			},
		};
		tracing::debug!(
			target: LOG_TARGET,
			"Checking offchain workers at {hash:?}: version: {version}",
		);

		let process = (version > 0).then(|| {
			let (api, runner) = api::AsyncApi::new(
				self.network_provider.clone(),
				self.is_validator,
				self.shared_http_client.clone(),
			);
			tracing::debug!(target: LOG_TARGET, "Spawning offchain workers at {hash:?}");
			let header = header.clone();
			let client = self.runtime_api_provider.clone();

			let mut capabilities = offchain::Capabilities::all();
			capabilities.set(offchain::Capabilities::HTTP, self.enable_http_requests);

			let keystore = self.keystore.clone();
			let db = self.offchain_db.clone();
			let tx_pool = self.transaction_pool.clone();
			let custom_extensions = (*self.custom_extensions)(hash);

			self.spawn_worker(move || {
				let mut runtime = client.runtime_api();
				let api = Box::new(api);
				tracing::debug!(target: LOG_TARGET, "Running offchain workers at {hash:?}");

				if let Some(keystore) = keystore {
					runtime.register_extension(KeystoreExt(keystore.clone()));
				}

				if let Some(pool) = tx_pool {
					runtime.register_extension(pool.offchain_transaction_pool(hash));
				}

				if let Some(offchain_db) = db {
					runtime.register_extension(offchain::OffchainDbExt::new(
						offchain::LimitedExternalities::new(capabilities, offchain_db.clone()),
					));
				}

				runtime.register_extension(offchain::OffchainWorkerExt::new(
					offchain::LimitedExternalities::new(capabilities, api),
				));

				custom_extensions.into_iter().for_each(|ext| runtime.register_extension(ext));

				let run = if version == 2 {
					runtime.offchain_worker(hash, &header)
				} else {
					#[allow(deprecated)]
					runtime.offchain_worker_before_version_2(hash, *header.number())
				};

				if let Err(e) = run {
					tracing::error!(
						target: LOG_TARGET,
						"Error running offchain workers at {:?}: {}",
						hash,
						e
					);
				}
			});

			runner.process()
		});

		async move {
			futures::future::OptionFuture::from(process).await;
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
	fn spawn_worker(&self, f: impl FnOnce() -> () + Send + 'static) {
		self.thread_pool.lock().execute(f);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures::executor::block_on;
	use libp2p::{Multiaddr, PeerId};
	use sc_block_builder::BlockBuilderProvider as _;
	use sc_client_api::Backend as _;
	use sc_network::{config::MultiaddrWithPeerId, types::ProtocolName, ReputationChange};
	use sc_transaction_pool::BasicPool;
	use sc_transaction_pool_api::{InPoolTransaction, TransactionPool};
	use sp_consensus::BlockOrigin;
	use std::{collections::HashSet, sync::Arc};
	use substrate_test_runtime_client::{
		runtime::{
			substrate_test_pallet::pallet::Call as PalletCall, ExtrinsicBuilder, RuntimeCall,
		},
		ClientBlockImportExt, DefaultTestClientBuilderExt, TestClientBuilderExt,
	};

	struct TestNetwork();

	impl NetworkStateInfo for TestNetwork {
		fn external_addresses(&self) -> Vec<Multiaddr> {
			Vec::new()
		}

		fn local_peer_id(&self) -> PeerId {
			PeerId::random()
		}

		fn listen_addresses(&self) -> Vec<Multiaddr> {
			Vec::new()
		}
	}

	impl NetworkPeers for TestNetwork {
		fn set_authorized_peers(&self, _peers: HashSet<PeerId>) {
			unimplemented!();
		}

		fn set_authorized_only(&self, _reserved_only: bool) {
			unimplemented!();
		}

		fn add_known_address(&self, _peer_id: PeerId, _addr: Multiaddr) {
			unimplemented!();
		}

		fn report_peer(&self, _who: PeerId, _cost_benefit: ReputationChange) {
			unimplemented!();
		}

		fn disconnect_peer(&self, _who: PeerId, _protocol: ProtocolName) {
			unimplemented!();
		}

		fn accept_unreserved_peers(&self) {
			unimplemented!();
		}

		fn deny_unreserved_peers(&self) {
			unimplemented!();
		}

		fn add_reserved_peer(&self, _peer: MultiaddrWithPeerId) -> Result<(), String> {
			unimplemented!();
		}

		fn remove_reserved_peer(&self, _peer_id: PeerId) {
			unimplemented!();
		}

		fn set_reserved_peers(
			&self,
			_protocol: ProtocolName,
			_peers: HashSet<Multiaddr>,
		) -> Result<(), String> {
			unimplemented!();
		}

		fn add_peers_to_reserved_set(
			&self,
			_protocol: ProtocolName,
			_peers: HashSet<Multiaddr>,
		) -> Result<(), String> {
			unimplemented!();
		}

		fn remove_peers_from_reserved_set(&self, _protocol: ProtocolName, _peers: Vec<PeerId>) {
			unimplemented!();
		}

		fn sync_num_connected(&self) -> usize {
			unimplemented!();
		}
	}

	#[test]
	fn should_call_into_runtime_and_produce_extrinsic() {
		sp_tracing::try_init_simple();

		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let pool =
			BasicPool::new_full(Default::default(), true.into(), None, spawner, client.clone());
		let network = Arc::new(TestNetwork());
		let header = client.header(client.chain_info().genesis_hash).unwrap().unwrap();

		// when
		let offchain = OffchainWorkers::new(OffchainWorkerOptions {
			runtime_api_provider: client,
			keystore: None,
			offchain_db: None::<NoOffchainStorage>,
			transaction_pool: Some(OffchainTransactionPoolFactory::new(pool.clone())),
			network_provider: network,
			is_validator: false,
			enable_http_requests: false,
			custom_extensions: |_| Vec::new(),
		});
		futures::executor::block_on(offchain.on_block_imported(&header));

		// then
		assert_eq!(pool.status().ready, 1);
		assert!(matches!(
			pool.ready().next().unwrap().data().function,
			RuntimeCall::SubstrateTest(PalletCall::storage_change { .. })
		));
	}

	#[test]
	fn offchain_index_set_and_clear_works() {
		use sp_core::offchain::OffchainStorage;

		sp_tracing::try_init_simple();

		let (client, backend) = substrate_test_runtime_client::TestClientBuilder::new()
			.enable_offchain_indexing_api()
			.build_with_backend();
		let mut client = Arc::new(client);
		let offchain_db = backend.offchain_storage().unwrap();

		let key = &b"hello"[..];
		let value = &b"world"[..];
		let mut block_builder = client.new_block(Default::default()).unwrap();
		let ext = ExtrinsicBuilder::new_offchain_index_set(key.to_vec(), value.to_vec()).build();
		block_builder.push(ext).unwrap();

		let block = block_builder.build().unwrap().block;
		block_on(client.import(BlockOrigin::Own, block)).unwrap();

		assert_eq!(value, &offchain_db.get(sp_offchain::STORAGE_PREFIX, &key).unwrap());

		let mut block_builder = client.new_block(Default::default()).unwrap();
		let ext = ExtrinsicBuilder::new_offchain_index_clear(key.to_vec()).nonce(1).build();
		block_builder.push(ext).unwrap();

		let block = block_builder.build().unwrap().block;
		block_on(client.import(BlockOrigin::Own, block)).unwrap();

		assert!(offchain_db.get(sp_offchain::STORAGE_PREFIX, &key).is_none());
	}
}
