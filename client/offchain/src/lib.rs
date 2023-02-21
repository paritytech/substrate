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

use std::{fmt, marker::PhantomData, sync::Arc};

use futures::{
	future::{ready, Future},
	prelude::*,
};
use parking_lot::Mutex;
use sc_network_common::service::{NetworkPeers, NetworkStateInfo};
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_core::{offchain, traits::SpawnNamed, ExecutionContext};
use sp_runtime::traits::{self, Header};
use threadpool::ThreadPool;

mod api;

pub use api::Db as OffchainDb;
pub use sp_offchain::{OffchainWorkerApi, STORAGE_PREFIX};

const LOG_TARGET: &str = "offchain-worker";

/// NetworkProvider provides [`OffchainWorkers`] with all necessary hooks into the
/// underlying Substrate networking.
pub trait NetworkProvider: NetworkStateInfo + NetworkPeers {}

impl<T> NetworkProvider for T where T: NetworkStateInfo + NetworkPeers {}

/// Options for [`OffchainWorkers`]
pub struct OffchainWorkerOptions {
	/// Enable http requests from offchain workers?
	///
	/// If not enabled, any http request will panic.
	pub enable_http_requests: bool,
}

/// An offchain workers manager.
pub struct OffchainWorkers<Client, Block: traits::Block> {
	client: Arc<Client>,
	_block: PhantomData<Block>,
	thread_pool: Mutex<ThreadPool>,
	shared_http_client: api::SharedClient,
	enable_http: bool,
}

impl<Client, Block: traits::Block> OffchainWorkers<Client, Block> {
	/// Creates new [`OffchainWorkers`].
	pub fn new(client: Arc<Client>) -> Self {
		Self::new_with_options(client, OffchainWorkerOptions { enable_http_requests: true })
	}

	/// Creates new [`OffchainWorkers`] using the given `options`.
	pub fn new_with_options(client: Arc<Client>, options: OffchainWorkerOptions) -> Self {
		Self {
			client,
			_block: PhantomData,
			thread_pool: Mutex::new(ThreadPool::with_name(
				"offchain-worker".into(),
				num_cpus::get(),
			)),
			shared_http_client: api::SharedClient::new(),
			enable_http: options.enable_http_requests,
		}
	}
}

impl<Client, Block: traits::Block> fmt::Debug for OffchainWorkers<Client, Block> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_tuple("OffchainWorkers").finish()
	}
}

impl<Client, Block> OffchainWorkers<Client, Block>
where
	Block: traits::Block,
	Client: ProvideRuntimeApi<Block> + Send + Sync + 'static,
	Client::Api: OffchainWorkerApi<Block>,
{
	/// Start the offchain workers after given block.
	#[must_use]
	pub fn on_block_imported(
		&self,
		header: &Block::Header,
		network_provider: Arc<dyn NetworkProvider + Send + Sync>,
		is_validator: bool,
	) -> impl Future<Output = ()> {
		let runtime = self.client.runtime_api();
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
			"Checking offchain workers at {:?}: version:{}",
			hash,
			version
		);
		let process = (version > 0).then(|| {
			let (api, runner) =
				api::AsyncApi::new(network_provider, is_validator, self.shared_http_client.clone());
			tracing::debug!(target: LOG_TARGET, "Spawning offchain workers at {:?}", hash);
			let header = header.clone();
			let client = self.client.clone();

			let mut capabilities = offchain::Capabilities::all();

			capabilities.set(offchain::Capabilities::HTTP, self.enable_http);
			self.spawn_worker(move || {
				let runtime = client.runtime_api();
				let api = Box::new(api);
				tracing::debug!(target: LOG_TARGET, "Running offchain workers at {:?}", hash);

				let context = ExecutionContext::OffchainCall(Some((api, capabilities)));
				let run = if version == 2 {
					runtime.offchain_worker_with_context(hash, context, &header)
				} else {
					#[allow(deprecated)]
					runtime.offchain_worker_before_version_2_with_context(
						hash,
						context,
						*header.number(),
					)
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

/// Inform the offchain worker about new imported blocks
pub async fn notification_future<Client, Block, Spawner>(
	is_validator: bool,
	client: Arc<Client>,
	offchain: Arc<OffchainWorkers<Client, Block>>,
	spawner: Spawner,
	network_provider: Arc<dyn NetworkProvider + Send + Sync>,
) where
	Block: traits::Block,
	Client:
		ProvideRuntimeApi<Block> + sc_client_api::BlockchainEvents<Block> + Send + Sync + 'static,
	Client::Api: OffchainWorkerApi<Block>,
	Spawner: SpawnNamed,
{
	client
		.import_notification_stream()
		.for_each(move |n| {
			if n.is_new_best {
				spawner.spawn(
					"offchain-on-block",
					Some("offchain-worker"),
					offchain
						.on_block_imported(&n.header, network_provider.clone(), is_validator)
						.boxed(),
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

#[cfg(test)]
mod tests {
	use super::*;
	use futures::executor::block_on;
	use libp2p::{Multiaddr, PeerId};
	use sc_block_builder::BlockBuilderProvider as _;
	use sc_client_api::Backend as _;
	use sc_network_common::{config::MultiaddrWithPeerId, protocol::ProtocolName};
	use sc_peerset::ReputationChange;
	use sc_transaction_pool::{BasicPool, FullChainApi};
	use sc_transaction_pool_api::{InPoolTransaction, TransactionPool};
	use sp_consensus::BlockOrigin;
	use sp_runtime::generic::BlockId;
	use std::{collections::HashSet, sync::Arc};
	use substrate_test_runtime_client::{
		runtime::Block, ClientBlockImportExt, DefaultTestClientBuilderExt, TestClient,
		TestClientBuilderExt,
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

		fn add_to_peers_set(
			&self,
			_protocol: ProtocolName,
			_peers: HashSet<Multiaddr>,
		) -> Result<(), String> {
			unimplemented!();
		}

		fn remove_from_peers_set(&self, _protocol: ProtocolName, _peers: Vec<PeerId>) {
			unimplemented!();
		}

		fn sync_num_connected(&self) -> usize {
			unimplemented!();
		}
	}

	struct TestPool(Arc<BasicPool<FullChainApi<TestClient, Block>, Block>>);

	impl sc_transaction_pool_api::OffchainSubmitTransaction<Block> for TestPool {
		fn submit_at(
			&self,
			at: &BlockId<Block>,
			extrinsic: <Block as traits::Block>::Extrinsic,
		) -> Result<(), ()> {
			let source = sc_transaction_pool_api::TransactionSource::Local;
			futures::executor::block_on(self.0.submit_one(&at, source, extrinsic))
				.map(|_| ())
				.map_err(|_| ())
		}
	}

	#[test]
	fn should_call_into_runtime_and_produce_extrinsic() {
		sp_tracing::try_init_simple();

		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let pool = TestPool(BasicPool::new_full(
			Default::default(),
			true.into(),
			None,
			spawner,
			client.clone(),
		));
		let network = Arc::new(TestNetwork());
		let header = client.header(client.chain_info().genesis_hash).unwrap().unwrap();

		// when
		let offchain = OffchainWorkers::new(client);
		futures::executor::block_on(offchain.on_block_imported(&header, network, false));

		// then
		assert_eq!(pool.0.status().ready, 1);
		assert_eq!(pool.0.ready().next().unwrap().is_propagable(), false);
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
		block_builder
			.push(substrate_test_runtime_client::runtime::Extrinsic::OffchainIndexSet(
				key.to_vec(),
				value.to_vec(),
			))
			.unwrap();

		let block = block_builder.build().unwrap().block;
		block_on(client.import(BlockOrigin::Own, block)).unwrap();

		assert_eq!(value, &offchain_db.get(sp_offchain::STORAGE_PREFIX, &key).unwrap());

		let mut block_builder = client.new_block(Default::default()).unwrap();
		block_builder
			.push(substrate_test_runtime_client::runtime::Extrinsic::OffchainIndexClear(
				key.to_vec(),
			))
			.unwrap();

		let block = block_builder.build().unwrap().block;
		block_on(client.import(BlockOrigin::Own, block)).unwrap();

		assert!(offchain_db.get(sp_offchain::STORAGE_PREFIX, &key).is_none());
	}
}
