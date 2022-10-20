// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use crate::{config, ChainSyncInterface, NetworkService, NetworkWorker};

use futures::prelude::*;
use libp2p::Multiaddr;
use sc_client_api::{BlockBackend, HeaderBackend};
use sc_consensus::ImportQueue;
use sc_network_common::{
	config::{
		NonDefaultSetConfig, NonReservedPeerMode, NotificationHandshake, ProtocolId, SetConfig,
		TransportConfig,
	},
	protocol::{event::Event, role::Roles},
	service::NetworkEventStream,
	sync::{message::BlockAnnouncesHandshake, ChainSync as ChainSyncT},
};
use sc_network_light::light_client_requests::handler::LightClientRequestHandler;
use sc_network_sync::{
	block_request_handler::BlockRequestHandler,
	service::network::{NetworkServiceHandle, NetworkServiceProvider},
	state_request_handler::StateRequestHandler,
	ChainSync,
};
use sp_runtime::traits::{Block as BlockT, Header as _, Zero};
use std::sync::Arc;
use substrate_test_runtime_client::{
	runtime::{Block as TestBlock, Hash as TestHash},
	TestClient, TestClientBuilder, TestClientBuilderExt as _,
};

#[cfg(test)]
mod chain_sync;
#[cfg(test)]
mod service;

type TestNetworkWorker = NetworkWorker<TestBlock, TestHash, TestClient>;
type TestNetworkService = NetworkService<TestBlock, TestHash>;

const BLOCK_ANNOUNCE_PROTO_NAME: &str = "/block-announces";
const PROTOCOL_NAME: &str = "/foo";

struct TestNetwork {
	network: TestNetworkWorker,
}

impl TestNetwork {
	pub fn new(network: TestNetworkWorker) -> Self {
		Self { network }
	}

	pub fn service(&self) -> &Arc<TestNetworkService> {
		&self.network.service()
	}

	pub fn network(&mut self) -> &mut TestNetworkWorker {
		&mut self.network
	}

	pub fn start_network(
		self,
	) -> (Arc<TestNetworkService>, (impl Stream<Item = Event> + std::marker::Unpin)) {
		let worker = self.network;
		let service = worker.service().clone();
		let event_stream = service.event_stream("test");

		async_std::task::spawn(async move {
			futures::pin_mut!(worker);
			let _ = worker.await;
		});

		(service, event_stream)
	}
}

struct TestNetworkBuilder {
	import_queue: Option<Box<dyn ImportQueue<TestBlock>>>,
	client: Option<Arc<substrate_test_runtime_client::TestClient>>,
	listen_addresses: Vec<Multiaddr>,
	set_config: Option<SetConfig>,
	chain_sync: Option<(Box<dyn ChainSyncT<TestBlock>>, Box<dyn ChainSyncInterface<TestBlock>>)>,
	chain_sync_network: Option<(NetworkServiceProvider, NetworkServiceHandle)>,
	config: Option<config::NetworkConfiguration>,
}

impl TestNetworkBuilder {
	pub fn new() -> Self {
		Self {
			import_queue: None,
			client: None,
			listen_addresses: Vec::new(),
			set_config: None,
			chain_sync: None,
			chain_sync_network: None,
			config: None,
		}
	}

	pub fn with_client(mut self, client: Arc<substrate_test_runtime_client::TestClient>) -> Self {
		self.client = Some(client);
		self
	}

	pub fn with_config(mut self, config: config::NetworkConfiguration) -> Self {
		self.config = Some(config);
		self
	}

	pub fn with_listen_addresses(mut self, addresses: Vec<Multiaddr>) -> Self {
		self.listen_addresses = addresses;
		self
	}

	pub fn with_set_config(mut self, set_config: SetConfig) -> Self {
		self.set_config = Some(set_config);
		self
	}

	pub fn with_chain_sync(
		mut self,
		chain_sync: (Box<dyn ChainSyncT<TestBlock>>, Box<dyn ChainSyncInterface<TestBlock>>),
	) -> Self {
		self.chain_sync = Some(chain_sync);
		self
	}

	pub fn with_chain_sync_network(
		mut self,
		chain_sync_network: (NetworkServiceProvider, NetworkServiceHandle),
	) -> Self {
		self.chain_sync_network = Some(chain_sync_network);
		self
	}

	pub fn with_import_queue(mut self, import_queue: Box<dyn ImportQueue<TestBlock>>) -> Self {
		self.import_queue = Some(import_queue);
		self
	}

	pub fn build(mut self) -> TestNetwork {
		let client = self.client.as_mut().map_or(
			Arc::new(TestClientBuilder::with_default_backend().build_with_longest_chain().0),
			|v| v.clone(),
		);

		let network_config = self.config.unwrap_or(config::NetworkConfiguration {
			extra_sets: vec![NonDefaultSetConfig {
				notifications_protocol: PROTOCOL_NAME.into(),
				fallback_names: Vec::new(),
				max_notification_size: 1024 * 1024,
				handshake: None,
				set_config: self.set_config.unwrap_or_default(),
			}],
			listen_addresses: self.listen_addresses,
			transport: TransportConfig::MemoryOnly,
			..config::NetworkConfiguration::new_local()
		});

		#[derive(Clone)]
		struct PassThroughVerifier(bool);

		#[async_trait::async_trait]
		impl<B: BlockT> sc_consensus::Verifier<B> for PassThroughVerifier {
			async fn verify(
				&mut self,
				mut block: sc_consensus::BlockImportParams<B, ()>,
			) -> Result<
				(
					sc_consensus::BlockImportParams<B, ()>,
					Option<Vec<(sp_blockchain::well_known_cache_keys::Id, Vec<u8>)>>,
				),
				String,
			> {
				let maybe_keys = block
					.header
					.digest()
					.log(|l| {
						l.try_as_raw(sp_runtime::generic::OpaqueDigestItemId::Consensus(b"aura"))
							.or_else(|| {
								l.try_as_raw(sp_runtime::generic::OpaqueDigestItemId::Consensus(
									b"babe",
								))
							})
					})
					.map(|blob| {
						vec![(sp_blockchain::well_known_cache_keys::AUTHORITIES, blob.to_vec())]
					});

				block.finalized = self.0;
				block.fork_choice = Some(sc_consensus::ForkChoiceStrategy::LongestChain);
				Ok((block, maybe_keys))
			}
		}

		let import_queue = self.import_queue.unwrap_or(Box::new(sc_consensus::BasicQueue::new(
			PassThroughVerifier(false),
			Box::new(client.clone()),
			None,
			&sp_core::testing::TaskExecutor::new(),
			None,
		)));

		let (chain_sync_network_provider, chain_sync_network_handle) =
			self.chain_sync_network.unwrap_or(NetworkServiceProvider::new());

		let (chain_sync, chain_sync_service) = self.chain_sync.unwrap_or({
			let (chain_sync, chain_sync_service) = ChainSync::new(
				match network_config.sync_mode {
					config::SyncMode::Full => sc_network_common::sync::SyncMode::Full,
					config::SyncMode::Fast { skip_proofs, storage_chain_mode } =>
						sc_network_common::sync::SyncMode::LightState {
							skip_proofs,
							storage_chain_mode,
						},
					config::SyncMode::Warp => sc_network_common::sync::SyncMode::Warp,
				},
				client.clone(),
				Box::new(sp_consensus::block_validation::DefaultBlockAnnounceValidator),
				network_config.max_parallel_downloads,
				None,
				chain_sync_network_handle,
			)
			.unwrap();

			(Box::new(chain_sync), chain_sync_service)
		});

		let protocol_id = ProtocolId::from("test-protocol-name");
		let fork_id = Some(String::from("test-fork-id"));

		let block_request_protocol_config = {
			let (handler, protocol_config) =
				BlockRequestHandler::new(&protocol_id, None, client.clone(), 50);
			async_std::task::spawn(handler.run().boxed());
			protocol_config
		};

		let state_request_protocol_config = {
			let (handler, protocol_config) =
				StateRequestHandler::new(&protocol_id, None, client.clone(), 50);
			async_std::task::spawn(handler.run().boxed());
			protocol_config
		};

		let light_client_request_protocol_config = {
			let (handler, protocol_config) =
				LightClientRequestHandler::new(&protocol_id, None, client.clone());
			async_std::task::spawn(handler.run().boxed());
			protocol_config
		};

		let block_announce_config = NonDefaultSetConfig {
			notifications_protocol: BLOCK_ANNOUNCE_PROTO_NAME.into(),
			fallback_names: vec![],
			max_notification_size: 1024 * 1024,
			handshake: Some(NotificationHandshake::new(BlockAnnouncesHandshake::<
				substrate_test_runtime_client::runtime::Block,
			>::build(
				Roles::from(&config::Role::Full),
				client.info().best_number,
				client.info().best_hash,
				client
					.block_hash(Zero::zero())
					.ok()
					.flatten()
					.expect("Genesis block exists; qed"),
			))),
			set_config: SetConfig {
				in_peers: 0,
				out_peers: 0,
				reserved_nodes: Vec::new(),
				non_reserved_mode: NonReservedPeerMode::Deny,
			},
		};

		let worker = NetworkWorker::<
			substrate_test_runtime_client::runtime::Block,
			substrate_test_runtime_client::runtime::Hash,
			substrate_test_runtime_client::TestClient,
		>::new(config::Params {
			block_announce_config,
			role: config::Role::Full,
			executor: None,
			network_config,
			chain: client.clone(),
			protocol_id,
			fork_id,
			import_queue,
			chain_sync,
			chain_sync_service,
			metrics_registry: None,
			block_request_protocol_config,
			state_request_protocol_config,
			light_client_request_protocol_config,
			warp_sync_protocol_config: None,
			request_response_protocol_configs: Vec::new(),
		})
		.unwrap();

		let service = worker.service().clone();
		async_std::task::spawn(async move {
			let _ = chain_sync_network_provider.run(service).await;
		});

		TestNetwork::new(worker)
	}
}
