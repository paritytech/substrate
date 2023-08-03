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

use futures::prelude::*;
use libp2p::{Multiaddr, PeerId};

use sc_consensus::{ImportQueue, Link};
use sc_network::{
	config::{self, FullNetworkConfiguration, MultiaddrWithPeerId, ProtocolId, TransportConfig},
	event::Event,
	peer_store::PeerStore,
	service::traits::{NotificationEvent, ValidationResult},
	NetworkEventStream, NetworkPeers, NetworkService, NetworkStateInfo, NetworkWorker,
	NotificationService,
};
use sc_network_common::role::Roles;
use sc_network_light::light_client_requests::handler::LightClientRequestHandler;
use sc_network_sync::{
	block_request_handler::BlockRequestHandler,
	engine::SyncingEngine,
	service::network::{NetworkServiceHandle, NetworkServiceProvider},
	state_request_handler::StateRequestHandler,
};
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::{Block as BlockT, Zero};
use substrate_test_runtime_client::{
	runtime::{Block as TestBlock, Hash as TestHash},
	TestClientBuilder, TestClientBuilderExt as _,
};

use std::{sync::Arc, time::Duration};

type TestNetworkWorker = NetworkWorker<TestBlock, TestHash>;
type TestNetworkService = NetworkService<TestBlock, TestHash>;

const PROTOCOL_NAME: &str = "/foo";

struct TestNetwork {
	network: TestNetworkWorker,
}

impl TestNetwork {
	pub fn new(network: TestNetworkWorker) -> Self {
		Self { network }
	}

	pub fn start_network(
		self,
	) -> (Arc<TestNetworkService>, (impl Stream<Item = Event> + std::marker::Unpin)) {
		let worker = self.network;
		let service = worker.service().clone();
		let event_stream = service.event_stream("test");

		tokio::spawn(worker.run());

		(service, event_stream)
	}
}

struct TestNetworkBuilder {
	import_queue: Option<Box<dyn ImportQueue<TestBlock>>>,
	link: Option<Box<dyn Link<TestBlock>>>,
	client: Option<Arc<substrate_test_runtime_client::TestClient>>,
	listen_addresses: Vec<Multiaddr>,
	set_config: Option<config::SetConfig>,
	chain_sync_network: Option<(NetworkServiceProvider, NetworkServiceHandle)>,
	notification_protocols: Vec<config::NonDefaultSetConfig>,
	config: Option<config::NetworkConfiguration>,
}

impl TestNetworkBuilder {
	pub fn new() -> Self {
		Self {
			import_queue: None,
			link: None,
			client: None,
			listen_addresses: Vec::new(),
			set_config: None,
			chain_sync_network: None,
			notification_protocols: Vec::new(),
			config: None,
		}
	}

	pub fn with_config(mut self, config: config::NetworkConfiguration) -> Self {
		self.config = Some(config);
		self
	}

	pub fn with_notification_protocol(mut self, config: config::NonDefaultSetConfig) -> Self {
		self.notification_protocols.push(config);
		self
	}

	pub fn with_listen_addresses(mut self, addresses: Vec<Multiaddr>) -> Self {
		self.listen_addresses = addresses;
		self
	}

	pub fn with_set_config(mut self, set_config: config::SetConfig) -> Self {
		self.set_config = Some(set_config);
		self
	}

	pub fn build(mut self) -> (TestNetwork, Option<Box<dyn NotificationService>>) {
		let client = self.client.as_mut().map_or(
			Arc::new(TestClientBuilder::with_default_backend().build_with_longest_chain().0),
			|v| v.clone(),
		);

		let network_config = self.config.unwrap_or(config::NetworkConfiguration {
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
			) -> Result<sc_consensus::BlockImportParams<B, ()>, String> {
				block.finalized = self.0;
				block.fork_choice = Some(sc_consensus::ForkChoiceStrategy::LongestChain);
				Ok(block)
			}
		}

		let mut import_queue =
			self.import_queue.unwrap_or(Box::new(sc_consensus::BasicQueue::new(
				PassThroughVerifier(false),
				Box::new(client.clone()),
				None,
				&sp_core::testing::TaskExecutor::new(),
				None,
			)));

		let protocol_id = ProtocolId::from("test-protocol-name");
		let fork_id = Some(String::from("test-fork-id"));
		let mut full_net_config = FullNetworkConfiguration::new(&network_config);

		let block_request_protocol_config = {
			let (handler, protocol_config) =
				BlockRequestHandler::new(&protocol_id, None, client.clone(), 50);
			tokio::spawn(handler.run().boxed());
			protocol_config
		};

		let state_request_protocol_config = {
			let (handler, protocol_config) =
				StateRequestHandler::new(&protocol_id, None, client.clone(), 50);
			tokio::spawn(handler.run().boxed());
			protocol_config
		};

		let light_client_request_protocol_config = {
			let (handler, protocol_config) =
				LightClientRequestHandler::new(&protocol_id, None, client.clone());
			tokio::spawn(handler.run().boxed());
			protocol_config
		};

		let (chain_sync_network_provider, chain_sync_network_handle) =
			self.chain_sync_network.unwrap_or(NetworkServiceProvider::new());
		let (tx, rx) = sc_utils::mpsc::tracing_unbounded("mpsc_syncing_engine_protocol", 100_000);
		let (engine, chain_sync_service, block_announce_config) = SyncingEngine::new(
			Roles::from(&config::Role::Full),
			client.clone(),
			None,
			&full_net_config,
			protocol_id.clone(),
			&None,
			Box::new(sp_consensus::block_validation::DefaultBlockAnnounceValidator),
			None,
			chain_sync_network_handle,
			import_queue.service(),
			block_request_protocol_config.name.clone(),
			state_request_protocol_config.name.clone(),
			None,
			rx,
		)
		.unwrap();
		let mut link = self.link.unwrap_or(Box::new(chain_sync_service.clone()));

		let handle = if !self.notification_protocols.is_empty() {
			for config in self.notification_protocols {
				full_net_config.add_notification_protocol(config);
			}
			None
		} else {
			let (config, handle) = config::NonDefaultSetConfig::new(
				PROTOCOL_NAME.into(),
				Vec::new(),
				1024 * 1024,
				None,
				self.set_config.unwrap_or_default(),
			);
			full_net_config.add_notification_protocol(config);
			Some(handle)
		};

		for config in [
			block_request_protocol_config,
			state_request_protocol_config,
			light_client_request_protocol_config,
		] {
			full_net_config.add_request_response_protocol(config);
		}

		let peer_store = PeerStore::new(
			network_config.boot_nodes.iter().map(|bootnode| bootnode.peer_id).collect(),
		);
		let peer_store_handle = peer_store.handle();
		tokio::spawn(peer_store.run().boxed());

		let genesis_hash =
			client.hash(Zero::zero()).ok().flatten().expect("Genesis block exists; qed");
		let worker = NetworkWorker::<
			substrate_test_runtime_client::runtime::Block,
			substrate_test_runtime_client::runtime::Hash,
		>::new(config::Params::<substrate_test_runtime_client::runtime::Block> {
			block_announce_config,
			role: config::Role::Full,
			executor: Box::new(|f| {
				tokio::spawn(f);
			}),
			genesis_hash,
			network_config: full_net_config,
			peer_store: peer_store_handle,
			protocol_id,
			fork_id,
			metrics_registry: None,
			tx,
		})
		.unwrap();

		let service = worker.service().clone();
		tokio::spawn(async move {
			let _ = chain_sync_network_provider.run(service).await;
		});
		tokio::spawn(async move {
			loop {
				futures::future::poll_fn(|cx| {
					import_queue.poll_actions(cx, &mut *link);
					std::task::Poll::Ready(())
				})
				.await;
				tokio::time::sleep(std::time::Duration::from_millis(250)).await;
			}
		});
		tokio::spawn(engine.run());

		(TestNetwork::new(worker), handle)
	}
}

/// Builds two nodes and their associated events stream.
/// The nodes are connected together and have the `PROTOCOL_NAME` protocol registered.
fn build_nodes_one_proto() -> (
	Arc<TestNetworkService>,
	Option<Box<dyn NotificationService>>,
	Arc<TestNetworkService>,
	Option<Box<dyn NotificationService>>,
) {
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];

	let (network1, handle1) = TestNetworkBuilder::new()
		.with_listen_addresses(vec![listen_addr.clone()])
		.build();
	let (node1, _) = network1.start_network();

	let (network2, handle2) = TestNetworkBuilder::new()
		.with_set_config(config::SetConfig {
			reserved_nodes: vec![MultiaddrWithPeerId {
				multiaddr: listen_addr,
				peer_id: node1.local_peer_id(),
			}],
			..Default::default()
		})
		.build();

	let (node2, _) = network2.start_network();

	(node1, handle1, node2, handle2)
}

#[tokio::test]
async fn notifications_state_consistent() {
	// Runs two nodes and ensures that events are propagated out of the API in a consistent
	// correct order, which means no notification received on a closed substream.

	let (node1, handle1, node2, handle2) = build_nodes_one_proto();
	let (mut handle1, mut handle2) = (handle1.unwrap(), handle2.unwrap());

	// Write some initial notifications that shouldn't get through.
	for _ in 0..(rand::random::<u8>() % 5) {
		let _ = handle1.send_sync_notification(&node2.local_peer_id(), b"hello world".to_vec());
	}
	for _ in 0..(rand::random::<u8>() % 5) {
		let _ = handle2.send_sync_notification(&node1.local_peer_id(), b"hello world".to_vec());
	}

	// True if we have an active substream from node1 to node2.
	let mut node1_to_node2_open = false;
	// True if we have an active substream from node2 to node1.
	let mut node2_to_node1_open = false;
	// We stop the test after a certain number of iterations.
	let mut iterations = 0;
	// Safe guard because we don't want the test to pass if no substream has been open.
	let mut something_happened = false;

	loop {
		iterations += 1;
		if iterations >= 1_000 {
			assert!(something_happened);
			break
		}

		// Start by sending a notification from node1 to node2 and vice-versa. Part of the
		// test consists in ensuring that notifications get ignored if the stream isn't open.
		if rand::random::<u8>() % 5 >= 3 {
			let _ = handle1.send_sync_notification(&node2.local_peer_id(), b"hello world".to_vec());
		}
		if rand::random::<u8>() % 5 >= 3 {
			let _ = handle2.send_sync_notification(&node1.local_peer_id(), b"hello world".to_vec());
		}

		// Also randomly disconnect the two nodes from time to time.
		if rand::random::<u8>() % 20 == 0 {
			node1.disconnect_peer(node2.local_peer_id(), PROTOCOL_NAME.into());
		}
		if rand::random::<u8>() % 20 == 0 {
			node2.disconnect_peer(node1.local_peer_id(), PROTOCOL_NAME.into());
		}

		// Grab next event from either `events_stream1` or `events_stream2`.
		let next_event = {
			let next1 = handle1.next_event();
			let next2 = handle2.next_event();
			// We also await on a small timer, otherwise it is possible for the test to wait
			// forever while nothing at all happens on the network.
			let continue_test = futures_timer::Delay::new(Duration::from_millis(20));
			match future::select(future::select(next1, next2), continue_test).await {
				future::Either::Left((future::Either::Left((Some(ev), _)), _)) =>
					future::Either::Left(ev),
				future::Either::Left((future::Either::Right((Some(ev), _)), _)) =>
					future::Either::Right(ev),
				future::Either::Right(_) => continue,
				_ => break,
			}
		};

		match next_event {
			future::Either::Left(NotificationEvent::ValidateInboundSubstream {
				result_tx, ..
			}) => {
				result_tx.send(ValidationResult::Accept).unwrap();
			},
			future::Either::Right(NotificationEvent::ValidateInboundSubstream {
				result_tx,
				..
			}) => {
				result_tx.send(ValidationResult::Accept).unwrap();
			},
			future::Either::Left(NotificationEvent::NotificationStreamOpened { peer, .. }) => {
				something_happened = true;
				assert!(!node1_to_node2_open);
				node1_to_node2_open = true;
				assert_eq!(peer, node2.local_peer_id());
			},
			future::Either::Right(NotificationEvent::NotificationStreamOpened { peer, .. }) => {
				something_happened = true;
				assert!(!node2_to_node1_open);
				node2_to_node1_open = true;
				assert_eq!(peer, node1.local_peer_id());
			},
			future::Either::Left(NotificationEvent::NotificationStreamClosed { peer, .. }) => {
				assert!(node1_to_node2_open);
				node1_to_node2_open = false;
				assert_eq!(peer, node2.local_peer_id());
			},
			future::Either::Right(NotificationEvent::NotificationStreamClosed { peer, .. }) => {
				assert!(node2_to_node1_open);
				node2_to_node1_open = false;
				assert_eq!(peer, node1.local_peer_id());
			},
			future::Either::Left(NotificationEvent::NotificationReceived { peer, .. }) => {
				assert!(node1_to_node2_open);
				assert_eq!(peer, node2.local_peer_id());
				if rand::random::<u8>() % 5 >= 4 {
					let _ = handle1
						.send_sync_notification(&node2.local_peer_id(), b"hello world".to_vec());
				}
			},
			future::Either::Right(NotificationEvent::NotificationReceived { peer, .. }) => {
				assert!(node2_to_node1_open);
				assert_eq!(peer, node1.local_peer_id());
				if rand::random::<u8>() % 5 >= 4 {
					let _ = handle2
						.send_sync_notification(&node1.local_peer_id(), b"hello world".to_vec());
				}
			},
		};
	}
}

#[tokio::test]
async fn lots_of_incoming_peers_works() {
	sp_tracing::try_init_simple();
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];

	let (main_node, handle1) = TestNetworkBuilder::new()
		.with_listen_addresses(vec![listen_addr.clone()])
		.with_set_config(config::SetConfig { in_peers: u32::MAX, ..Default::default() })
		.build();
	let mut handle1 = handle1.unwrap();
	let (main_node, _) = main_node.start_network();

	let main_node_peer_id = main_node.local_peer_id();

	tokio::spawn(async move {
		while let Some(event) = handle1.next_event().await {
			if let NotificationEvent::ValidateInboundSubstream { result_tx, .. } = event {
				result_tx.send(ValidationResult::Accept).unwrap();
			}
		}
	});

	// We spawn background tasks and push them in this `Vec`. They will all be waited upon before
	// this test ends.
	let mut background_tasks_to_wait = Vec::new();

	for _ in 0..32 {
		let (dialing_node, handle) = TestNetworkBuilder::new()
			.with_set_config(config::SetConfig {
				reserved_nodes: vec![MultiaddrWithPeerId {
					multiaddr: listen_addr.clone(),
					peer_id: main_node_peer_id,
				}],
				..Default::default()
			})
			.build();
		let mut handle = handle.unwrap();
		let (_, _) = dialing_node.start_network();

		background_tasks_to_wait.push(tokio::spawn(async move {
			// Create a dummy timer that will "never" fire, and that will be overwritten when we
			// actually need the timer. Using an Option would be technically cleaner, but it would
			// make the code below way more complicated.
			let mut timer = futures_timer::Delay::new(Duration::from_secs(3600 * 24 * 7)).fuse();

			loop {
				futures::select! {
					_ = timer => {
						// Test succeeds when timer fires.
						return;
					}
					ev = handle.next_event().fuse() => match ev.unwrap() {
						NotificationEvent::ValidateInboundSubstream { result_tx, .. } => {
							result_tx.send(ValidationResult::Accept).unwrap();
						}
						NotificationEvent::NotificationStreamOpened { peer, .. } => {
							assert_eq!(peer, main_node_peer_id);
							// Test succeeds after 5 seconds. This timer is here in order to
							// detect a potential problem after opening.
							timer = futures_timer::Delay::new(Duration::from_secs(5)).fuse();
						}
						_ => {}
					}
				}
			}
		}));
	}

	future::join_all(background_tasks_to_wait).await;
}

#[tokio::test]
async fn notifications_back_pressure() {
	// Node 1 floods node 2 with notifications. Random sleeps are done on node 2 to simulate the
	// node being busy. We make sure that all notifications are received.

	const TOTAL_NOTIFS: usize = 10_000;

	let (_node1, handle1, node2, handle2) = build_nodes_one_proto();
	let (mut handle1, mut handle2) = (handle1.unwrap(), handle2.unwrap());
	let node2_id = node2.local_peer_id();

	let receiver = tokio::spawn(async move {
		let mut received_notifications = 0;
		// let mut sync_protocol_name = None;

		while received_notifications < TOTAL_NOTIFS {
			match handle2.next_event().await.unwrap() {
				NotificationEvent::ValidateInboundSubstream { result_tx, .. } => {
					result_tx.send(ValidationResult::Accept).unwrap();
				},
				NotificationEvent::NotificationReceived { notification, .. } => {
					assert_eq!(
						notification,
						format!("hello #{}", received_notifications).into_bytes()
					);
					received_notifications += 1;
				},
				_ => {},
			}

			if rand::random::<u8>() < 2 {
				tokio::time::sleep(Duration::from_millis(rand::random::<u64>() % 750)).await;
			}
		}
	});

	// Wait for the `NotificationStreamOpened`.
	loop {
		match handle1.next_event().await.unwrap() {
			NotificationEvent::ValidateInboundSubstream { result_tx, .. } => {
				result_tx.send(ValidationResult::Accept).unwrap();
			},
			NotificationEvent::NotificationStreamOpened { .. } => break,
			_ => {},
		};
	}

	// Sending!
	for num in 0..TOTAL_NOTIFS {
		handle1
			.send_async_notification(&node2_id, format!("hello #{}", num).into_bytes())
			.await
			.unwrap();
	}

	receiver.await.unwrap();
}

#[tokio::test]
async fn fallback_name_working() {
	sp_tracing::try_init_simple();
	// Node 1 supports the protocols "new" and "old". Node 2 only supports "old". Checks whether
	// they can connect.
	const NEW_PROTOCOL_NAME: &str = "/new-shiny-protocol-that-isnt-PROTOCOL_NAME";

	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];
	let (config, mut handle1) = config::NonDefaultSetConfig::new(
		NEW_PROTOCOL_NAME.into(),
		vec![PROTOCOL_NAME.into()],
		1024 * 1024,
		None,
		Default::default(),
	);
	let (network1, _) = TestNetworkBuilder::new()
		.with_notification_protocol(config)
		.with_config(config::NetworkConfiguration {
			listen_addresses: vec![listen_addr.clone()],
			transport: TransportConfig::MemoryOnly,
			..config::NetworkConfiguration::new_local()
		})
		.build();

	let (node1, _) = network1.start_network();

	let (network2, handle2) = TestNetworkBuilder::new()
		.with_set_config(config::SetConfig {
			reserved_nodes: vec![MultiaddrWithPeerId {
				multiaddr: listen_addr,
				peer_id: node1.local_peer_id(),
			}],
			..Default::default()
		})
		.build();
	let mut handle2 = handle2.unwrap();
	let _ = network2.start_network();

	let receiver = tokio::spawn(async move {
		// Wait for the `NotificationStreamOpened`.
		loop {
			match handle2.next_event().await.unwrap() {
				NotificationEvent::ValidateInboundSubstream { result_tx, .. } => {
					result_tx.send(ValidationResult::Accept).unwrap();
				},
				NotificationEvent::NotificationStreamOpened { negotiated_fallback, .. } => {
					assert_eq!(negotiated_fallback, None);
					break
				},
				_ => {},
			}
		}
	});

	// Wait for the `NotificationStreamOpened`.
	loop {
		match handle1.next_event().await.unwrap() {
			NotificationEvent::ValidateInboundSubstream { result_tx, .. } => {
				result_tx.send(ValidationResult::Accept).unwrap();
			},
			NotificationEvent::NotificationStreamOpened { negotiated_fallback, .. } => {
				assert_eq!(negotiated_fallback, Some(PROTOCOL_NAME.into()));
				break
			},
			_ => {},
		}
	}

	receiver.await.unwrap();
}

#[tokio::test]
#[should_panic(expected = "don't match the transport")]
async fn ensure_listen_addresses_consistent_with_transport_memory() {
	let listen_addr = config::build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(0_u16)];

	let _ = TestNetworkBuilder::new()
		.with_config(config::NetworkConfiguration {
			listen_addresses: vec![listen_addr.clone()],
			transport: TransportConfig::MemoryOnly,
			..config::NetworkConfiguration::new(
				"test-node",
				"test-client",
				Default::default(),
				None,
			)
		})
		.build()
		.0
		.start_network();
}

#[tokio::test]
#[should_panic(expected = "don't match the transport")]
async fn ensure_listen_addresses_consistent_with_transport_not_memory() {
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];

	let _ = TestNetworkBuilder::new()
		.with_config(config::NetworkConfiguration {
			listen_addresses: vec![listen_addr.clone()],
			..config::NetworkConfiguration::new(
				"test-node",
				"test-client",
				Default::default(),
				None,
			)
		})
		.build()
		.0
		.start_network();
}

#[tokio::test]
#[should_panic(expected = "don't match the transport")]
async fn ensure_boot_node_addresses_consistent_with_transport_memory() {
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];
	let boot_node = MultiaddrWithPeerId {
		multiaddr: config::build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(0_u16)],
		peer_id: PeerId::random(),
	};

	let _ = TestNetworkBuilder::new()
		.with_config(config::NetworkConfiguration {
			listen_addresses: vec![listen_addr.clone()],
			transport: TransportConfig::MemoryOnly,
			boot_nodes: vec![boot_node],
			..config::NetworkConfiguration::new(
				"test-node",
				"test-client",
				Default::default(),
				None,
			)
		})
		.build()
		.0
		.start_network();
}

#[tokio::test]
#[should_panic(expected = "don't match the transport")]
async fn ensure_boot_node_addresses_consistent_with_transport_not_memory() {
	let listen_addr = config::build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(0_u16)];
	let boot_node = MultiaddrWithPeerId {
		multiaddr: config::build_multiaddr![Memory(rand::random::<u64>())],
		peer_id: PeerId::random(),
	};

	let _ = TestNetworkBuilder::new()
		.with_config(config::NetworkConfiguration {
			listen_addresses: vec![listen_addr.clone()],
			boot_nodes: vec![boot_node],
			..config::NetworkConfiguration::new(
				"test-node",
				"test-client",
				Default::default(),
				None,
			)
		})
		.build()
		.0
		.start_network();
}

#[tokio::test]
#[should_panic(expected = "don't match the transport")]
async fn ensure_reserved_node_addresses_consistent_with_transport_memory() {
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];
	let reserved_node = MultiaddrWithPeerId {
		multiaddr: config::build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(0_u16)],
		peer_id: PeerId::random(),
	};

	let _ = TestNetworkBuilder::new()
		.with_config(config::NetworkConfiguration {
			listen_addresses: vec![listen_addr.clone()],
			transport: TransportConfig::MemoryOnly,
			default_peers_set: config::SetConfig {
				reserved_nodes: vec![reserved_node],
				..Default::default()
			},
			..config::NetworkConfiguration::new(
				"test-node",
				"test-client",
				Default::default(),
				None,
			)
		})
		.build()
		.0
		.start_network();
}

#[tokio::test]
#[should_panic(expected = "don't match the transport")]
async fn ensure_reserved_node_addresses_consistent_with_transport_not_memory() {
	let listen_addr = config::build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(0_u16)];
	let reserved_node = MultiaddrWithPeerId {
		multiaddr: config::build_multiaddr![Memory(rand::random::<u64>())],
		peer_id: PeerId::random(),
	};

	let _ = TestNetworkBuilder::new()
		.with_config(config::NetworkConfiguration {
			listen_addresses: vec![listen_addr.clone()],
			default_peers_set: config::SetConfig {
				reserved_nodes: vec![reserved_node],
				..Default::default()
			},
			..config::NetworkConfiguration::new(
				"test-node",
				"test-client",
				Default::default(),
				None,
			)
		})
		.build()
		.0
		.start_network();
}

#[tokio::test]
#[should_panic(expected = "don't match the transport")]
async fn ensure_public_addresses_consistent_with_transport_memory() {
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];
	let public_address = config::build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(0_u16)];

	let _ = TestNetworkBuilder::new()
		.with_config(config::NetworkConfiguration {
			listen_addresses: vec![listen_addr.clone()],
			transport: TransportConfig::MemoryOnly,
			public_addresses: vec![public_address],
			..config::NetworkConfiguration::new(
				"test-node",
				"test-client",
				Default::default(),
				None,
			)
		})
		.build()
		.0
		.start_network();
}

#[tokio::test]
#[should_panic(expected = "don't match the transport")]
async fn ensure_public_addresses_consistent_with_transport_not_memory() {
	let listen_addr = config::build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(0_u16)];
	let public_address = config::build_multiaddr![Memory(rand::random::<u64>())];

	let _ = TestNetworkBuilder::new()
		.with_config(config::NetworkConfiguration {
			listen_addresses: vec![listen_addr.clone()],
			public_addresses: vec![public_address],
			..config::NetworkConfiguration::new(
				"test-node",
				"test-client",
				Default::default(),
				None,
			)
		})
		.build()
		.0
		.start_network();
}
