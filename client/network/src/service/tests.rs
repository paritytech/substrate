// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use crate::{config, Event, NetworkService, NetworkWorker};

use futures::prelude::*;
use sp_runtime::traits::{Block as BlockT, Header as _};
use std::sync::Arc;
use substrate_test_runtime_client::{TestClientBuilder, TestClientBuilderExt as _};

/// Builds a full node to be used for testing.
fn build_test_full_node(config: config::NetworkConfiguration) -> (Arc<NetworkService<
	substrate_test_runtime_client::runtime::Block,
	substrate_test_runtime_client::runtime::Hash,
>>, impl Stream<Item = Event>) {
	let client = Arc::new(
		TestClientBuilder::with_default_backend()
			.build_with_longest_chain()
			.0,
	);

	#[derive(Clone)]
	struct PassThroughVerifier(bool);
	impl<B: BlockT> sp_consensus::import_queue::Verifier<B> for PassThroughVerifier {
		fn verify(
			&mut self,
			origin: sp_consensus::BlockOrigin,
			header: B::Header,
			justification: Option<sp_runtime::Justification>,
			body: Option<Vec<B::Extrinsic>>,
		) -> Result<
			(
				sp_consensus::BlockImportParams<B, ()>,
				Option<Vec<(sp_blockchain::well_known_cache_keys::Id, Vec<u8>)>>,
			),
			String,
		> {
			let maybe_keys = header
				.digest()
				.log(|l| {
					l.try_as_raw(sp_runtime::generic::OpaqueDigestItemId::Consensus(b"aura"))
						.or_else(|| {
							l.try_as_raw(sp_runtime::generic::OpaqueDigestItemId::Consensus(b"babe"))
						})
				})
				.map(|blob| {
					vec![(
						sp_blockchain::well_known_cache_keys::AUTHORITIES,
						blob.to_vec(),
					)]
				});

			let mut import = sp_consensus::BlockImportParams::new(origin, header);
			import.body = body;
			import.finalized = self.0;
			import.justification = justification;
			import.fork_choice = Some(sp_consensus::ForkChoiceStrategy::LongestChain);
			Ok((import, maybe_keys))
		}
	}

	let import_queue = Box::new(sp_consensus::import_queue::BasicQueue::new(
		PassThroughVerifier(false),
		Box::new(client.clone()),
		None,
		None,
	));

	let worker = NetworkWorker::new(config::Params {
		role: config::Role::Full,
		executor: None,
		network_config: config,
		chain: client.clone(),
		finality_proof_provider: None,
		finality_proof_request_builder: None,
		on_demand: None,
		transaction_pool: Arc::new(crate::service::EmptyTransactionPool),
		protocol_id: config::ProtocolId::from(&b"/test-protocol-name"[..]),
		import_queue,
		block_announce_validator: Box::new(
			sp_consensus::block_validation::DefaultBlockAnnounceValidator::new(client.clone()),
		),
		metrics_registry: None,
	})
	.unwrap();

	let service = worker.service().clone();
	let event_stream = service.event_stream();

	async_std::task::spawn(async move {
		futures::pin_mut!(worker);
		let _ = worker.await;
	});

	(service, event_stream)
}

const ENGINE_ID: sp_runtime::ConsensusEngineId = *b"foo\0";

/// Builds a full node to be used for testing.
fn build_nodes_one_proto() -> (Arc<NetworkService<
	substrate_test_runtime_client::runtime::Block,
	substrate_test_runtime_client::runtime::Hash,
>>, impl Stream<Item = Event>, Arc<NetworkService<
substrate_test_runtime_client::runtime::Block,
substrate_test_runtime_client::runtime::Hash,
>>, impl Stream<Item = Event>) {
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];

	let (node1, events_stream1) = build_test_full_node(config::NetworkConfiguration {
		notifications_protocols: vec![(ENGINE_ID, From::from(&b"/foo"[..]))],
		listen_addresses: vec![listen_addr.clone()],
		transport: config::TransportConfig::MemoryOnly,
		.. config::NetworkConfiguration::default()
	});

	let (node2, events_stream2) = build_test_full_node(config::NetworkConfiguration {
		notifications_protocols: vec![(ENGINE_ID, From::from(&b"/foo"[..]))],
		reserved_nodes: vec![config::MultiaddrWithPeerId {
			multiaddr: listen_addr,
			peer_id: node1.local_peer_id().clone(),
		}],
		transport: config::TransportConfig::MemoryOnly,
		.. config::NetworkConfiguration::default()
	});

	(node1, events_stream1, node2, events_stream2)
}

#[test]
fn notifications_state_consistent() {
	let (node1, mut events_stream1, node2, mut events_stream2) = build_nodes_one_proto();

	async_std::task::block_on(async move {
		// True if we have an active substream from node1 to node2.
		let mut node1_to_node2_open = false;
		// True if we have an active substream from node2 to node1.
		let mut node2_to_node1_open = false;
		// We stop the test after a certain number of iterations.
		let mut iterations = 0;

		loop {
			iterations += 1;
			if iterations >= 1_000 {
				break;
			}

			// Start by sending a notification from node1 to node2 and vice-versa. Part of the
			// test consists in ensuring that notifications get ignored if the stream isn't open.
			if rand::random::<u8>() % 5 >= 3 {
				node1.write_notification(node2.local_peer_id().clone(), ENGINE_ID, b"hello world".to_vec());
			}
			if rand::random::<u8>() % 5 >= 3 {
				node2.write_notification(node1.local_peer_id().clone(), ENGINE_ID, b"hello world".to_vec());
			}

			// Also randomly disconnect the two nodes.
			if rand::random::<u8>() % 20 == 0 {
				node1.disconnect_peer(node2.local_peer_id().clone());
			}
			if rand::random::<u8>() % 20 == 0 {
				node2.disconnect_peer(node1.local_peer_id().clone());
			}

			// Grab next event from either `events_stream1` or `events_stream2`.
			let next_event = {
				let next1 = events_stream1.next();
				let next2 = events_stream2.next();
				match future::select(next1, next2).await {
					future::Either::Left((Some(ev), _)) => future::Either::Left(ev),
					future::Either::Right((Some(ev), _)) => future::Either::Right(ev),
					_ => break,
				}
			};

			match next_event {
				future::Either::Left(Event::NotificationStreamOpened { remote, engine_id, .. }) => {
					assert!(!node1_to_node2_open);
					node1_to_node2_open = true;
					assert_eq!(remote, *node2.local_peer_id());
					assert_eq!(engine_id, ENGINE_ID);
				}
				future::Either::Left(Event::NotificationStreamClosed { remote, engine_id, .. }) => {
					assert!(node1_to_node2_open);
					node1_to_node2_open = false;
					assert_eq!(remote, *node2.local_peer_id());
					assert_eq!(engine_id, ENGINE_ID);
				}
				future::Either::Left(Event::NotificationsReceived { remote, .. }) => {
					assert!(node1_to_node2_open);
					assert_eq!(remote, *node2.local_peer_id());
					node1.write_notification(node2.local_peer_id().clone(), ENGINE_ID, b"hello world".to_vec());
				}
				future::Either::Right(Event::NotificationStreamOpened { remote, engine_id, .. }) => {
					assert!(!node2_to_node1_open);
					node2_to_node1_open = true;
					assert_eq!(remote, *node1.local_peer_id());
					assert_eq!(engine_id, ENGINE_ID);
				}
				future::Either::Right(Event::NotificationStreamClosed { remote, engine_id, .. }) => {
					assert!(node2_to_node1_open);
					node2_to_node1_open = false;
					assert_eq!(remote, *node1.local_peer_id());
					assert_eq!(engine_id, ENGINE_ID);
				}
				future::Either::Right(Event::NotificationsReceived { remote, .. }) => {
					assert!(node2_to_node1_open);
					assert_eq!(remote, *node1.local_peer_id());
					node2.write_notification(node1.local_peer_id().clone(), ENGINE_ID, b"hello world".to_vec());
				}
				_ => {}
			};
		}
	});
}
