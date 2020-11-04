// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

use crate::{config, gossip::QueuedSender, Event, NetworkService, NetworkWorker};

use futures::prelude::*;
use sp_runtime::traits::{Block as BlockT, Header as _};
use std::{sync::Arc, time::Duration};
use substrate_test_runtime_client::{TestClientBuilder, TestClientBuilderExt as _};

type TestNetworkService = NetworkService<
	substrate_test_runtime_client::runtime::Block,
	substrate_test_runtime_client::runtime::Hash,
>;

/// Builds a full node to be used for testing. Returns the node service and its associated events
/// stream.
///
/// > **Note**: We return the events stream in order to not possibly lose events between the
/// >			construction of the service and the moment the events stream is grabbed.
fn build_test_full_node(network_config: config::NetworkConfiguration)
	-> (Arc<TestNetworkService>, impl Stream<Item = Event>)
{
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
		&sp_core::testing::TaskExecutor::new(),
		None,
	));

	let protocol_id = config::ProtocolId::from("/test-protocol-name");

	// Add block request handler.
	let block_request_protocol_config = {
		let (handler, protocol_config) = crate::block_request_handler::BlockRequestHandler::new(protocol_id.clone(), client.clone());
		async_std::task::spawn(handler.run().boxed());
		protocol_config
	};

	// Add finality protocol.
	let finality_request_protocol_config = crate::finality_request_handler::generate_protocol_config(protocol_id.clone());

	let worker = NetworkWorker::new(config::Params {
		role: config::Role::Full,
		executor: None,
		network_config,
		chain: client.clone(),
		finality_proof_request_builder: None,
		on_demand: None,
		transaction_pool: Arc::new(crate::config::EmptyTransactionPool),
		protocol_id: config::ProtocolId::from("/test-protocol-name"),
		import_queue,
		block_announce_validator: Box::new(
			sp_consensus::block_validation::DefaultBlockAnnounceValidator,
		),
		metrics_registry: None,
		block_request_protocol_config,
		finality_request_protocol_config,
	})
	.unwrap();

	let service = worker.service().clone();
	let event_stream = service.event_stream("test");

	async_std::task::spawn(async move {
		futures::pin_mut!(worker);
		let _ = worker.await;
	});

	(service, event_stream)
}

const ENGINE_ID: sp_runtime::ConsensusEngineId = *b"foo\0";

/// Builds two nodes and their associated events stream.
/// The nodes are connected together and have the `ENGINE_ID` protocol registered.
fn build_nodes_one_proto()
	-> (Arc<TestNetworkService>, impl Stream<Item = Event>, Arc<TestNetworkService>, impl Stream<Item = Event>)
{
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];

	let (node1, events_stream1) = build_test_full_node(config::NetworkConfiguration {
		notifications_protocols: vec![(ENGINE_ID, From::from("/foo"))],
		listen_addresses: vec![listen_addr.clone()],
		transport: config::TransportConfig::MemoryOnly,
		.. config::NetworkConfiguration::new_local()
	});

	let (node2, events_stream2) = build_test_full_node(config::NetworkConfiguration {
		notifications_protocols: vec![(ENGINE_ID, From::from("/foo"))],
		listen_addresses: vec![],
		reserved_nodes: vec![config::MultiaddrWithPeerId {
			multiaddr: listen_addr,
			peer_id: node1.local_peer_id().clone(),
		}],
		transport: config::TransportConfig::MemoryOnly,
		.. config::NetworkConfiguration::new_local()
	});

	(node1, events_stream1, node2, events_stream2)
}

#[test]
fn basic_works() {
	const NUM_NOTIFS: usize = 256;

	let (node1, mut events_stream1, node2, mut events_stream2) = build_nodes_one_proto();
	let node2_id = node2.local_peer_id().clone();

	let receiver = async_std::task::spawn(async move {
		let mut received_notifications = 0;

		while received_notifications < NUM_NOTIFS {
			match events_stream2.next().await.unwrap() {
				Event::NotificationStreamClosed { .. } => panic!(),
				Event::NotificationsReceived { messages, .. } => {
					for message in messages {
						assert_eq!(message.0, ENGINE_ID);
						assert_eq!(message.1, &b"message"[..]);
						received_notifications += 1;
					}
				}
				_ => {}
			};

			if rand::random::<u8>() < 2 {
				async_std::task::sleep(Duration::from_millis(rand::random::<u64>() % 750)).await;
			}
		}
	});

	async_std::task::block_on(async move {
		let (mut sender, bg_future) =
			QueuedSender::new(node1, node2_id, ENGINE_ID, NUM_NOTIFS, |msg| msg);
		async_std::task::spawn(bg_future);

		// Wait for the `NotificationStreamOpened`.
		loop {
			match events_stream1.next().await.unwrap() {
				Event::NotificationStreamOpened { .. } => break,
				_ => {}
			};
		}

		for _ in 0..NUM_NOTIFS {
			sender.queue_or_discard(b"message".to_vec()).await;
		}

		receiver.await;
	});
}
