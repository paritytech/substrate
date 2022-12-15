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

use crate::{config, service::tests::TestNetworkBuilder, NetworkService};

use futures::prelude::*;
use libp2p::PeerId;
use sc_network_common::{
	config::{MultiaddrWithPeerId, NonDefaultSetConfig, SetConfig, TransportConfig},
	protocol::event::Event,
	service::{NetworkNotification, NetworkPeers, NetworkStateInfo},
};
use std::{sync::Arc, time::Duration};
use tokio::runtime::Handle;

type TestNetworkService = NetworkService<
	substrate_test_runtime_client::runtime::Block,
	substrate_test_runtime_client::runtime::Hash,
>;

const BLOCK_ANNOUNCE_PROTO_NAME: &str = "/block-announces";
const PROTOCOL_NAME: &str = "/foo";

/// Builds two nodes and their associated events stream.
/// The nodes are connected together and have the `PROTOCOL_NAME` protocol registered.
fn build_nodes_one_proto(
	rt_handle: &Handle,
) -> (
	Arc<TestNetworkService>,
	impl Stream<Item = Event>,
	Arc<TestNetworkService>,
	impl Stream<Item = Event>,
) {
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];

	let (node1, events_stream1) = TestNetworkBuilder::new(rt_handle.clone())
		.with_listen_addresses(vec![listen_addr.clone()])
		.build()
		.start_network();

	let (node2, events_stream2) = TestNetworkBuilder::new(rt_handle.clone())
		.with_set_config(SetConfig {
			reserved_nodes: vec![MultiaddrWithPeerId {
				multiaddr: listen_addr,
				peer_id: node1.local_peer_id(),
			}],
			..Default::default()
		})
		.build()
		.start_network();

	(node1, events_stream1, node2, events_stream2)
}

#[test]
fn notifications_state_consistent() {
	// Runs two nodes and ensures that events are propagated out of the API in a consistent
	// correct order, which means no notification received on a closed substream.

	let runtime = tokio::runtime::Runtime::new().unwrap();

	let (node1, mut events_stream1, node2, mut events_stream2) =
		build_nodes_one_proto(runtime.handle());

	// Write some initial notifications that shouldn't get through.
	for _ in 0..(rand::random::<u8>() % 5) {
		node1.write_notification(
			node2.local_peer_id(),
			PROTOCOL_NAME.into(),
			b"hello world".to_vec(),
		);
	}
	for _ in 0..(rand::random::<u8>() % 5) {
		node2.write_notification(
			node1.local_peer_id(),
			PROTOCOL_NAME.into(),
			b"hello world".to_vec(),
		);
	}

	runtime.block_on(async move {
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
				node1.write_notification(
					node2.local_peer_id(),
					PROTOCOL_NAME.into(),
					b"hello world".to_vec(),
				);
			}
			if rand::random::<u8>() % 5 >= 3 {
				node2.write_notification(
					node1.local_peer_id(),
					PROTOCOL_NAME.into(),
					b"hello world".to_vec(),
				);
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
				let next1 = events_stream1.next();
				let next2 = events_stream2.next();
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
				future::Either::Left(Event::NotificationStreamOpened {
					remote, protocol, ..
				}) =>
					if protocol == PROTOCOL_NAME.into() {
						something_happened = true;
						assert!(!node1_to_node2_open);
						node1_to_node2_open = true;
						assert_eq!(remote, node2.local_peer_id());
					},
				future::Either::Right(Event::NotificationStreamOpened {
					remote, protocol, ..
				}) =>
					if protocol == PROTOCOL_NAME.into() {
						something_happened = true;
						assert!(!node2_to_node1_open);
						node2_to_node1_open = true;
						assert_eq!(remote, node1.local_peer_id());
					},
				future::Either::Left(Event::NotificationStreamClosed {
					remote, protocol, ..
				}) =>
					if protocol == PROTOCOL_NAME.into() {
						assert!(node1_to_node2_open);
						node1_to_node2_open = false;
						assert_eq!(remote, node2.local_peer_id());
					},
				future::Either::Right(Event::NotificationStreamClosed {
					remote, protocol, ..
				}) =>
					if protocol == PROTOCOL_NAME.into() {
						assert!(node2_to_node1_open);
						node2_to_node1_open = false;
						assert_eq!(remote, node1.local_peer_id());
					},
				future::Either::Left(Event::NotificationsReceived { remote, .. }) => {
					assert!(node1_to_node2_open);
					assert_eq!(remote, node2.local_peer_id());
					if rand::random::<u8>() % 5 >= 4 {
						node1.write_notification(
							node2.local_peer_id(),
							PROTOCOL_NAME.into(),
							b"hello world".to_vec(),
						);
					}
				},
				future::Either::Right(Event::NotificationsReceived { remote, .. }) => {
					assert!(node2_to_node1_open);
					assert_eq!(remote, node1.local_peer_id());
					if rand::random::<u8>() % 5 >= 4 {
						node2.write_notification(
							node1.local_peer_id(),
							PROTOCOL_NAME.into(),
							b"hello world".to_vec(),
						);
					}
				},

				// Add new events here.
				future::Either::Left(Event::SyncConnected { .. }) => {},
				future::Either::Right(Event::SyncConnected { .. }) => {},
				future::Either::Left(Event::SyncDisconnected { .. }) => {},
				future::Either::Right(Event::SyncDisconnected { .. }) => {},
				future::Either::Left(Event::Dht(_)) => {},
				future::Either::Right(Event::Dht(_)) => {},
			};
		}
	});
}

#[tokio::test]
async fn lots_of_incoming_peers_works() {
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];

	let (main_node, _) = TestNetworkBuilder::new(Handle::current())
		.with_listen_addresses(vec![listen_addr.clone()])
		.with_set_config(SetConfig { in_peers: u32::MAX, ..Default::default() })
		.build()
		.start_network();

	let main_node_peer_id = main_node.local_peer_id();

	// We spawn background tasks and push them in this `Vec`. They will all be waited upon before
	// this test ends.
	let mut background_tasks_to_wait = Vec::new();

	for _ in 0..32 {
		let (_dialing_node, event_stream) = TestNetworkBuilder::new(Handle::current())
			.with_set_config(SetConfig {
				reserved_nodes: vec![MultiaddrWithPeerId {
					multiaddr: listen_addr.clone(),
					peer_id: main_node_peer_id,
				}],
				..Default::default()
			})
			.build()
			.start_network();

		background_tasks_to_wait.push(tokio::spawn(async move {
			// Create a dummy timer that will "never" fire, and that will be overwritten when we
			// actually need the timer. Using an Option would be technically cleaner, but it would
			// make the code below way more complicated.
			let mut timer = futures_timer::Delay::new(Duration::from_secs(3600 * 24 * 7)).fuse();

			let mut event_stream = event_stream.fuse();
			loop {
				futures::select! {
					_ = timer => {
						// Test succeeds when timer fires.
						return;
					}
					ev = event_stream.next() => {
						match ev.unwrap() {
							Event::NotificationStreamOpened { remote, .. } => {
								assert_eq!(remote, main_node_peer_id);
								// Test succeeds after 5 seconds. This timer is here in order to
								// detect a potential problem after opening.
								timer = futures_timer::Delay::new(Duration::from_secs(5)).fuse();
							}
							Event::NotificationStreamClosed { .. } => {
								// Test failed.
								panic!();
							}
							_ => {}
						}
					}
				}
			}
		}));
	}

	future::join_all(background_tasks_to_wait).await;
}

#[test]
fn notifications_back_pressure() {
	// Node 1 floods node 2 with notifications. Random sleeps are done on node 2 to simulate the
	// node being busy. We make sure that all notifications are received.

	const TOTAL_NOTIFS: usize = 10_000;

	let runtime = tokio::runtime::Runtime::new().unwrap();

	let (node1, mut events_stream1, node2, mut events_stream2) =
		build_nodes_one_proto(runtime.handle());
	let node2_id = node2.local_peer_id();

	let receiver = runtime.spawn(async move {
		let mut received_notifications = 0;

		while received_notifications < TOTAL_NOTIFS {
			match events_stream2.next().await.unwrap() {
				Event::NotificationStreamClosed { .. } => panic!(),
				Event::NotificationsReceived { messages, .. } =>
					for message in messages {
						assert_eq!(message.0, PROTOCOL_NAME.into());
						assert_eq!(message.1, format!("hello #{}", received_notifications));
						received_notifications += 1;
					},
				_ => {},
			};

			if rand::random::<u8>() < 2 {
				tokio::time::sleep(Duration::from_millis(rand::random::<u64>() % 750)).await;
			}
		}
	});

	runtime.block_on(async move {
		// Wait for the `NotificationStreamOpened`.
		loop {
			match events_stream1.next().await.unwrap() {
				Event::NotificationStreamOpened { .. } => break,
				_ => {},
			};
		}

		// Sending!
		for num in 0..TOTAL_NOTIFS {
			let notif = node1.notification_sender(node2_id, PROTOCOL_NAME.into()).unwrap();
			notif
				.ready()
				.await
				.unwrap()
				.send(format!("hello #{}", num).into_bytes())
				.unwrap();
		}

		receiver.await.unwrap();
	});
}

#[test]
fn fallback_name_working() {
	// Node 1 supports the protocols "new" and "old". Node 2 only supports "old". Checks whether
	// they can connect.
	const NEW_PROTOCOL_NAME: &str = "/new-shiny-protocol-that-isnt-PROTOCOL_NAME";

	let runtime = tokio::runtime::Runtime::new().unwrap();

	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];
	let (node1, mut events_stream1) = TestNetworkBuilder::new(runtime.handle().clone())
		.with_config(config::NetworkConfiguration {
			extra_sets: vec![NonDefaultSetConfig {
				notifications_protocol: NEW_PROTOCOL_NAME.into(),
				fallback_names: vec![PROTOCOL_NAME.into()],
				max_notification_size: 1024 * 1024,
				handshake: None,
				set_config: Default::default(),
			}],
			listen_addresses: vec![listen_addr.clone()],
			transport: TransportConfig::MemoryOnly,
			..config::NetworkConfiguration::new_local()
		})
		.build()
		.start_network();

	let (_, mut events_stream2) = TestNetworkBuilder::new(runtime.handle().clone())
		.with_set_config(SetConfig {
			reserved_nodes: vec![MultiaddrWithPeerId {
				multiaddr: listen_addr,
				peer_id: node1.local_peer_id(),
			}],
			..Default::default()
		})
		.build()
		.start_network();

	let receiver = runtime.spawn(async move {
		// Wait for the `NotificationStreamOpened`.
		loop {
			match events_stream2.next().await.unwrap() {
				Event::NotificationStreamOpened { protocol, negotiated_fallback, .. } => {
					assert_eq!(protocol, PROTOCOL_NAME.into());
					assert_eq!(negotiated_fallback, None);
					break
				},
				_ => {},
			};
		}
	});

	runtime.block_on(async move {
		// Wait for the `NotificationStreamOpened`.
		loop {
			match events_stream1.next().await.unwrap() {
				Event::NotificationStreamOpened { protocol, negotiated_fallback, .. }
					if protocol == NEW_PROTOCOL_NAME.into() =>
				{
					assert_eq!(negotiated_fallback, Some(PROTOCOL_NAME.into()));
					break
				},
				_ => {},
			};
		}

		receiver.await.unwrap();
	});
}

// Disconnect peer by calling `Protocol::disconnect_peer()` with the supplied block announcement
// protocol name and verify that `SyncDisconnected` event is emitted
#[tokio::test]
async fn disconnect_sync_peer_using_block_announcement_protocol_name() {
	let (node1, mut events_stream1, node2, mut events_stream2) =
		build_nodes_one_proto(&Handle::current());

	async fn wait_for_events(stream: &mut (impl Stream<Item = Event> + std::marker::Unpin)) {
		let mut notif_received = false;
		let mut sync_received = false;

		while !notif_received || !sync_received {
			match stream.next().await.unwrap() {
				Event::NotificationStreamOpened { .. } => notif_received = true,
				Event::SyncConnected { .. } => sync_received = true,
				_ => {},
			};
		}
	}

	wait_for_events(&mut events_stream1).await;
	wait_for_events(&mut events_stream2).await;

	// disconnect peer using `PROTOCOL_NAME`, verify `NotificationStreamClosed` event is emitted
	node2.disconnect_peer(node1.local_peer_id(), PROTOCOL_NAME.into());
	assert!(std::matches!(
		events_stream2.next().await,
		Some(Event::NotificationStreamClosed { .. })
	));
	let _ = events_stream2.next().await; // ignore the reopen event

	// now disconnect using `BLOCK_ANNOUNCE_PROTO_NAME`, verify that `SyncDisconnected` is
	// emitted
	node2.disconnect_peer(node1.local_peer_id(), BLOCK_ANNOUNCE_PROTO_NAME.into());
	assert!(std::matches!(events_stream2.next().await, Some(Event::SyncDisconnected { .. })));
}

#[tokio::test]
#[should_panic(expected = "don't match the transport")]
async fn ensure_listen_addresses_consistent_with_transport_memory() {
	let listen_addr = config::build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(0_u16)];

	let _ = TestNetworkBuilder::new(Handle::current())
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
		.start_network();
}

#[tokio::test]
#[should_panic(expected = "don't match the transport")]
async fn ensure_listen_addresses_consistent_with_transport_not_memory() {
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];

	let _ = TestNetworkBuilder::new(Handle::current())
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

	let _ = TestNetworkBuilder::new(Handle::current())
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

	let _ = TestNetworkBuilder::new(Handle::current())
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

	let _ = TestNetworkBuilder::new(Handle::current())
		.with_config(config::NetworkConfiguration {
			listen_addresses: vec![listen_addr.clone()],
			transport: TransportConfig::MemoryOnly,
			default_peers_set: SetConfig {
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

	let _ = TestNetworkBuilder::new(Handle::current())
		.with_config(config::NetworkConfiguration {
			listen_addresses: vec![listen_addr.clone()],
			default_peers_set: SetConfig {
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
		.start_network();
}

#[tokio::test]
#[should_panic(expected = "don't match the transport")]
async fn ensure_public_addresses_consistent_with_transport_memory() {
	let listen_addr = config::build_multiaddr![Memory(rand::random::<u64>())];
	let public_address = config::build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(0_u16)];

	let _ = TestNetworkBuilder::new(Handle::current())
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
		.start_network();
}

#[tokio::test]
#[should_panic(expected = "don't match the transport")]
async fn ensure_public_addresses_consistent_with_transport_not_memory() {
	let listen_addr = config::build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(0_u16)];
	let public_address = config::build_multiaddr![Memory(rand::random::<u64>())];

	let _ = TestNetworkBuilder::new(Handle::current())
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
		.start_network();
}
