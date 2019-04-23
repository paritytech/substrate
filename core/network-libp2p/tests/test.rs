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

use futures::{future, stream, prelude::*, try_ready};
use rand::seq::SliceRandom;
use std::io;
use substrate_network_libp2p::{CustomMessage, multiaddr::Protocol, ServiceEvent, build_multiaddr};

/// Builds two services. The second one and further have the first one as its bootstrap node.
/// This is to be used only for testing, and a panic will happen if something goes wrong.
fn build_nodes<TMsg>(num: usize) -> Vec<substrate_network_libp2p::Service<TMsg>>
	where TMsg: CustomMessage + Send + 'static
{
	let mut result: Vec<substrate_network_libp2p::Service<_>> = Vec::with_capacity(num);

	for _ in 0 .. num {
		let mut boot_nodes = Vec::new();
		if !result.is_empty() {
			let mut bootnode = result[0].listeners().next().unwrap().clone();
			bootnode.append(Protocol::P2p(result[0].peer_id().clone().into()));
			boot_nodes.push(bootnode.to_string());
		}

		let config = substrate_network_libp2p::NetworkConfiguration {
			listen_addresses: vec![build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(0u16)]],
			boot_nodes,
			..substrate_network_libp2p::NetworkConfiguration::default()
		};

		let proto = substrate_network_libp2p::RegisteredProtocol::new(&b"tst"[..], &[1]);
		result.push(substrate_network_libp2p::start_service(config, proto).unwrap().0);
	}

	result
}

#[test]
fn basic_two_nodes_connectivity() {
	let (mut service1, mut service2) = {
		let mut l = build_nodes::<Vec<u8>>(2).into_iter();
		let a = l.next().unwrap();
		let b = l.next().unwrap();
		(a, b)
	};

	let fut1 = future::poll_fn(move || -> io::Result<_> {
		match try_ready!(service1.poll()) {
			Some(ServiceEvent::OpenedCustomProtocol { version, .. }) => {
				assert_eq!(version, 1);
				Ok(Async::Ready(()))
			},
			_ => panic!(),
		}
	});

	let fut2 = future::poll_fn(move || -> io::Result<_> {
		match try_ready!(service2.poll()) {
			Some(ServiceEvent::OpenedCustomProtocol { version, .. }) => {
				assert_eq!(version, 1);
				Ok(Async::Ready(()))
			},
			_ => panic!(),
		}
	});

	let combined = fut1.select(fut2).map_err(|(err, _)| err);
	tokio::runtime::Runtime::new().unwrap().block_on_all(combined).unwrap();
}

#[test]
fn two_nodes_transfer_lots_of_packets() {
	// We spawn two nodes, then make the first one send lots of packets to the second one. The test
	// ends when the second one has received all of them.

	// Note that if we go too high, we will reach the limit to the number of simultaneous
	// substreams allowed by the multiplexer.
	const NUM_PACKETS: u32 = 5000;

	let (mut service1, mut service2) = {
		let mut l = build_nodes::<Vec<u8>>(2).into_iter();
		let a = l.next().unwrap();
		let b = l.next().unwrap();
		(a, b)
	};

	let fut1 = future::poll_fn(move || -> io::Result<_> {
		loop {
			match try_ready!(service1.poll()) {
				Some(ServiceEvent::OpenedCustomProtocol { peer_id, .. }) => {
					for n in 0 .. NUM_PACKETS {
						service1.send_custom_message(&peer_id, vec![(n % 256) as u8]);
					}
				},
				_ => panic!(),
			}
		}
	});

	let mut packet_counter = 0u32;
	let fut2 = future::poll_fn(move || -> io::Result<_> {
		loop {
			match try_ready!(service2.poll()) {
				Some(ServiceEvent::OpenedCustomProtocol { .. }) => {},
				Some(ServiceEvent::CustomMessage { message, .. }) => {
					assert_eq!(message.len(), 1);
					packet_counter += 1;
					if packet_counter == NUM_PACKETS {
						return Ok(Async::Ready(()))
					}
				}
				_ => panic!(),
			}
		}
	});

	let combined = fut1.select(fut2).map_err(|(err, _)| err);
	tokio::runtime::Runtime::new().unwrap().block_on(combined).unwrap();
}

#[test]
fn many_nodes_connectivity() {
	// Creates many nodes, then make sure that they are all connected to each other.
	// Note: if you increase this number, keep in mind that there's a limit to the number of
	// simultaneous connections which will make the test fail if it is reached. This can be
	// increased in the `NetworkConfiguration`.
	const NUM_NODES: usize = 25;

	let mut futures = build_nodes::<Vec<u8>>(NUM_NODES)
		.into_iter()
		.map(move |mut node| {
			let mut num_connecs = 0;
			stream::poll_fn(move || -> io::Result<_> {
				loop {
					const MAX_BANDWIDTH: u64 = NUM_NODES as u64 * 1024;		// 1kiB/s/node
					assert!(node.average_download_per_sec() < MAX_BANDWIDTH);
					assert!(node.average_upload_per_sec() < MAX_BANDWIDTH);

					match try_ready!(node.poll()) {
						Some(ServiceEvent::OpenedCustomProtocol { .. }) => {
							num_connecs += 1;
							assert!(num_connecs < NUM_NODES);
							if num_connecs == NUM_NODES - 1 {
								return Ok(Async::Ready(Some(true)))
							}
						}
						Some(ServiceEvent::ClosedCustomProtocol { .. }) => {
							let was_success = num_connecs == NUM_NODES - 1;
							num_connecs -= 1;
							if was_success && num_connecs < NUM_NODES - 1 {
								return Ok(Async::Ready(Some(false)))
							}
						}
						_ => panic!(),
					}
				}
			})
		})
		.collect::<Vec<_>>();

	let mut successes = 0;
	let combined = future::poll_fn(move || -> io::Result<_> {
		for node in futures.iter_mut() {
			match node.poll()? {
				Async::Ready(Some(true)) => successes += 1,
				Async::Ready(Some(false)) => successes -= 1,
				Async::Ready(None) => unreachable!(),
				Async::NotReady => ()
			}
		}

		if successes == NUM_NODES {
			Ok(Async::Ready(()))
		} else {
			Ok(Async::NotReady)
		}
	});

	tokio::runtime::Runtime::new().unwrap().block_on(combined).unwrap();
}

#[test]
fn basic_two_nodes_requests_in_parallel() {
	let (mut service1, mut service2) = {
		let mut l = build_nodes::<(Option<u64>, Vec<u8>)>(2).into_iter();
		let a = l.next().unwrap();
		let b = l.next().unwrap();
		(a, b)
	};

	// Generate random messages with or without a request id.
	let mut to_send = {
		let mut to_send = Vec::new();
		let mut next_id = 0;
		for _ in 0..200 { // Note: don't make that number too high or the CPU usage will explode.
			let id = if rand::random::<usize>() % 4 != 0 {
				let i = next_id;
				next_id += 1;
				Some(i)
			} else {
				None
			};

			let msg = (id, (0..10).map(|_| rand::random::<u8>()).collect::<Vec<_>>());
			to_send.push(msg);
		}
		to_send
	};

	// Clone `to_send` in `to_receive`. Below we will remove from `to_receive` the messages we
	// receive, until the list is empty.
	let mut to_receive = to_send.clone();
	to_send.shuffle(&mut rand::thread_rng());

	let fut1 = future::poll_fn(move || -> io::Result<_> {
		loop {
			match try_ready!(service1.poll()) {
				Some(ServiceEvent::OpenedCustomProtocol { peer_id, .. }) => {
					for msg in to_send.drain(..) {
						service1.send_custom_message(&peer_id, msg);
					}
				},
				_ => panic!(),
			}
		}
	});

	let fut2 = future::poll_fn(move || -> io::Result<_> {
		loop {
			match try_ready!(service2.poll()) {
				Some(ServiceEvent::OpenedCustomProtocol { .. }) => {},
				Some(ServiceEvent::CustomMessage { message, .. }) => {
					let pos = to_receive.iter().position(|m| *m == message).unwrap();
					to_receive.remove(pos);
					if to_receive.is_empty() {
						return Ok(Async::Ready(()))
					}
				}
				_ => panic!(),
			}
		}
	});

	let combined = fut1.select(fut2).map_err(|(err, _)| err);
	tokio::runtime::Runtime::new().unwrap().block_on_all(combined).unwrap();
}
