// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

#![cfg(test)]

use futures::{prelude::*, ready};
use codec::{Encode, Decode};
use libp2p::core::nodes::listeners::ListenerId;
use libp2p::core::ConnectedPoint;
use libp2p::swarm::{Swarm, ProtocolsHandler, IntoProtocolsHandler};
use libp2p::swarm::{PollParameters, NetworkBehaviour, NetworkBehaviourAction};
use libp2p::{PeerId, Multiaddr, Transport};
use rand::seq::SliceRandom;
use std::{error, io, task::Context, task::Poll, time::Duration};
use crate::message::Message;
use crate::protocol::legacy_proto::{LegacyProto, LegacyProtoOut};
use sp_test_primitives::Block;

/// Builds two nodes that have each other as bootstrap nodes.
/// This is to be used only for testing, and a panic will happen if something goes wrong.
fn build_nodes() -> (Swarm<CustomProtoWithAddr>, Swarm<CustomProtoWithAddr>) {
	let mut out = Vec::with_capacity(2);

	let keypairs: Vec<_> = (0..2).map(|_| libp2p::identity::Keypair::generate_ed25519()).collect();
	let addrs: Vec<Multiaddr> = (0..2)
		.map(|_| format!("/memory/{}", rand::random::<u64>()).parse().unwrap())
		.collect();

	for index in 0 .. 2 {
		let keypair = keypairs[index].clone();
		let transport = libp2p::core::transport::MemoryTransport
			.and_then(move |out, endpoint| {
				let secio = libp2p::secio::SecioConfig::new(keypair);
				libp2p::core::upgrade::apply(
					out,
					secio,
					endpoint,
					libp2p::core::upgrade::Version::V1
				)
			})
			.and_then(move |(peer_id, stream), endpoint| {
				libp2p::core::upgrade::apply(
					stream,
					libp2p::yamux::Config::default(),
					endpoint,
					libp2p::core::upgrade::Version::V1
				)
					.map_ok(|muxer| (peer_id, libp2p::core::muxing::StreamMuxerBox::new(muxer)))
			})
			.timeout(Duration::from_secs(20))
			.map_err(|err| io::Error::new(io::ErrorKind::Other, err))
			.boxed();

		let (peerset, _) = sc_peerset::Peerset::from_config(sc_peerset::PeersetConfig {
			in_peers: 25,
			out_peers: 25,
			bootnodes: if index == 0 {
				keypairs
					.iter()
					.skip(1)
					.map(|keypair| keypair.public().into_peer_id())
					.collect()
			} else {
				vec![]
			},
			reserved_only: false,
			reserved_nodes: Vec::new(),
		});

		let behaviour = CustomProtoWithAddr {
			inner: LegacyProto::new(&b"test"[..], &[1], peerset),
			addrs: addrs
				.iter()
				.enumerate()
				.filter_map(|(n, a)| if n != index {
					Some((keypairs[n].public().into_peer_id(), a.clone()))
				} else {
					None
				})
				.collect(),
		};

		let mut swarm = Swarm::new(
			transport,
			behaviour,
			keypairs[index].public().into_peer_id()
		);
		Swarm::listen_on(&mut swarm, addrs[index].clone()).unwrap();
		out.push(swarm);
	}

	// Final output
	let mut out_iter = out.into_iter();
	let first = out_iter.next().unwrap();
	let second = out_iter.next().unwrap();
	(first, second)
}

/// Wraps around the `CustomBehaviour` network behaviour, and adds hardcoded node addresses to it.
struct CustomProtoWithAddr {
	inner: LegacyProto,
	addrs: Vec<(PeerId, Multiaddr)>,
}

impl std::ops::Deref for CustomProtoWithAddr {
	type Target = LegacyProto;

	fn deref(&self) -> &Self::Target {
		&self.inner
	}
}

impl std::ops::DerefMut for CustomProtoWithAddr {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.inner
	}
}

impl NetworkBehaviour for CustomProtoWithAddr {
	type ProtocolsHandler = <LegacyProto as NetworkBehaviour>::ProtocolsHandler;
	type OutEvent = <LegacyProto as NetworkBehaviour>::OutEvent;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		self.inner.new_handler()
	}

	fn addresses_of_peer(&mut self, peer_id: &PeerId) -> Vec<Multiaddr> {
		let mut list = self.inner.addresses_of_peer(peer_id);
		for (p, a) in self.addrs.iter() {
			if p == peer_id {
				list.push(a.clone());
			}
		}
		list
	}

	fn inject_connected(&mut self, peer_id: PeerId, endpoint: ConnectedPoint) {
		self.inner.inject_connected(peer_id, endpoint)
	}

	fn inject_disconnected(&mut self, peer_id: &PeerId, endpoint: ConnectedPoint) {
		self.inner.inject_disconnected(peer_id, endpoint)
	}

	fn inject_node_event(
		&mut self,
		peer_id: PeerId,
		event: <<Self::ProtocolsHandler as IntoProtocolsHandler>::Handler as ProtocolsHandler>::OutEvent
	) {
		self.inner.inject_node_event(peer_id, event)
	}

	fn poll(
		&mut self,
		cx: &mut Context,
		params: &mut impl PollParameters
	) -> Poll<
		NetworkBehaviourAction<
			<<Self::ProtocolsHandler as IntoProtocolsHandler>::Handler as ProtocolsHandler>::InEvent,
			Self::OutEvent
		>
	> {
		self.inner.poll(cx, params)
	}

	fn inject_replaced(&mut self, peer_id: PeerId, closed_endpoint: ConnectedPoint, new_endpoint: ConnectedPoint) {
		self.inner.inject_replaced(peer_id, closed_endpoint, new_endpoint)
	}

	fn inject_addr_reach_failure(&mut self, peer_id: Option<&PeerId>, addr: &Multiaddr, error: &dyn std::error::Error) {
		self.inner.inject_addr_reach_failure(peer_id, addr, error)
	}

	fn inject_dial_failure(&mut self, peer_id: &PeerId) {
		self.inner.inject_dial_failure(peer_id)
	}

	fn inject_new_listen_addr(&mut self, addr: &Multiaddr) {
		self.inner.inject_new_listen_addr(addr)
	}

	fn inject_expired_listen_addr(&mut self, addr: &Multiaddr) {
		self.inner.inject_expired_listen_addr(addr)
	}

	fn inject_new_external_addr(&mut self, addr: &Multiaddr) {
		self.inner.inject_new_external_addr(addr)
	}

	fn inject_listener_error(&mut self, id: ListenerId, err: &(dyn error::Error + 'static)) {
		self.inner.inject_listener_error(id, err);
	}

	fn inject_listener_closed(&mut self, id: ListenerId) {
		self.inner.inject_listener_closed(id);
	}
}

#[test]
fn two_nodes_transfer_lots_of_packets() {
	// We spawn two nodes, then make the first one send lots of packets to the second one. The test
	// ends when the second one has received all of them.

	// Note that if we go too high, we will reach the limit to the number of simultaneous
	// substreams allowed by the multiplexer.
	const NUM_PACKETS: u32 = 5000;

	let (mut service1, mut service2) = build_nodes();

	let fut1 = future::poll_fn(move |cx| -> Poll<()> {
		loop {
			match ready!(service1.poll_next_unpin(cx)) {
				Some(LegacyProtoOut::CustomProtocolOpen { peer_id, .. }) => {
					for n in 0 .. NUM_PACKETS {
						service1.send_packet(
							&peer_id,
							Message::<Block>::ChainSpecific(vec![(n % 256) as u8]).encode()
						);
					}
				},
				_ => panic!(),
			}
		}
	});

	let mut packet_counter = 0u32;
	let fut2 = future::poll_fn(move |cx| {
		loop {
			match ready!(service2.poll_next_unpin(cx)) {
				Some(LegacyProtoOut::CustomProtocolOpen { .. }) => {},
				Some(LegacyProtoOut::CustomMessage { message, .. }) => {
					match Message::<Block>::decode(&mut &message[..]).unwrap() {
						Message::<Block>::ChainSpecific(message) => {
							assert_eq!(message.len(), 1);
							packet_counter += 1;
							if packet_counter == NUM_PACKETS {
								return Poll::Ready(())
							}
						},
						_ => panic!(),
					}
				}
				_ => panic!(),
			}
		}
	});

	futures::executor::block_on(async move {
		future::select(fut1, fut2).await;
	});
}

#[test]
fn basic_two_nodes_requests_in_parallel() {
	let (mut service1, mut service2) = build_nodes();

	// Generate random messages with or without a request id.
	let mut to_send = {
		let mut to_send = Vec::new();
		for _ in 0..200 { // Note: don't make that number too high or the CPU usage will explode.
			let msg = (0..10).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
			to_send.push(Message::<Block>::ChainSpecific(msg));
		}
		to_send
	};

	// Clone `to_send` in `to_receive`. Below we will remove from `to_receive` the messages we
	// receive, until the list is empty.
	let mut to_receive = to_send.clone();
	to_send.shuffle(&mut rand::thread_rng());

	let fut1 = future::poll_fn(move |cx| -> Poll<()> {
		loop {
			match ready!(service1.poll_next_unpin(cx)) {
				Some(LegacyProtoOut::CustomProtocolOpen { peer_id, .. }) => {
					for msg in to_send.drain(..) {
						service1.send_packet(&peer_id, msg.encode());
					}
				},
				_ => panic!(),
			}
		}
	});

	let fut2 = future::poll_fn(move |cx| {
		loop {
			match ready!(service2.poll_next_unpin(cx)) {
				Some(LegacyProtoOut::CustomProtocolOpen { .. }) => {},
				Some(LegacyProtoOut::CustomMessage { message, .. }) => {
					let pos = to_receive.iter().position(|m| m.encode() == message).unwrap();
					to_receive.remove(pos);
					if to_receive.is_empty() {
						return Poll::Ready(())
					}
				}
				_ => panic!(),
			}
		}
	});

	futures::executor::block_on(async move {
		future::select(fut1, fut2).await;
	});
}

#[test]
fn reconnect_after_disconnect() {
	// We connect two nodes together, then force a disconnect (through the API of the `Service`),
	// check that the disconnect worked, and finally check whether they successfully reconnect.

	let (mut service1, mut service2) = build_nodes();

	// For this test, the services can be in the following states.
	#[derive(Debug, Copy, Clone, PartialEq, Eq)]
	enum ServiceState { NotConnected, FirstConnec, Disconnected, ConnectedAgain }
	let mut service1_state = ServiceState::NotConnected;
	let mut service2_state = ServiceState::NotConnected;

	// Run the events loops.
	futures::executor::block_on(future::poll_fn(|cx| -> Poll<Result<_, io::Error>> {
		loop {
			let mut service1_not_ready = false;

			match service1.poll_next_unpin(cx) {
				Poll::Ready(Some(LegacyProtoOut::CustomProtocolOpen { .. })) => {
					match service1_state {
						ServiceState::NotConnected => {
							service1_state = ServiceState::FirstConnec;
							if service2_state == ServiceState::FirstConnec {
								service1.disconnect_peer(Swarm::local_peer_id(&service2));
							}
						},
						ServiceState::Disconnected => service1_state = ServiceState::ConnectedAgain,
						ServiceState::FirstConnec | ServiceState::ConnectedAgain => panic!(),
					}
				},
				Poll::Ready(Some(LegacyProtoOut::CustomProtocolClosed { .. })) => {
					match service1_state {
						ServiceState::FirstConnec => service1_state = ServiceState::Disconnected,
						ServiceState::ConnectedAgain| ServiceState::NotConnected |
						ServiceState::Disconnected => panic!(),
					}
				},
				Poll::Pending => service1_not_ready = true,
				_ => panic!()
			}

			match service2.poll_next_unpin(cx) {
				Poll::Ready(Some(LegacyProtoOut::CustomProtocolOpen { .. })) => {
					match service2_state {
						ServiceState::NotConnected => {
							service2_state = ServiceState::FirstConnec;
							if service1_state == ServiceState::FirstConnec {
								service1.disconnect_peer(Swarm::local_peer_id(&service2));
							}
						},
						ServiceState::Disconnected => service2_state = ServiceState::ConnectedAgain,
						ServiceState::FirstConnec | ServiceState::ConnectedAgain => panic!(),
					}
				},
				Poll::Ready(Some(LegacyProtoOut::CustomProtocolClosed { .. })) => {
					match service2_state {
						ServiceState::FirstConnec => service2_state = ServiceState::Disconnected,
						ServiceState::ConnectedAgain| ServiceState::NotConnected |
						ServiceState::Disconnected => panic!(),
					}
				},
				Poll::Pending if service1_not_ready => break,
				Poll::Pending => {}
				_ => panic!()
			}
		}

		if service1_state == ServiceState::ConnectedAgain && service2_state == ServiceState::ConnectedAgain {
			Poll::Ready(Ok(()))
		} else {
			Poll::Pending
		}
	})).unwrap();

	// Do a second 3-seconds run to make sure we don't get disconnected immediately again.
	let mut delay = futures_timer::Delay::new(Duration::from_secs(3));
	futures::executor::block_on(future::poll_fn(|cx| -> Poll<Result<_, io::Error>> {
		match service1.poll_next_unpin(cx) {
			Poll::Pending => {},
			_ => panic!()
		}

		match service2.poll_next_unpin(cx) {
			Poll::Pending => {},
			_ => panic!()
		}

		if let Poll::Ready(()) = delay.poll_unpin(cx) {
			Poll::Ready(Ok(()))
		} else {
			Poll::Pending
		}
	})).unwrap();
}
