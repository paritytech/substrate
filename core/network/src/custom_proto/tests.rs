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

#![cfg(test)]

use futures::{future, prelude::*, try_ready};
use libp2p::core::{nodes::Substream, swarm::Swarm};
use libp2p::core::{transport::boxed::Boxed, muxing::StreamMuxerBox};
use libp2p::core::{ProtocolsHandler, protocols_handler::IntoProtocolsHandler};
use libp2p::core::swarm::{ConnectedPoint, NetworkBehaviour, NetworkBehaviourAction};
use libp2p::core::swarm::PollParameters;
use libp2p::{PeerId, Multiaddr, Transport};
use rand::seq::SliceRandom;
use std::{io, time::Duration, time::Instant};
use test_client::runtime::Block;
use crate::protocol::message::{Message as MessageAlias, generic::Message};
use crate::custom_proto::{CustomProto, CustomProtoOut, CustomMessage};

/// Builds two nodes that have each other as bootstrap nodes.
/// This is to be used only for testing, and a panic will happen if something goes wrong.
fn build_nodes<T: CustomMessage + Send + 'static>()
-> (
	Swarm<Boxed<(PeerId, StreamMuxerBox), io::Error>, CustomProtoWithAddr<T>>,
	Swarm<Boxed<(PeerId, StreamMuxerBox), io::Error>, CustomProtoWithAddr<T>>
) {
	let mut out = Vec::with_capacity(2);

	let keypairs: Vec<_> = (0..2).map(|_| libp2p::identity::Keypair::generate_ed25519()).collect();
	let addrs: Vec<Multiaddr> = (0..2)
		.map(|_| format!("/memory/{}", rand::random::<u64>()).parse().unwrap())
		.collect();

	for index in 0 .. 2 {
		let transport = libp2p::core::transport::MemoryTransport
			.with_upgrade(libp2p::secio::SecioConfig::new(keypairs[index].clone()))
			.and_then(move |out, endpoint| {
				let peer_id = out.remote_key.into_peer_id();
				libp2p::core::upgrade::apply(out.stream, libp2p::yamux::Config::default(), endpoint)
					.map(|muxer| (peer_id, libp2p::core::muxing::StreamMuxerBox::new(muxer)))
			})
			.with_timeout(Duration::from_secs(20))
			.map_err(|err| io::Error::new(io::ErrorKind::Other, err))
			.boxed();

		let (peerset, _) = peerset::Peerset::from_config(peerset::PeersetConfig {
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
			inner: CustomProto::new(&b"test"[..], &[1], peerset),
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

		let mut swarm = libp2p::core::swarm::Swarm::new(
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
struct CustomProtoWithAddr<T: CustomMessage + Send + 'static> {
	inner: CustomProto<T, Substream<StreamMuxerBox>>,
	addrs: Vec<(PeerId, Multiaddr)>,
}

impl<T: CustomMessage + Send + 'static> std::ops::Deref for CustomProtoWithAddr<T> {
	type Target = CustomProto<T, Substream<StreamMuxerBox>>;

	fn deref(&self) -> &Self::Target {
		&self.inner
	}
}

impl<T: CustomMessage + Send + 'static> std::ops::DerefMut for CustomProtoWithAddr<T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.inner
	}
}

impl<T: CustomMessage + Send + 'static> NetworkBehaviour for CustomProtoWithAddr<T> {
	type ProtocolsHandler =
		<CustomProto<T, Substream<StreamMuxerBox>> as NetworkBehaviour>::ProtocolsHandler;
	type OutEvent = <CustomProto<T, Substream<StreamMuxerBox>> as NetworkBehaviour>::OutEvent;

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
		params: &mut PollParameters
	) -> Async<
		NetworkBehaviourAction<
			<<Self::ProtocolsHandler as IntoProtocolsHandler>::Handler as ProtocolsHandler>::InEvent,
			Self::OutEvent
		>
	> {
		self.inner.poll(params)
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
}

#[test]
fn two_nodes_transfer_lots_of_packets() {
	// We spawn two nodes, then make the first one send lots of packets to the second one. The test
	// ends when the second one has received all of them.

	// Note that if we go too high, we will reach the limit to the number of simultaneous
	// substreams allowed by the multiplexer.
	const NUM_PACKETS: u32 = 5000;

	let (mut service1, mut service2) = build_nodes::<MessageAlias<Block>>();

	let fut1 = future::poll_fn(move || -> io::Result<_> {
		loop {
			match try_ready!(service1.poll()) {
				Some(CustomProtoOut::CustomProtocolOpen { peer_id, .. }) => {
					for n in 0 .. NUM_PACKETS {
						service1.send_packet(
							&peer_id,
							Message::ChainSpecific(vec![(n % 256) as u8])
						);
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
				Some(CustomProtoOut::CustomProtocolOpen { .. }) => {},
				Some(CustomProtoOut::CustomMessage { message: Message::ChainSpecific(message), .. }) => {
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
	let _ = tokio::runtime::Runtime::new().unwrap().block_on(combined).unwrap();
}

#[test]
fn basic_two_nodes_requests_in_parallel() {
	let (mut service1, mut service2) = build_nodes::<MessageAlias<Block>>();

	// Generate random messages with or without a request id.
	let mut to_send = {
		let mut to_send = Vec::new();
		for _ in 0..200 { // Note: don't make that number too high or the CPU usage will explode.
			let msg = (0..10).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
			to_send.push(Message::ChainSpecific(msg));
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
				Some(CustomProtoOut::CustomProtocolOpen { peer_id, .. }) => {
					for msg in to_send.drain(..) {
						service1.send_packet(&peer_id, msg);
					}
				},
				_ => panic!(),
			}
		}
	});

	let fut2 = future::poll_fn(move || -> io::Result<_> {
		loop {
			match try_ready!(service2.poll()) {
				Some(CustomProtoOut::CustomProtocolOpen { .. }) => {},
				Some(CustomProtoOut::CustomMessage { message, .. }) => {
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
	let _ = tokio::runtime::Runtime::new().unwrap().block_on_all(combined).unwrap();
}

#[test]
fn reconnect_after_disconnect() {
	// We connect two nodes together, then force a disconnect (through the API of the `Service`),
	// check that the disconnect worked, and finally check whether they successfully reconnect.

	let (mut service1, mut service2) = build_nodes::<MessageAlias<Block>>();

	// We use the `current_thread` runtime because it doesn't require us to have `'static` futures.
	let mut runtime = tokio::runtime::current_thread::Runtime::new().unwrap();

	// For this test, the services can be in the following states.
	#[derive(Debug, Copy, Clone, PartialEq, Eq)]
	enum ServiceState { NotConnected, FirstConnec, Disconnected, ConnectedAgain }
	let mut service1_state = ServiceState::NotConnected;
	let mut service2_state = ServiceState::NotConnected;

	// Run the events loops.
	runtime.block_on(future::poll_fn(|| -> Result<_, io::Error> {
		loop {
			let mut service1_not_ready = false;

			match service1.poll().unwrap() {
				Async::Ready(Some(CustomProtoOut::CustomProtocolOpen { .. })) => {
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
				Async::Ready(Some(CustomProtoOut::CustomProtocolClosed { .. })) => {
					match service1_state {
						ServiceState::FirstConnec => service1_state = ServiceState::Disconnected,
						ServiceState::ConnectedAgain| ServiceState::NotConnected |
						ServiceState::Disconnected => panic!(),
					}
				},
				Async::NotReady => service1_not_ready = true,
				_ => panic!()
			}

			match service2.poll().unwrap() {
				Async::Ready(Some(CustomProtoOut::CustomProtocolOpen { .. })) => {
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
				Async::Ready(Some(CustomProtoOut::CustomProtocolClosed { .. })) => {
					match service2_state {
						ServiceState::FirstConnec => service2_state = ServiceState::Disconnected,
						ServiceState::ConnectedAgain| ServiceState::NotConnected |
						ServiceState::Disconnected => panic!(),
					}
				},
				Async::NotReady if service1_not_ready => break,
				Async::NotReady => {}
				_ => panic!()
			}
		}

		if service1_state == ServiceState::ConnectedAgain && service2_state == ServiceState::ConnectedAgain {
			Ok(Async::Ready(()))
		} else {
			Ok(Async::NotReady)
		}
	})).unwrap();

	// Do a second 3-seconds run to make sure we don't get disconnected immediately again.
	let mut delay = tokio::timer::Delay::new(Instant::now() + Duration::from_secs(3));
	runtime.block_on(future::poll_fn(|| -> Result<_, io::Error> {
		match service1.poll().unwrap() {
			Async::NotReady => {},
			_ => panic!()
		}

		match service2.poll().unwrap() {
			Async::NotReady => {},
			_ => panic!()
		}

		if let Async::Ready(()) = delay.poll().unwrap() {
			Ok(Async::Ready(()))
		} else {
			Ok(Async::NotReady)
		}
	})).unwrap();
}
