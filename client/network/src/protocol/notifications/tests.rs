// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

#![cfg(test)]

use crate::protocol::notifications::{Notifications, NotificationsOut};

use futures::prelude::*;
use libp2p::{PeerId, Multiaddr, Transport};
use libp2p::core::{
	connection::{ConnectionId, ListenerId},
	ConnectedPoint,
	transport::MemoryTransport,
	upgrade
};
use libp2p::{identity, noise, yamux};
use libp2p::swarm::{
	Swarm, ProtocolsHandler, IntoProtocolsHandler, PollParameters,
	NetworkBehaviour, NetworkBehaviourAction
};
use std::{error, io, iter, task::{Context, Poll}, time::Duration};

/// Builds two nodes that have each other as bootstrap nodes.
/// This is to be used only for testing, and a panic will happen if something goes wrong.
fn build_nodes() -> (Swarm<CustomProtoWithAddr>, Swarm<CustomProtoWithAddr>) {
	let mut out = Vec::with_capacity(2);

	let keypairs: Vec<_> = (0..2).map(|_| identity::Keypair::generate_ed25519()).collect();
	let addrs: Vec<Multiaddr> = (0..2)
		.map(|_| format!("/memory/{}", rand::random::<u64>()).parse().unwrap())
		.collect();

	for index in 0 .. 2 {
		let keypair = keypairs[index].clone();

		let noise_keys = noise::Keypair::<noise::X25519Spec>::new()
			.into_authentic(&keypair)
			.unwrap();

		let transport = MemoryTransport
			.upgrade(upgrade::Version::V1)
			.authenticate(noise::NoiseConfig::xx(noise_keys).into_authenticated())
			.multiplex(yamux::YamuxConfig::default())
			.timeout(Duration::from_secs(20))
			.boxed();

		let (peerset, _) = sc_peerset::Peerset::from_config(sc_peerset::PeersetConfig {
			sets: vec![
				sc_peerset::SetConfig {
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
					reserved_nodes: Default::default(),
					reserved_only: false,
				}
			],
		});

		let behaviour = CustomProtoWithAddr {
			inner: Notifications::new(peerset, iter::once(("/foo".into(), Vec::new(), 1024 * 1024))),
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
		swarm.listen_on(addrs[index].clone()).unwrap();
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
	inner: Notifications,
	addrs: Vec<(PeerId, Multiaddr)>,
}

impl std::ops::Deref for CustomProtoWithAddr {
	type Target = Notifications;

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
	type ProtocolsHandler = <Notifications as NetworkBehaviour>::ProtocolsHandler;
	type OutEvent = <Notifications as NetworkBehaviour>::OutEvent;

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

	fn inject_connected(&mut self, peer_id: &PeerId) {
		self.inner.inject_connected(peer_id)
	}

	fn inject_disconnected(&mut self, peer_id: &PeerId) {
		self.inner.inject_disconnected(peer_id)
	}

	fn inject_connection_established(&mut self, peer_id: &PeerId, conn: &ConnectionId, endpoint: &ConnectedPoint) {
		self.inner.inject_connection_established(peer_id, conn, endpoint)
	}

	fn inject_connection_closed(&mut self, peer_id: &PeerId, conn: &ConnectionId, endpoint: &ConnectedPoint) {
		self.inner.inject_connection_closed(peer_id, conn, endpoint)
	}

	fn inject_event(
		&mut self,
		peer_id: PeerId,
		connection: ConnectionId,
		event: <<Self::ProtocolsHandler as IntoProtocolsHandler>::Handler as ProtocolsHandler>::OutEvent
	) {
		self.inner.inject_event(peer_id, connection, event)
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

	fn inject_addr_reach_failure(&mut self, peer_id: Option<&PeerId>, addr: &Multiaddr, error: &dyn std::error::Error) {
		self.inner.inject_addr_reach_failure(peer_id, addr, error)
	}

	fn inject_dial_failure(&mut self, peer_id: &PeerId) {
		self.inner.inject_dial_failure(peer_id)
	}

	fn inject_new_listener(&mut self, id: ListenerId) {
		self.inner.inject_new_listener(id)
	}

	fn inject_new_listen_addr(&mut self, id: ListenerId, addr: &Multiaddr) {
		self.inner.inject_new_listen_addr(id, addr)
	}

	fn inject_expired_listen_addr(&mut self, id: ListenerId, addr: &Multiaddr) {
		self.inner.inject_expired_listen_addr(id, addr)
	}

	fn inject_new_external_addr(&mut self, addr: &Multiaddr) {
		self.inner.inject_new_external_addr(addr)
	}

	fn inject_expired_external_addr(&mut self, addr: &Multiaddr) {
		self.inner.inject_expired_external_addr(addr)
	}

	fn inject_listener_error(&mut self, id: ListenerId, err: &(dyn error::Error + 'static)) {
		self.inner.inject_listener_error(id, err);
	}

	fn inject_listener_closed(&mut self, id: ListenerId, reason: Result<(), &io::Error>) {
		self.inner.inject_listener_closed(id, reason);
	}
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

	futures::executor::block_on(async move {
		loop {
			// Grab next event from services.
			let event = {
				let s1 = service1.next();
				let s2 = service2.next();
				futures::pin_mut!(s1, s2);
				match future::select(s1, s2).await {
					future::Either::Left((ev, _)) => future::Either::Left(ev),
					future::Either::Right((ev, _)) => future::Either::Right(ev),
				}
			};

			match event {
				future::Either::Left(NotificationsOut::CustomProtocolOpen { .. }) => {
					match service1_state {
						ServiceState::NotConnected => {
							service1_state = ServiceState::FirstConnec;
							if service2_state == ServiceState::FirstConnec {
								service1.behaviour_mut().disconnect_peer(
									Swarm::local_peer_id(&service2),
									sc_peerset::SetId::from(0)
								);
							}
						},
						ServiceState::Disconnected => service1_state = ServiceState::ConnectedAgain,
						ServiceState::FirstConnec | ServiceState::ConnectedAgain => panic!(),
					}
				},
				future::Either::Left(NotificationsOut::CustomProtocolClosed { .. }) => {
					match service1_state {
						ServiceState::FirstConnec => service1_state = ServiceState::Disconnected,
						ServiceState::ConnectedAgain| ServiceState::NotConnected |
						ServiceState::Disconnected => panic!(),
					}
				},
				future::Either::Right(NotificationsOut::CustomProtocolOpen { .. }) => {
					match service2_state {
						ServiceState::NotConnected => {
							service2_state = ServiceState::FirstConnec;
							if service1_state == ServiceState::FirstConnec {
								service1.behaviour_mut().disconnect_peer(
									Swarm::local_peer_id(&service2),
									sc_peerset::SetId::from(0)
								);
							}
						},
						ServiceState::Disconnected => service2_state = ServiceState::ConnectedAgain,
						ServiceState::FirstConnec | ServiceState::ConnectedAgain => panic!(),
					}
				},
				future::Either::Right(NotificationsOut::CustomProtocolClosed { .. }) => {
					match service2_state {
						ServiceState::FirstConnec => service2_state = ServiceState::Disconnected,
						ServiceState::ConnectedAgain| ServiceState::NotConnected |
						ServiceState::Disconnected => panic!(),
					}
				},
				_ => {}
			}

			if service1_state == ServiceState::ConnectedAgain && service2_state == ServiceState::ConnectedAgain {
				break;
			}
		}

		// Now that the two services have disconnected and reconnected, wait for 3 seconds and
		// check whether they're still connected.
		let mut delay = futures_timer::Delay::new(Duration::from_secs(3));

		loop {
			// Grab next event from services.
			let event = {
				let s1 = service1.next();
				let s2 = service2.next();
				futures::pin_mut!(s1, s2);
				match future::select(future::select(s1, s2), &mut delay).await {
					future::Either::Right(_) => break,	// success
					future::Either::Left((future::Either::Left((ev, _)), _)) => ev,
					future::Either::Left((future::Either::Right((ev, _)), _)) => ev,
				}
			};

			match event {
				NotificationsOut::CustomProtocolOpen { .. } |
				NotificationsOut::CustomProtocolClosed { .. } => panic!(),
				_ => {}
			}
		}
	});
}
