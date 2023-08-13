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

#![cfg(test)]

use crate::{
	peer_store::PeerStore,
	protocol::notifications::{Notifications, NotificationsOut, ProtocolConfig},
	protocol_controller::{ProtoSetConfig, ProtocolController, SetId},
};

use futures::{future::BoxFuture, prelude::*};
use libp2p::{
	core::{transport::MemoryTransport, upgrade, Endpoint},
	identity, noise,
	swarm::{
		behaviour::FromSwarm, ConnectionDenied, ConnectionId, Executor, NetworkBehaviour,
		PollParameters, Swarm, SwarmBuilder, SwarmEvent, THandler, THandlerInEvent,
		THandlerOutEvent, ToSwarm,
	},
	yamux, Multiaddr, PeerId, Transport,
};
use sc_utils::mpsc::tracing_unbounded;
use std::{
	iter,
	pin::Pin,
	task::{Context, Poll},
	time::Duration,
};

struct TokioExecutor(tokio::runtime::Runtime);
impl Executor for TokioExecutor {
	fn exec(&self, f: Pin<Box<dyn Future<Output = ()> + Send>>) {
		let _ = self.0.spawn(f);
	}
}

/// Builds two nodes that have each other as bootstrap nodes.
/// This is to be used only for testing, and a panic will happen if something goes wrong.
fn build_nodes() -> (Swarm<CustomProtoWithAddr>, Swarm<CustomProtoWithAddr>) {
	let mut out = Vec::with_capacity(2);

	let keypairs: Vec<_> = (0..2).map(|_| identity::Keypair::generate_ed25519()).collect();
	let addrs: Vec<Multiaddr> = (0..2)
		.map(|_| format!("/memory/{}", rand::random::<u64>()).parse().unwrap())
		.collect();

	for index in 0..2 {
		let keypair = keypairs[index].clone();

		let transport = MemoryTransport::new()
			.upgrade(upgrade::Version::V1)
			.authenticate(noise::Config::new(&keypair).unwrap())
			.multiplex(yamux::Config::default())
			.timeout(Duration::from_secs(20))
			.boxed();

		let peer_store = PeerStore::new(if index == 0 {
			keypairs.iter().skip(1).map(|keypair| keypair.public().to_peer_id()).collect()
		} else {
			vec![]
		});

		let (to_notifications, from_controller) =
			tracing_unbounded("test_protocol_controller_to_notifications", 10_000);

		let (controller_handle, controller) = ProtocolController::new(
			SetId::from(0),
			ProtoSetConfig {
				in_peers: 25,
				out_peers: 25,
				reserved_nodes: Default::default(),
				reserved_only: false,
			},
			to_notifications,
			Box::new(peer_store.handle()),
		);

		let behaviour = CustomProtoWithAddr {
			inner: Notifications::new(
				vec![controller_handle],
				from_controller,
				iter::once(ProtocolConfig {
					name: "/foo".into(),
					fallback_names: Vec::new(),
					handshake: Vec::new(),
					max_notification_size: 1024 * 1024,
				}),
			),
			peer_store_future: peer_store.run().boxed(),
			protocol_controller_future: controller.run().boxed(),
			addrs: addrs
				.iter()
				.enumerate()
				.filter_map(|(n, a)| {
					if n != index {
						Some((keypairs[n].public().to_peer_id(), a.clone()))
					} else {
						None
					}
				})
				.collect(),
		};

		let runtime = tokio::runtime::Runtime::new().unwrap();
		let mut swarm = SwarmBuilder::with_executor(
			transport,
			behaviour,
			keypairs[index].public().to_peer_id(),
			TokioExecutor(runtime),
		)
		.build();
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
	peer_store_future: BoxFuture<'static, ()>,
	protocol_controller_future: BoxFuture<'static, ()>,
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
	type ConnectionHandler = <Notifications as NetworkBehaviour>::ConnectionHandler;
	type ToSwarm = <Notifications as NetworkBehaviour>::ToSwarm;

	fn handle_pending_inbound_connection(
		&mut self,
		connection_id: ConnectionId,
		local_addr: &Multiaddr,
		remote_addr: &Multiaddr,
	) -> Result<(), ConnectionDenied> {
		self.inner
			.handle_pending_inbound_connection(connection_id, local_addr, remote_addr)
	}

	fn handle_pending_outbound_connection(
		&mut self,
		connection_id: ConnectionId,
		maybe_peer: Option<PeerId>,
		addresses: &[Multiaddr],
		effective_role: Endpoint,
	) -> Result<Vec<Multiaddr>, ConnectionDenied> {
		let mut list = self.inner.handle_pending_outbound_connection(
			connection_id,
			maybe_peer,
			addresses,
			effective_role,
		)?;
		if let Some(peer_id) = maybe_peer {
			for (p, a) in self.addrs.iter() {
				if *p == peer_id {
					list.push(a.clone());
				}
			}
		}
		Ok(list)
	}

	fn handle_established_inbound_connection(
		&mut self,
		connection_id: ConnectionId,
		peer: PeerId,
		local_addr: &Multiaddr,
		remote_addr: &Multiaddr,
	) -> Result<THandler<Self>, ConnectionDenied> {
		self.inner.handle_established_inbound_connection(
			connection_id,
			peer,
			local_addr,
			remote_addr,
		)
	}

	fn handle_established_outbound_connection(
		&mut self,
		connection_id: ConnectionId,
		peer: PeerId,
		addr: &Multiaddr,
		role_override: Endpoint,
	) -> Result<THandler<Self>, ConnectionDenied> {
		self.inner
			.handle_established_outbound_connection(connection_id, peer, addr, role_override)
	}

	fn on_swarm_event(&mut self, event: FromSwarm<Self::ConnectionHandler>) {
		self.inner.on_swarm_event(event);
	}

	fn on_connection_handler_event(
		&mut self,
		peer_id: PeerId,
		connection_id: ConnectionId,
		event: THandlerOutEvent<Self>,
	) {
		self.inner.on_connection_handler_event(peer_id, connection_id, event);
	}

	fn poll(
		&mut self,
		cx: &mut Context,
		params: &mut impl PollParameters,
	) -> Poll<ToSwarm<Self::ToSwarm, THandlerInEvent<Self>>> {
		let _ = self.peer_store_future.poll_unpin(cx);
		let _ = self.protocol_controller_future.poll_unpin(cx);

		self.inner.poll(cx, params)
	}
}

#[test]
fn reconnect_after_disconnect() {
	// We connect two nodes together, then force a disconnect (through the API of the `Service`),
	// check that the disconnect worked, and finally check whether they successfully reconnect.

	let (mut service1, mut service2) = build_nodes();

	// For this test, the services can be in the following states.
	#[derive(Debug, Copy, Clone, PartialEq, Eq)]
	enum ServiceState {
		NotConnected,
		FirstConnec,
		Disconnected,
		ConnectedAgain,
	}
	let mut service1_state = ServiceState::NotConnected;
	let mut service2_state = ServiceState::NotConnected;

	futures::executor::block_on(async move {
		loop {
			// Grab next event from services.
			let event = {
				let s1 = service1.select_next_some();
				let s2 = service2.select_next_some();
				futures::pin_mut!(s1, s2);
				match future::select(s1, s2).await {
					future::Either::Left((ev, _)) => future::Either::Left(ev),
					future::Either::Right((ev, _)) => future::Either::Right(ev),
				}
			};

			match event {
				future::Either::Left(SwarmEvent::Behaviour(
					NotificationsOut::CustomProtocolOpen { .. },
				)) => match service1_state {
					ServiceState::NotConnected => {
						service1_state = ServiceState::FirstConnec;
						if service2_state == ServiceState::FirstConnec {
							service1
								.behaviour_mut()
								.disconnect_peer(Swarm::local_peer_id(&service2), SetId::from(0));
						}
					},
					ServiceState::Disconnected => service1_state = ServiceState::ConnectedAgain,
					ServiceState::FirstConnec | ServiceState::ConnectedAgain => panic!(),
				},
				future::Either::Left(SwarmEvent::Behaviour(
					NotificationsOut::CustomProtocolClosed { .. },
				)) => match service1_state {
					ServiceState::FirstConnec => service1_state = ServiceState::Disconnected,
					ServiceState::ConnectedAgain |
					ServiceState::NotConnected |
					ServiceState::Disconnected => panic!(),
				},
				future::Either::Right(SwarmEvent::Behaviour(
					NotificationsOut::CustomProtocolOpen { .. },
				)) => match service2_state {
					ServiceState::NotConnected => {
						service2_state = ServiceState::FirstConnec;
						if service1_state == ServiceState::FirstConnec {
							service1
								.behaviour_mut()
								.disconnect_peer(Swarm::local_peer_id(&service2), SetId::from(0));
						}
					},
					ServiceState::Disconnected => service2_state = ServiceState::ConnectedAgain,
					ServiceState::FirstConnec | ServiceState::ConnectedAgain => panic!(),
				},
				future::Either::Right(SwarmEvent::Behaviour(
					NotificationsOut::CustomProtocolClosed { .. },
				)) => match service2_state {
					ServiceState::FirstConnec => service2_state = ServiceState::Disconnected,
					ServiceState::ConnectedAgain |
					ServiceState::NotConnected |
					ServiceState::Disconnected => panic!(),
				},
				_ => {},
			}

			// Due to the bug in `Notifications`, the disconnected node does not always detect that
			// it was disconnected. The closed inbound substream is tolerated by design, and the
			// closed outbound substream is not detected until something is sent into it.
			// See [PR #13396](https://github.com/paritytech/substrate/pull/13396).
			// This happens if the disconnecting node reconnects to it fast enough.
			// In this case the disconnected node does not transit via `ServiceState::NotConnected`
			// and stays in `ServiceState::FirstConnec`.
			// TODO: update this once the fix is finally merged.
			if service1_state == ServiceState::ConnectedAgain &&
				service2_state == ServiceState::ConnectedAgain ||
				service1_state == ServiceState::ConnectedAgain &&
					service2_state == ServiceState::FirstConnec ||
				service1_state == ServiceState::FirstConnec &&
					service2_state == ServiceState::ConnectedAgain
			{
				break
			}
		}

		// Now that the two services have disconnected and reconnected, wait for 3 seconds and
		// check whether they're still connected.
		let mut delay = futures_timer::Delay::new(Duration::from_secs(3));

		loop {
			// Grab next event from services.
			let event = {
				let s1 = service1.select_next_some();
				let s2 = service2.select_next_some();
				futures::pin_mut!(s1, s2);
				match future::select(future::select(s1, s2), &mut delay).await {
					future::Either::Right(_) => break, // success
					future::Either::Left((future::Either::Left((ev, _)), _)) => ev,
					future::Either::Left((future::Either::Right((ev, _)), _)) => ev,
				}
			};

			match event {
				SwarmEvent::Behaviour(NotificationsOut::CustomProtocolOpen { .. }) |
				SwarmEvent::Behaviour(NotificationsOut::CustomProtocolClosed { .. }) => panic!(),
				_ => {},
			}
		}
	});
}
