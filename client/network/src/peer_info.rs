// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use crate::utils::interval;
use fnv::FnvHashMap;
use futures::prelude::*;
use libp2p::{
	core::{
		connection::ConnectionId, either::EitherOutput, transport::ListenerId, ConnectedPoint,
		PeerId, PublicKey,
	},
	identify::{Identify, IdentifyConfig, IdentifyEvent, IdentifyInfo},
	ping::{Ping, PingConfig, PingEvent, PingSuccess},
	swarm::{
		ConnectionHandler, IntoConnectionHandler, IntoConnectionHandlerSelect, NetworkBehaviour,
		NetworkBehaviourAction, PollParameters,
	},
	Multiaddr,
};
use log::{debug, error, trace};
use smallvec::SmallVec;
use std::{
	collections::hash_map::Entry,
	error, io,
	pin::Pin,
	task::{Context, Poll},
	time::{Duration, Instant},
};

/// Time after we disconnect from a node before we purge its information from the cache.
const CACHE_EXPIRE: Duration = Duration::from_secs(10 * 60);
/// Interval at which we perform garbage collection on the node info.
const GARBAGE_COLLECT_INTERVAL: Duration = Duration::from_secs(2 * 60);

/// Implementation of `NetworkBehaviour` that holds information about peers in cache.
pub struct PeerInfoBehaviour {
	/// Periodically ping nodes, and close the connection if it's unresponsive.
	ping: Ping,
	/// Periodically identifies the remote and responds to incoming requests.
	identify: Identify,
	/// Information that we know about all nodes.
	nodes_info: FnvHashMap<PeerId, NodeInfo>,
	/// Interval at which we perform garbage collection in `nodes_info`.
	garbage_collect: Pin<Box<dyn Stream<Item = ()> + Send>>,
}

/// Information about a node we're connected to.
#[derive(Debug)]
struct NodeInfo {
	/// When we will remove the entry about this node from the list, or `None` if we're connected
	/// to the node.
	info_expire: Option<Instant>,
	/// Non-empty list of connected endpoints, one per connection.
	endpoints: SmallVec<[ConnectedPoint; crate::MAX_CONNECTIONS_PER_PEER]>,
	/// Version reported by the remote, or `None` if unknown.
	client_version: Option<String>,
	/// Latest ping time with this node.
	latest_ping: Option<Duration>,
}

impl NodeInfo {
	fn new(endpoint: ConnectedPoint) -> Self {
		let mut endpoints = SmallVec::new();
		endpoints.push(endpoint);
		Self { info_expire: None, endpoints, client_version: None, latest_ping: None }
	}
}

impl PeerInfoBehaviour {
	/// Builds a new `PeerInfoBehaviour`.
	pub fn new(user_agent: String, local_public_key: PublicKey) -> Self {
		let identify = {
			let cfg = IdentifyConfig::new("/substrate/1.0".to_string(), local_public_key)
				.with_agent_version(user_agent);
			Identify::new(cfg)
		};

		Self {
			ping: Ping::new(PingConfig::new()),
			identify,
			nodes_info: FnvHashMap::default(),
			garbage_collect: Box::pin(interval(GARBAGE_COLLECT_INTERVAL)),
		}
	}

	/// Borrows `self` and returns a struct giving access to the information about a node.
	///
	/// Returns `None` if we don't know anything about this node. Always returns `Some` for nodes
	/// we're connected to, meaning that if `None` is returned then we're not connected to that
	/// node.
	pub fn node(&self, peer_id: &PeerId) -> Option<Node> {
		self.nodes_info.get(peer_id).map(Node)
	}

	/// Inserts a ping time in the cache. Has no effect if we don't have any entry for that node,
	/// which shouldn't happen.
	fn handle_ping_report(&mut self, peer_id: &PeerId, ping_time: Duration) {
		trace!(target: "sub-libp2p", "Ping time with {:?}: {:?}", peer_id, ping_time);
		if let Some(entry) = self.nodes_info.get_mut(peer_id) {
			entry.latest_ping = Some(ping_time);
		} else {
			error!(target: "sub-libp2p",
				"Received ping from node we're not connected to {:?}", peer_id);
		}
	}

	/// Inserts an identify record in the cache. Has no effect if we don't have any entry for that
	/// node, which shouldn't happen.
	fn handle_identify_report(&mut self, peer_id: &PeerId, info: &IdentifyInfo) {
		trace!(target: "sub-libp2p", "Identified {:?} => {:?}", peer_id, info);
		if let Some(entry) = self.nodes_info.get_mut(peer_id) {
			entry.client_version = Some(info.agent_version.clone());
		} else {
			error!(target: "sub-libp2p",
				"Received pong from node we're not connected to {:?}", peer_id);
		}
	}
}

/// Gives access to the information about a node.
pub struct Node<'a>(&'a NodeInfo);

impl<'a> Node<'a> {
	/// Returns the endpoint of an established connection to the peer.
	///
	/// Returns `None` if we are disconnected from the node.
	pub fn endpoint(&self) -> Option<&'a ConnectedPoint> {
		self.0.endpoints.get(0)
	}

	/// Returns the latest version information we know of.
	pub fn client_version(&self) -> Option<&'a str> {
		self.0.client_version.as_deref()
	}

	/// Returns the latest ping time we know of for this node. `None` if we never successfully
	/// pinged this node.
	pub fn latest_ping(&self) -> Option<Duration> {
		self.0.latest_ping
	}
}

/// Event that can be emitted by the behaviour.
#[derive(Debug)]
pub enum PeerInfoEvent {
	/// We have obtained identity information from a peer, including the addresses it is listening
	/// on.
	Identified {
		/// Id of the peer that has been identified.
		peer_id: PeerId,
		/// Information about the peer.
		info: IdentifyInfo,
	},
}

impl NetworkBehaviour for PeerInfoBehaviour {
	type ConnectionHandler = IntoConnectionHandlerSelect<
		<Ping as NetworkBehaviour>::ConnectionHandler,
		<Identify as NetworkBehaviour>::ConnectionHandler,
	>;
	type OutEvent = PeerInfoEvent;

	fn new_handler(&mut self) -> Self::ConnectionHandler {
		IntoConnectionHandler::select(self.ping.new_handler(), self.identify.new_handler())
	}

	fn addresses_of_peer(&mut self, peer_id: &PeerId) -> Vec<Multiaddr> {
		let mut list = self.ping.addresses_of_peer(peer_id);
		list.extend_from_slice(&self.identify.addresses_of_peer(peer_id));
		list
	}

	fn inject_address_change(
		&mut self,
		peer_id: &PeerId,
		conn: &ConnectionId,
		old: &ConnectedPoint,
		new: &ConnectedPoint,
	) {
		self.ping.inject_address_change(peer_id, conn, old, new);
		self.identify.inject_address_change(peer_id, conn, old, new);

		if let Some(entry) = self.nodes_info.get_mut(peer_id) {
			if let Some(endpoint) = entry.endpoints.iter_mut().find(|e| e == &old) {
				*endpoint = new.clone();
			} else {
				error!(target: "sub-libp2p",
					"Unknown address change for peer {:?} from {:?} to {:?}", peer_id, old, new);
			}
		} else {
			error!(target: "sub-libp2p",
				"Unknown peer {:?} to change address from {:?} to {:?}", peer_id, old, new);
		}
	}

	fn inject_connection_established(
		&mut self,
		peer_id: &PeerId,
		conn: &ConnectionId,
		endpoint: &ConnectedPoint,
		failed_addresses: Option<&Vec<Multiaddr>>,
		other_established: usize,
	) {
		self.ping.inject_connection_established(
			peer_id,
			conn,
			endpoint,
			failed_addresses,
			other_established,
		);
		self.identify.inject_connection_established(
			peer_id,
			conn,
			endpoint,
			failed_addresses,
			other_established,
		);
		match self.nodes_info.entry(*peer_id) {
			Entry::Vacant(e) => {
				e.insert(NodeInfo::new(endpoint.clone()));
			},
			Entry::Occupied(e) => {
				let e = e.into_mut();
				if e.info_expire.as_ref().map(|exp| *exp < Instant::now()).unwrap_or(false) {
					e.client_version = None;
					e.latest_ping = None;
				}
				e.info_expire = None;
				e.endpoints.push(endpoint.clone());
			},
		}
	}

	fn inject_connection_closed(
		&mut self,
		peer_id: &PeerId,
		conn: &ConnectionId,
		endpoint: &ConnectedPoint,
		handler: <Self::ConnectionHandler as IntoConnectionHandler>::Handler,
		remaining_established: usize,
	) {
		let (ping_handler, identity_handler) = handler.into_inner();
		self.identify.inject_connection_closed(
			peer_id,
			conn,
			endpoint,
			identity_handler,
			remaining_established,
		);
		self.ping.inject_connection_closed(
			peer_id,
			conn,
			endpoint,
			ping_handler,
			remaining_established,
		);

		if let Some(entry) = self.nodes_info.get_mut(peer_id) {
			if remaining_established == 0 {
				entry.info_expire = Some(Instant::now() + CACHE_EXPIRE);
			}
			entry.endpoints.retain(|ep| ep != endpoint)
		} else {
			error!(target: "sub-libp2p",
				"Unknown connection to {:?} closed: {:?}", peer_id, endpoint);
		}
	}

	fn inject_event(
		&mut self,
		peer_id: PeerId,
		connection: ConnectionId,
		event: <<Self::ConnectionHandler as IntoConnectionHandler>::Handler as ConnectionHandler>::OutEvent,
	) {
		match event {
			EitherOutput::First(event) => self.ping.inject_event(peer_id, connection, event),
			EitherOutput::Second(event) => self.identify.inject_event(peer_id, connection, event),
		}
	}

	fn inject_dial_failure(
		&mut self,
		peer_id: Option<PeerId>,
		handler: Self::ConnectionHandler,
		error: &libp2p::swarm::DialError,
	) {
		let (ping_handler, identity_handler) = handler.into_inner();
		self.identify.inject_dial_failure(peer_id, identity_handler, error);
		self.ping.inject_dial_failure(peer_id, ping_handler, error);
	}

	fn inject_new_listener(&mut self, id: ListenerId) {
		self.ping.inject_new_listener(id);
		self.identify.inject_new_listener(id);
	}

	fn inject_new_listen_addr(&mut self, id: ListenerId, addr: &Multiaddr) {
		self.ping.inject_new_listen_addr(id, addr);
		self.identify.inject_new_listen_addr(id, addr);
	}

	fn inject_expired_listen_addr(&mut self, id: ListenerId, addr: &Multiaddr) {
		self.ping.inject_expired_listen_addr(id, addr);
		self.identify.inject_expired_listen_addr(id, addr);
	}

	fn inject_new_external_addr(&mut self, addr: &Multiaddr) {
		self.ping.inject_new_external_addr(addr);
		self.identify.inject_new_external_addr(addr);
	}

	fn inject_expired_external_addr(&mut self, addr: &Multiaddr) {
		self.ping.inject_expired_external_addr(addr);
		self.identify.inject_expired_external_addr(addr);
	}

	fn inject_listen_failure(
		&mut self,
		local_addr: &Multiaddr,
		send_back_addr: &Multiaddr,
		handler: Self::ConnectionHandler,
	) {
		let (ping_handler, identity_handler) = handler.into_inner();
		self.identify
			.inject_listen_failure(local_addr, send_back_addr, identity_handler);
		self.ping.inject_listen_failure(local_addr, send_back_addr, ping_handler);
	}

	fn inject_listener_error(&mut self, id: ListenerId, err: &(dyn error::Error + 'static)) {
		self.ping.inject_listener_error(id, err);
		self.identify.inject_listener_error(id, err);
	}

	fn inject_listener_closed(&mut self, id: ListenerId, reason: Result<(), &io::Error>) {
		self.ping.inject_listener_closed(id, reason);
		self.identify.inject_listener_closed(id, reason);
	}

	fn poll(
		&mut self,
		cx: &mut Context,
		params: &mut impl PollParameters,
	) -> Poll<NetworkBehaviourAction<Self::OutEvent, Self::ConnectionHandler>> {
		loop {
			match self.ping.poll(cx, params) {
				Poll::Pending => break,
				Poll::Ready(NetworkBehaviourAction::GenerateEvent(ev)) => {
					if let PingEvent { peer, result: Ok(PingSuccess::Ping { rtt }) } = ev {
						self.handle_ping_report(&peer, rtt)
					}
				},
				Poll::Ready(NetworkBehaviourAction::Dial { opts, handler }) => {
					let handler =
						IntoConnectionHandler::select(handler, self.identify.new_handler());
					return Poll::Ready(NetworkBehaviourAction::Dial { opts, handler })
				},
				Poll::Ready(NetworkBehaviourAction::NotifyHandler { peer_id, handler, event }) =>
					return Poll::Ready(NetworkBehaviourAction::NotifyHandler {
						peer_id,
						handler,
						event: EitherOutput::First(event),
					}),
				Poll::Ready(NetworkBehaviourAction::ReportObservedAddr { address, score }) =>
					return Poll::Ready(NetworkBehaviourAction::ReportObservedAddr {
						address,
						score,
					}),
				Poll::Ready(NetworkBehaviourAction::CloseConnection { peer_id, connection }) =>
					return Poll::Ready(NetworkBehaviourAction::CloseConnection {
						peer_id,
						connection,
					}),
			}
		}

		loop {
			match self.identify.poll(cx, params) {
				Poll::Pending => break,
				Poll::Ready(NetworkBehaviourAction::GenerateEvent(event)) => match event {
					IdentifyEvent::Received { peer_id, info, .. } => {
						self.handle_identify_report(&peer_id, &info);
						let event = PeerInfoEvent::Identified { peer_id, info };
						return Poll::Ready(NetworkBehaviourAction::GenerateEvent(event))
					},
					IdentifyEvent::Error { peer_id, error } => {
						debug!(target: "sub-libp2p", "Identification with peer {:?} failed => {}", peer_id, error)
					},
					IdentifyEvent::Pushed { .. } => {},
					IdentifyEvent::Sent { .. } => {},
				},
				Poll::Ready(NetworkBehaviourAction::Dial { opts, handler }) => {
					let handler = IntoConnectionHandler::select(self.ping.new_handler(), handler);
					return Poll::Ready(NetworkBehaviourAction::Dial { opts, handler })
				},
				Poll::Ready(NetworkBehaviourAction::NotifyHandler { peer_id, handler, event }) =>
					return Poll::Ready(NetworkBehaviourAction::NotifyHandler {
						peer_id,
						handler,
						event: EitherOutput::Second(event),
					}),
				Poll::Ready(NetworkBehaviourAction::ReportObservedAddr { address, score }) =>
					return Poll::Ready(NetworkBehaviourAction::ReportObservedAddr {
						address,
						score,
					}),
				Poll::Ready(NetworkBehaviourAction::CloseConnection { peer_id, connection }) =>
					return Poll::Ready(NetworkBehaviourAction::CloseConnection {
						peer_id,
						connection,
					}),
			}
		}

		while let Poll::Ready(Some(())) = self.garbage_collect.poll_next_unpin(cx) {
			self.nodes_info.retain(|_, node| {
				node.info_expire.as_ref().map(|exp| *exp >= Instant::now()).unwrap_or(true)
			});
		}

		Poll::Pending
	}
}
