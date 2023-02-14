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

use fnv::FnvHashMap;
use futures::prelude::*;
use libp2p::{
	core::{connection::ConnectionId, either::EitherOutput, ConnectedPoint, PeerId, PublicKey},
	identify::{
		Behaviour as Identify, Config as IdentifyConfig, Event as IdentifyEvent,
		Info as IdentifyInfo,
	},
	ping::{Behaviour as Ping, Config as PingConfig, Event as PingEvent, Success as PingSuccess},
	swarm::{
		behaviour::{
			AddressChange, ConnectionClosed, ConnectionEstablished, DialFailure, FromSwarm,
			ListenFailure,
		},
		ConnectionHandler, IntoConnectionHandler, IntoConnectionHandlerSelect, NetworkBehaviour,
		NetworkBehaviourAction, PollParameters,
	},
	Multiaddr,
};
use log::{debug, error, trace};
use sc_network_common::utils::interval;
use smallvec::SmallVec;
use std::{
	collections::hash_map::Entry,
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
				.with_agent_version(user_agent)
				// We don't need any peer information cached.
				.with_cache_size(0);
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

	fn addresses_of_peer(&mut self, _: &PeerId) -> Vec<Multiaddr> {
		// Only `Discovery::addresses_of_peer` must be returning addresses to ensure that we
		// don't return unwanted addresses.
		Vec::new()
	}

	fn on_swarm_event(&mut self, event: FromSwarm<Self::ConnectionHandler>) {
		match event {
			FromSwarm::ConnectionEstablished(
				e @ ConnectionEstablished { peer_id, endpoint, .. },
			) => {
				self.ping.on_swarm_event(FromSwarm::ConnectionEstablished(e));
				self.identify.on_swarm_event(FromSwarm::ConnectionEstablished(e));

				match self.nodes_info.entry(peer_id) {
					Entry::Vacant(e) => {
						e.insert(NodeInfo::new(endpoint.clone()));
					},
					Entry::Occupied(e) => {
						let e = e.into_mut();
						if e.info_expire.as_ref().map(|exp| *exp < Instant::now()).unwrap_or(false)
						{
							e.client_version = None;
							e.latest_ping = None;
						}
						e.info_expire = None;
						e.endpoints.push(endpoint.clone());
					},
				}
			},
			FromSwarm::ConnectionClosed(ConnectionClosed {
				peer_id,
				connection_id,
				endpoint,
				handler,
				remaining_established,
			}) => {
				let (ping_handler, identity_handler) = handler.into_inner();
				self.ping.on_swarm_event(FromSwarm::ConnectionClosed(ConnectionClosed {
					peer_id,
					connection_id,
					endpoint,
					handler: ping_handler,
					remaining_established,
				}));
				self.identify.on_swarm_event(FromSwarm::ConnectionClosed(ConnectionClosed {
					peer_id,
					connection_id,
					endpoint,
					handler: identity_handler,
					remaining_established,
				}));

				if let Some(entry) = self.nodes_info.get_mut(&peer_id) {
					if remaining_established == 0 {
						entry.info_expire = Some(Instant::now() + CACHE_EXPIRE);
					}
					entry.endpoints.retain(|ep| ep != endpoint)
				} else {
					error!(target: "sub-libp2p",
						"Unknown connection to {:?} closed: {:?}", peer_id, endpoint);
				}
			},
			FromSwarm::DialFailure(DialFailure { peer_id, handler, error }) => {
				let (ping_handler, identity_handler) = handler.into_inner();
				self.ping.on_swarm_event(FromSwarm::DialFailure(DialFailure {
					peer_id,
					handler: ping_handler,
					error,
				}));
				self.identify.on_swarm_event(FromSwarm::DialFailure(DialFailure {
					peer_id,
					handler: identity_handler,
					error,
				}));
			},
			FromSwarm::ListenerClosed(e) => {
				self.ping.on_swarm_event(FromSwarm::ListenerClosed(e));
				self.identify.on_swarm_event(FromSwarm::ListenerClosed(e));
			},
			FromSwarm::ListenFailure(ListenFailure { local_addr, send_back_addr, handler }) => {
				let (ping_handler, identity_handler) = handler.into_inner();
				self.ping.on_swarm_event(FromSwarm::ListenFailure(ListenFailure {
					local_addr,
					send_back_addr,
					handler: ping_handler,
				}));
				self.identify.on_swarm_event(FromSwarm::ListenFailure(ListenFailure {
					local_addr,
					send_back_addr,
					handler: identity_handler,
				}));
			},
			FromSwarm::ListenerError(e) => {
				self.ping.on_swarm_event(FromSwarm::ListenerError(e));
				self.identify.on_swarm_event(FromSwarm::ListenerError(e));
			},
			FromSwarm::ExpiredExternalAddr(e) => {
				self.ping.on_swarm_event(FromSwarm::ExpiredExternalAddr(e));
				self.identify.on_swarm_event(FromSwarm::ExpiredExternalAddr(e));
			},
			FromSwarm::NewListener(e) => {
				self.ping.on_swarm_event(FromSwarm::NewListener(e));
				self.identify.on_swarm_event(FromSwarm::NewListener(e));
			},
			FromSwarm::ExpiredListenAddr(e) => {
				self.ping.on_swarm_event(FromSwarm::ExpiredListenAddr(e));
				self.identify.on_swarm_event(FromSwarm::ExpiredListenAddr(e));
			},
			FromSwarm::NewExternalAddr(e) => {
				self.ping.on_swarm_event(FromSwarm::NewExternalAddr(e));
				self.identify.on_swarm_event(FromSwarm::NewExternalAddr(e));
			},
			FromSwarm::AddressChange(e @ AddressChange { peer_id, old, new, .. }) => {
				self.ping.on_swarm_event(FromSwarm::AddressChange(e));
				self.identify.on_swarm_event(FromSwarm::AddressChange(e));

				if let Some(entry) = self.nodes_info.get_mut(&peer_id) {
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
			},
			FromSwarm::NewListenAddr(e) => {
				self.ping.on_swarm_event(FromSwarm::NewListenAddr(e));
				self.identify.on_swarm_event(FromSwarm::NewListenAddr(e));
			},
		}
	}

	fn on_connection_handler_event(
		&mut self,
		peer_id: PeerId,
		connection_id: ConnectionId,
		event: <<Self::ConnectionHandler as IntoConnectionHandler>::Handler as
		ConnectionHandler>::OutEvent,
	) {
		match event {
			EitherOutput::First(event) =>
				self.ping.on_connection_handler_event(peer_id, connection_id, event),
			EitherOutput::Second(event) =>
				self.identify.on_connection_handler_event(peer_id, connection_id, event),
		}
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
