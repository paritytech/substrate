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

use crate::DiscoveryNetBehaviour;
use futures::prelude::*;
use libp2p::NetworkBehaviour;
use libp2p::core::{Multiaddr, PeerId, ProtocolsHandler, protocols_handler::IntoProtocolsHandler, PublicKey};
use libp2p::core::swarm::{ConnectedPoint, NetworkBehaviour, NetworkBehaviourAction};
use libp2p::core::swarm::{NetworkBehaviourEventProcess, PollParameters};
#[cfg(not(target_os = "unknown"))]
use libp2p::core::swarm::toggle::Toggle;
use libp2p::kad::{Kademlia, KademliaOut};
#[cfg(not(target_os = "unknown"))]
use libp2p::mdns::{Mdns, MdnsEvent};
use libp2p::multiaddr::Protocol;
use log::{debug, info, trace, warn};
use std::{cmp, iter, time::Duration};
use tokio_io::{AsyncRead, AsyncWrite};
use tokio_timer::{Delay, clock::Clock};
use void;

mod debug_info;

/// General behaviour of the network.
#[derive(NetworkBehaviour)]
#[behaviour(out_event = "TBehaviourEv", poll_method = "poll")]
pub struct Behaviour<TBehaviour, TBehaviourEv, TSubstream> {
	/// Main protocol that handles everything except the discovery and the technicalities.
	user_protocol: UserBehaviourWrap<TBehaviour>,
	/// Periodically pings and identifies the nodes we are connected to, and store information in a
	/// cache.
	debug_info: debug_info::DebugInfoBehaviour<TSubstream>,
	/// Discovers nodes of the network. Defined below.
	discovery: DiscoveryBehaviour<TSubstream>,
	/// Discovers nodes on the local network.
	#[cfg(not(target_os = "unknown"))]
	mdns: Toggle<Mdns<TSubstream>>,

	/// Queue of events to produce for the outside.
	#[behaviour(ignore)]
	events: Vec<TBehaviourEv>,
}

impl<TBehaviour, TBehaviourEv, TSubstream> Behaviour<TBehaviour, TBehaviourEv, TSubstream> {
	/// Builds a new `Behaviour`.
	pub fn new(
		user_protocol: TBehaviour,
		user_agent: String,
		local_public_key: PublicKey,
		known_addresses: Vec<(PeerId, Multiaddr)>,
		enable_mdns: bool,
	) -> Self {
		let debug_info = debug_info::DebugInfoBehaviour::new(user_agent, local_public_key.clone());

		let mut kademlia = Kademlia::new(local_public_key.clone().into_peer_id());
		for (peer_id, addr) in &known_addresses {
			kademlia.add_connected_address(peer_id, addr.clone());
		}

		if enable_mdns {
			#[cfg(target_os = "unknown")]
			warn!(target: "sub-libp2p", "mDNS is not available on this platform");
		}

		let clock = Clock::new();
		Behaviour {
			user_protocol: UserBehaviourWrap(user_protocol),
			debug_info,
			discovery: DiscoveryBehaviour {
				user_defined: known_addresses,
				kademlia,
				next_kad_random_query: Delay::new(clock.now()),
				duration_to_next_kad: Duration::from_secs(1),
				clock,
				local_peer_id: local_public_key.into_peer_id(),
			},
			#[cfg(not(target_os = "unknown"))]
			mdns: if enable_mdns {
				match Mdns::new() {
					Ok(mdns) => Some(mdns).into(),
					Err(err) => {
						warn!(target: "sub-libp2p", "Failed to initialize mDNS: {:?}", err);
						None.into()
					}
				}
			} else {
				None.into()
			},
			events: Vec::new(),
		}
	}

	/// Returns the list of nodes that we know exist in the network.
	pub fn known_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.discovery.kademlia.kbuckets_entries()
	}

	/// Adds a hard-coded address for the given peer, that never expires.
	pub fn add_known_address(&mut self, peer_id: PeerId, addr: Multiaddr) {
		if self.discovery.user_defined.iter().all(|(p, a)| *p != peer_id && *a != addr) {
			self.discovery.user_defined.push((peer_id, addr));
		}
	}

	/// Borrows `self` and returns a struct giving access to the information about a node.
	///
	/// Returns `None` if we don't know anything about this node. Always returns `Some` for nodes
	/// we're connected to, meaning that if `None` is returned then we're not connected to that
	/// node.
	pub fn node(&self, peer_id: &PeerId) -> Option<debug_info::Node> {
		self.debug_info.node(peer_id)
	}

	/// Returns a shared reference to the user protocol.
	pub fn user_protocol(&self) -> &TBehaviour {
		&self.user_protocol.0
	}

	/// Returns a mutable reference to the user protocol.
	pub fn user_protocol_mut(&mut self) -> &mut TBehaviour {
		&mut self.user_protocol.0
	}
}

impl<TBehaviour, TBehaviourEv, TSubstream> NetworkBehaviourEventProcess<void::Void> for
Behaviour<TBehaviour, TBehaviourEv, TSubstream> {
	fn inject_event(&mut self, event: void::Void) {
		void::unreachable(event)
	}
}

impl<TBehaviour, TBehaviourEv, TSubstream> NetworkBehaviourEventProcess<UserEventWrap<TBehaviourEv>> for
Behaviour<TBehaviour, TBehaviourEv, TSubstream> {
	fn inject_event(&mut self, event: UserEventWrap<TBehaviourEv>) {
		self.events.push(event.0);
	}
}

impl<TBehaviour, TBehaviourEv, TSubstream> NetworkBehaviourEventProcess<debug_info::DebugInfoEvent>
	for Behaviour<TBehaviour, TBehaviourEv, TSubstream>
	where TBehaviour: DiscoveryNetBehaviour {
	fn inject_event(&mut self, event: debug_info::DebugInfoEvent) {
		let debug_info::DebugInfoEvent::Identified { peer_id, mut info } = event;
		if !info.protocol_version.contains("substrate") {
			warn!(target: "sub-libp2p", "Connected to a non-Substrate node: {:?}", info);
		}
		if info.listen_addrs.len() > 30 {
			warn!(target: "sub-libp2p", "Node {:?} has reported more than 30 addresses; \
				it is identified by {:?} and {:?}", peer_id, info.protocol_version,
				info.agent_version
			);
			info.listen_addrs.truncate(30);
		}
		for addr in &info.listen_addrs {
			self.discovery.kademlia.add_connected_address(&peer_id, addr.clone());
		}
		self.user_protocol.0.add_discovered_nodes(iter::once(peer_id.clone()));
	}
}

impl<TBehaviour, TBehaviourEv, TSubstream> NetworkBehaviourEventProcess<KademliaOut>
	for Behaviour<TBehaviour, TBehaviourEv, TSubstream>
	where TBehaviour: DiscoveryNetBehaviour {
	fn inject_event(&mut self, out: KademliaOut) {
		match out {
			KademliaOut::Discovered { .. } => {}
			KademliaOut::KBucketAdded { peer_id, .. } => {
				self.user_protocol.0.add_discovered_nodes(iter::once(peer_id));
			}
			KademliaOut::FindNodeResult { key, closer_peers } => {
				trace!(target: "sub-libp2p", "Libp2p => Query for {:?} yielded {:?} results",
					key, closer_peers.len());
				if closer_peers.is_empty() {
					warn!(target: "sub-libp2p", "Libp2p => Random Kademlia query has yielded empty \
						results");
				}
			}
			// We never start any GET_PROVIDERS query.
			KademliaOut::GetProvidersResult { .. } => ()
		}
	}
}

#[cfg(not(target_os = "unknown"))]
impl<TBehaviour, TBehaviourEv, TSubstream> NetworkBehaviourEventProcess<MdnsEvent> for
	Behaviour<TBehaviour, TBehaviourEv, TSubstream>
	where TBehaviour: DiscoveryNetBehaviour {
	fn inject_event(&mut self, event: MdnsEvent) {
		match event {
			MdnsEvent::Discovered(list) => {
				self.user_protocol.0.add_discovered_nodes(list.into_iter().map(|(peer_id, _)| peer_id));
			},
			MdnsEvent::Expired(_) => {}
		}
	}
}

impl<TBehaviour, TBehaviourEv, TSubstream> Behaviour<TBehaviour, TBehaviourEv, TSubstream> {
	fn poll<TEv>(&mut self) -> Async<NetworkBehaviourAction<TEv, TBehaviourEv>> {
		if !self.events.is_empty() {
			return Async::Ready(NetworkBehaviourAction::GenerateEvent(self.events.remove(0)))
		}

		Async::NotReady
	}
}

/// Because of limitations with the network behaviour custom derive and trait impl duplication, we
/// have to wrap the user protocol into a struct.
pub struct UserBehaviourWrap<TInner>(TInner);
/// Event produced by `UserBehaviourWrap`.
pub struct UserEventWrap<TInner>(TInner);
impl<TInner: NetworkBehaviour> NetworkBehaviour for UserBehaviourWrap<TInner> {
	type ProtocolsHandler = TInner::ProtocolsHandler;
	type OutEvent = UserEventWrap<TInner::OutEvent>;
	fn new_handler(&mut self) -> Self::ProtocolsHandler { self.0.new_handler() }
	fn addresses_of_peer(&mut self, peer_id: &PeerId) -> Vec<Multiaddr> {
		self.0.addresses_of_peer(peer_id)
	}
	fn inject_connected(&mut self, peer_id: PeerId, endpoint: ConnectedPoint) {
		self.0.inject_connected(peer_id, endpoint)
	}
	fn inject_disconnected(&mut self, peer_id: &PeerId, endpoint: ConnectedPoint) {
		self.0.inject_disconnected(peer_id, endpoint)
	}
	fn inject_node_event(
		&mut self,
		peer_id: PeerId,
		event: <<Self::ProtocolsHandler as IntoProtocolsHandler>::Handler as ProtocolsHandler>::OutEvent
	) {
		self.0.inject_node_event(peer_id, event)
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
		match self.0.poll(params) {
			Async::NotReady => Async::NotReady,
			Async::Ready(NetworkBehaviourAction::GenerateEvent(ev)) =>
				Async::Ready(NetworkBehaviourAction::GenerateEvent(UserEventWrap(ev))),
			Async::Ready(NetworkBehaviourAction::DialAddress { address }) =>
				Async::Ready(NetworkBehaviourAction::DialAddress { address }),
			Async::Ready(NetworkBehaviourAction::DialPeer { peer_id }) =>
				Async::Ready(NetworkBehaviourAction::DialPeer { peer_id }),
			Async::Ready(NetworkBehaviourAction::SendEvent { peer_id, event }) =>
				Async::Ready(NetworkBehaviourAction::SendEvent { peer_id, event }),
			Async::Ready(NetworkBehaviourAction::ReportObservedAddr { address }) =>
				Async::Ready(NetworkBehaviourAction::ReportObservedAddr { address }),
		}
	}
	fn inject_replaced(&mut self, peer_id: PeerId, closed_endpoint: ConnectedPoint, new_endpoint: ConnectedPoint) {
		self.0.inject_replaced(peer_id, closed_endpoint, new_endpoint)
	}
	fn inject_addr_reach_failure(&mut self, peer_id: Option<&PeerId>, addr: &Multiaddr, error: &dyn std::error::Error) {
		self.0.inject_addr_reach_failure(peer_id, addr, error)
	}
	fn inject_dial_failure(&mut self, peer_id: &PeerId) {
		self.0.inject_dial_failure(peer_id)
	}
	fn inject_new_listen_addr(&mut self, addr: &Multiaddr) {
		self.0.inject_new_listen_addr(addr)
	}
	fn inject_expired_listen_addr(&mut self, addr: &Multiaddr) {
		self.0.inject_expired_listen_addr(addr)
	}
	fn inject_new_external_addr(&mut self, addr: &Multiaddr) {
		self.0.inject_new_external_addr(addr)
	}
}

/// Implementation of `NetworkBehaviour` that discovers the nodes on the network.
pub struct DiscoveryBehaviour<TSubstream> {
	/// User-defined list of nodes and their addresses. Typically includes bootstrap nodes and
	/// reserved nodes.
	user_defined: Vec<(PeerId, Multiaddr)>,
	/// Kademlia requests and answers.
	kademlia: Kademlia<TSubstream>,
	/// Stream that fires when we need to perform the next random Kademlia query.
	next_kad_random_query: Delay,
	/// After `next_kad_random_query` triggers, the next one triggers after this duration.
	duration_to_next_kad: Duration,
	/// `Clock` instance that uses the current execution context's source of time.
	clock: Clock,
	/// Identity of our local node.
	local_peer_id: PeerId,
}

impl<TSubstream> NetworkBehaviour for DiscoveryBehaviour<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	type ProtocolsHandler = <Kademlia<TSubstream> as NetworkBehaviour>::ProtocolsHandler;
	type OutEvent = <Kademlia<TSubstream> as NetworkBehaviour>::OutEvent;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		NetworkBehaviour::new_handler(&mut self.kademlia)
	}

	fn addresses_of_peer(&mut self, peer_id: &PeerId) -> Vec<Multiaddr> {
		let mut list = self.user_defined.iter()
			.filter_map(|(p, a)| if p == peer_id { Some(a.clone()) } else { None })
			.collect::<Vec<_>>();
		list.extend(self.kademlia.addresses_of_peer(peer_id));
		trace!(target: "sub-libp2p", "Addresses of {:?} are {:?}", peer_id, list);
		if list.is_empty() {
			if self.kademlia.kbuckets_entries().any(|p| p == peer_id) {
				debug!(target: "sub-libp2p", "Requested dialing to {:?} (peer in k-buckets), \
					and no address was found", peer_id);
			} else {
				debug!(target: "sub-libp2p", "Requested dialing to {:?} (peer not in k-buckets), \
					and no address was found", peer_id);
			}
		}
		list
	}

	fn inject_connected(&mut self, peer_id: PeerId, endpoint: ConnectedPoint) {
		NetworkBehaviour::inject_connected(&mut self.kademlia, peer_id, endpoint)
	}

	fn inject_disconnected(&mut self, peer_id: &PeerId, endpoint: ConnectedPoint) {
		NetworkBehaviour::inject_disconnected(&mut self.kademlia, peer_id, endpoint)
	}

	fn inject_replaced(&mut self, peer_id: PeerId, closed: ConnectedPoint, opened: ConnectedPoint) {
		NetworkBehaviour::inject_replaced(&mut self.kademlia, peer_id, closed, opened)
	}

	fn inject_node_event(
		&mut self,
		peer_id: PeerId,
		event: <Self::ProtocolsHandler as ProtocolsHandler>::OutEvent,
	) {
		NetworkBehaviour::inject_node_event(&mut self.kademlia, peer_id, event)
	}

	fn inject_new_external_addr(&mut self, addr: &Multiaddr) {
		let new_addr = addr.clone()
			.with(Protocol::P2p(self.local_peer_id.clone().into()));
		info!(target: "sub-libp2p", "Discovered new external address for our node: {}", new_addr);
	}

	fn inject_expired_listen_addr(&mut self, addr: &Multiaddr) {
		info!(target: "sub-libp2p", "No longer listening on {}", addr);
	}

	fn poll(
		&mut self,
		params: &mut PollParameters,
	) -> Async<
		NetworkBehaviourAction<
			<Self::ProtocolsHandler as ProtocolsHandler>::InEvent,
			Self::OutEvent,
		>,
	> {
		// Poll Kademlia.
		match self.kademlia.poll(params) {
			Async::Ready(action) => return Async::Ready(action),
			Async::NotReady => (),
		}

		// Poll the stream that fires when we need to start a random Kademlia query.
		loop {
			match self.next_kad_random_query.poll() {
				Ok(Async::NotReady) => break,
				Ok(Async::Ready(_)) => {
					let random_peer_id = PeerId::random();
					debug!(target: "sub-libp2p", "Libp2p <= Starting random Kademlia request for \
						{:?}", random_peer_id);
					self.kademlia.find_node(random_peer_id);

					// Reset the `Delay` to the next random.
					self.next_kad_random_query.reset(self.clock.now() + self.duration_to_next_kad);
					self.duration_to_next_kad = cmp::min(self.duration_to_next_kad * 2,
						Duration::from_secs(60));
				},
				Err(err) => {
					warn!(target: "sub-libp2p", "Kademlia query timer errored: {:?}", err);
					break
				}
			}
		}

		Async::NotReady
	}
}
