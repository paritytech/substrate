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

use crate::{
	debug_info, discovery::DiscoveryBehaviour, discovery::DiscoveryOut, DiscoveryNetBehaviour,
	protocol::event::DhtEvent
};
use crate::{ExHashT, specialization::NetworkSpecialization};
use crate::protocol::{CustomMessageOutcome, Protocol};
use futures::prelude::*;
use libp2p::NetworkBehaviour;
use libp2p::core::{Multiaddr, PeerId, PublicKey};
use libp2p::kad::record;
use libp2p::swarm::{NetworkBehaviourAction, NetworkBehaviourEventProcess};
use libp2p::core::{nodes::Substream, muxing::StreamMuxerBox};
use log::{debug, warn};
use sp_runtime::traits::Block as BlockT;
use std::{iter, task::{Context, Poll}};
use void;

/// General behaviour of the network. Combines all protocols together.
#[derive(NetworkBehaviour)]
#[behaviour(out_event = "BehaviourOut<B>", poll_method = "poll")]
pub struct Behaviour<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> {
	/// All the substrate-specific protocols.
	substrate: Protocol<B, S, H>,
	/// Periodically pings and identifies the nodes we are connected to, and store information in a
	/// cache.
	debug_info: debug_info::DebugInfoBehaviour<Substream<StreamMuxerBox>>,
	/// Discovers nodes of the network.
	discovery: DiscoveryBehaviour<Substream<StreamMuxerBox>>,

	/// Queue of events to produce for the outside.
	#[behaviour(ignore)]
	events: Vec<BehaviourOut<B>>,
}

/// Event generated by `Behaviour`.
pub enum BehaviourOut<B: BlockT> {
	SubstrateAction(CustomMessageOutcome<B>),
	Dht(DhtEvent),
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> Behaviour<B, S, H> {
	/// Builds a new `Behaviour`.
	pub fn new(
		substrate: Protocol<B, S, H>,
		user_agent: String,
		local_public_key: PublicKey,
		known_addresses: Vec<(PeerId, Multiaddr)>,
		enable_mdns: bool,
		allow_private_ipv4: bool,
	) -> Self {
		Behaviour {
			substrate,
			debug_info: debug_info::DebugInfoBehaviour::new(user_agent, local_public_key.clone()),
			discovery: DiscoveryBehaviour::new(
				local_public_key,
				known_addresses,
				enable_mdns,
				allow_private_ipv4
			),
			events: Vec::new(),
		}
	}

	/// Returns the list of nodes that we know exist in the network.
	pub fn known_peers(&mut self) -> impl Iterator<Item = &PeerId> {
		self.discovery.known_peers()
	}

	/// Adds a hard-coded address for the given peer, that never expires.
	pub fn add_known_address(&mut self, peer_id: PeerId, addr: Multiaddr) {
		self.discovery.add_known_address(peer_id, addr)
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
	pub fn user_protocol(&self) -> &Protocol<B, S, H> {
		&self.substrate
	}

	/// Returns a mutable reference to the user protocol.
	pub fn user_protocol_mut(&mut self) -> &mut Protocol<B, S, H> {
		&mut self.substrate
	}

	/// Start querying a record from the DHT. Will later produce either a `ValueFound` or a `ValueNotFound` event.
	pub fn get_value(&mut self, key: &record::Key) {
		self.discovery.get_value(key);
	}

	/// Starts putting a record into DHT. Will later produce either a `ValuePut` or a `ValuePutFailed` event.
	pub fn put_value(&mut self, key: record::Key, value: Vec<u8>) {
		self.discovery.put_value(key, value);
	}
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> NetworkBehaviourEventProcess<void::Void> for
Behaviour<B, S, H> {
	fn inject_event(&mut self, event: void::Void) {
		void::unreachable(event)
	}
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> NetworkBehaviourEventProcess<CustomMessageOutcome<B>> for
Behaviour<B, S, H> {
	fn inject_event(&mut self, event: CustomMessageOutcome<B>) {
		self.events.push(BehaviourOut::SubstrateAction(event));
	}
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> NetworkBehaviourEventProcess<debug_info::DebugInfoEvent>
	for Behaviour<B, S, H> {
	fn inject_event(&mut self, event: debug_info::DebugInfoEvent) {
		let debug_info::DebugInfoEvent::Identified { peer_id, mut info } = event;
		if !info.protocol_version.contains("substrate") {
			warn!(target: "sub-libp2p", "Connected to a non-Substrate node: {:?}", info);
		}
		if info.listen_addrs.len() > 30 {
			debug!(target: "sub-libp2p", "Node {:?} has reported more than 30 addresses; \
				it is identified by {:?} and {:?}", peer_id, info.protocol_version,
				info.agent_version
			);
			info.listen_addrs.truncate(30);
		}
		for addr in &info.listen_addrs {
			self.discovery.add_self_reported_address(&peer_id, addr.clone());
		}
		self.substrate.add_discovered_nodes(iter::once(peer_id.clone()));
	}
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> NetworkBehaviourEventProcess<DiscoveryOut>
	for Behaviour<B, S, H> {
	fn inject_event(&mut self, out: DiscoveryOut) {
		match out {
			DiscoveryOut::UnroutablePeer(_peer_id) => {
				// Obtaining and reporting listen addresses for unroutable peers back
				// to Kademlia is handled by the `Identify` protocol, part of the
				// `DebugInfoBehaviour`. See the `NetworkBehaviourEventProcess`
				// implementation for `DebugInfoEvent`.
			}
			DiscoveryOut::Discovered(peer_id) => {
				self.substrate.add_discovered_nodes(iter::once(peer_id));
			}
			DiscoveryOut::ValueFound(results) => {
				self.events.push(BehaviourOut::Dht(DhtEvent::ValueFound(results)));
			}
			DiscoveryOut::ValueNotFound(key) => {
				self.events.push(BehaviourOut::Dht(DhtEvent::ValueNotFound(key)));
			}
			DiscoveryOut::ValuePut(key) => {
				self.events.push(BehaviourOut::Dht(DhtEvent::ValuePut(key)));
			}
			DiscoveryOut::ValuePutFailed(key) => {
				self.events.push(BehaviourOut::Dht(DhtEvent::ValuePutFailed(key)));
			}
		}
	}
}

impl<B: BlockT, S: NetworkSpecialization<B>, H: ExHashT> Behaviour<B, S, H> {
	fn poll<TEv>(&mut self) -> Poll<NetworkBehaviourAction<TEv, BehaviourOut<B>>> {
		if !self.events.is_empty() {
			return Poll::Ready(NetworkBehaviourAction::GenerateEvent(self.events.remove(0)))
		}

		Poll::Pending
	}
}
