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

use crate::custom_proto::{CustomProto, CustomProtoOut, RegisteredProtocol};
use futures::prelude::*;
use libp2p::NetworkBehaviour;
use libp2p::core::{Multiaddr, PeerId, ProtocolsHandler, PublicKey};
use libp2p::core::swarm::{ConnectedPoint, NetworkBehaviour, NetworkBehaviourAction};
use libp2p::core::swarm::{NetworkBehaviourEventProcess, PollParameters};
#[cfg(not(target_os = "unknown"))]
use libp2p::core::swarm::toggle::Toggle;
use libp2p::identify::{Identify, IdentifyEvent, protocol::IdentifyInfo};
use libp2p::kad::{Kademlia, KademliaOut};
#[cfg(not(target_os = "unknown"))]
use libp2p::mdns::{Mdns, MdnsEvent};
use libp2p::multiaddr::Protocol;
use libp2p::ping::{Ping, PingConfig, PingEvent, PingSuccess};
use log::{debug, info, trace, warn};
use std::{borrow::Cow, cmp, time::Duration};
use tokio_io::{AsyncRead, AsyncWrite};
use tokio_timer::{Delay, clock::Clock};
use void;

/// General behaviour of the network.
#[derive(NetworkBehaviour)]
#[behaviour(out_event = "BehaviourOut<TMessage>", poll_method = "poll")]
pub struct Behaviour<TMessage, TSubstream> {
	/// Periodically ping nodes, and close the connection if it's unresponsive.
	ping: Ping<TSubstream>,
	/// Custom protocols (dot, bbq, sub, etc.).
	custom_protocols: CustomProto<TMessage, TSubstream>,
	/// Discovers nodes of the network. Defined below.
	discovery: DiscoveryBehaviour<TSubstream>,
	/// Periodically identifies the remote and responds to incoming requests.
	identify: Identify<TSubstream>,
	/// Discovers nodes on the local network.
	#[cfg(not(target_os = "unknown"))]
	mdns: Toggle<Mdns<TSubstream>>,

	/// Queue of events to produce for the outside.
	#[behaviour(ignore)]
	events: Vec<BehaviourOut<TMessage>>,
}

impl<TMessage, TSubstream> Behaviour<TMessage, TSubstream> {
	/// Builds a new `Behaviour`.
	pub fn new(
		user_agent: String,
		local_public_key: PublicKey,
		protocol: RegisteredProtocol<TMessage>,
		known_addresses: Vec<(PeerId, Multiaddr)>,
		peerset: substrate_peerset::Peerset,
		enable_mdns: bool,
	) -> Self {
		let identify = {
			let proto_version = "/substrate/1.0".to_string();
			Identify::new(proto_version, user_agent, local_public_key.clone())
		};

		let custom_protocols = CustomProto::new(protocol, peerset);

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
			ping: Ping::new(PingConfig::new()),
			custom_protocols,
			discovery: DiscoveryBehaviour {
				user_defined: known_addresses,
				kademlia,
				next_kad_random_query: Delay::new(clock.now()),
				duration_to_next_kad: Duration::from_secs(1),
				clock,
				local_peer_id: local_public_key.into_peer_id(),
			},
			identify,
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

	/// Sends a message to a peer.
	///
	/// Has no effect if the custom protocol is not open with the given peer.
	///
	/// Also note that even we have a valid open substream, it may in fact be already closed
	/// without us knowing, in which case the packet will not be received.
	#[inline]
	pub fn send_custom_message(&mut self, target: &PeerId, data: TMessage) {
		self.custom_protocols.send_packet(target, data)
	}

	/// Returns the list of nodes that we know exist in the network.
	pub fn known_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.discovery.kademlia.kbuckets_entries()
	}

	/// Returns true if we try to open protocols with the given peer.
	pub fn is_enabled(&self, peer_id: &PeerId) -> bool {
		self.custom_protocols.is_enabled(peer_id)
	}

	/// Returns true if we have an open protocol with the given peer.
	pub fn is_open(&self, peer_id: &PeerId) -> bool {
		self.custom_protocols.is_open(peer_id)
	}

	/// Adds a hard-coded address for the given peer, that never expires.
	pub fn add_known_address(&mut self, peer_id: PeerId, addr: Multiaddr) {
		if self.discovery.user_defined.iter().all(|(p, a)| *p != peer_id && *a != addr) {
			self.discovery.user_defined.push((peer_id, addr));
		}
	}

	/// Disconnects the custom protocols from a peer.
	///
	/// The peer will still be able to use Kademlia or other protocols, but will get disconnected
	/// after a few seconds of inactivity.
	///
	/// This is asynchronous and does not instantly close the custom protocols.
	/// Corresponding closing events will be generated once the closing actually happens.
	///
	/// Has no effect if we're not connected to the `PeerId`.
	#[inline]
	pub fn drop_node(&mut self, peer_id: &PeerId) {
		self.custom_protocols.disconnect_peer(peer_id)
	}

	/// Returns the state of the peerset manager, for debugging purposes.
	pub fn peerset_debug_info(&mut self) -> serde_json::Value {
		self.custom_protocols.peerset_debug_info()
	}
}

/// Event that can be emitted by the behaviour.
#[derive(Debug)]
pub enum BehaviourOut<TMessage> {
	/// Opened a custom protocol with the remote.
	CustomProtocolOpen {
		/// Version of the protocol that has been opened.
		version: u8,
		/// Id of the node we have opened a connection with.
		peer_id: PeerId,
		/// Endpoint used for this custom protocol.
		endpoint: ConnectedPoint,
	},

	/// Closed a custom protocol with the remote.
	CustomProtocolClosed {
		/// Id of the peer we were connected to.
		peer_id: PeerId,
		/// Reason why the substream closed, for diagnostic purposes.
		reason: Cow<'static, str>,
	},

	/// Receives a message on a custom protocol substream.
	CustomMessage {
		/// Id of the peer the message came from.
		peer_id: PeerId,
		/// Message that has been received.
		message: TMessage,
	},

	/// A substream with a remote is clogged. We should avoid sending more data to it if possible.
	Clogged {
		/// Id of the peer the message came from.
		peer_id: PeerId,
		/// Copy of the messages that are within the buffer, for further diagnostic.
		messages: Vec<TMessage>,
	},

	/// We have obtained debug information from a peer.
	Identified {
		/// Id of the peer that has been identified.
		peer_id: PeerId,
		/// Information about the peer.
		info: IdentifyInfo,
	},

	/// We have successfully pinged a peer.
	PingSuccess {
		/// Id of the peer that has been pinged.
		peer_id: PeerId,
		/// Time it took for the ping to come back.
		ping_time: Duration,
	},
}

impl<TMessage> From<CustomProtoOut<TMessage>> for BehaviourOut<TMessage> {
	fn from(other: CustomProtoOut<TMessage>) -> BehaviourOut<TMessage> {
		match other {
			CustomProtoOut::CustomProtocolOpen { version, peer_id, endpoint } => {
				BehaviourOut::CustomProtocolOpen { version, peer_id, endpoint }
			}
			CustomProtoOut::CustomProtocolClosed { peer_id, reason } => {
				BehaviourOut::CustomProtocolClosed { peer_id, reason }
			}
			CustomProtoOut::CustomMessage { peer_id, message } => {
				BehaviourOut::CustomMessage { peer_id, message }
			}
			CustomProtoOut::Clogged { peer_id, messages } => {
				BehaviourOut::Clogged { peer_id, messages }
			}
		}
	}
}

impl<TMessage, TSubstream> NetworkBehaviourEventProcess<void::Void> for Behaviour<TMessage, TSubstream> {
	fn inject_event(&mut self, event: void::Void) {
		void::unreachable(event)
	}
}

impl<TMessage, TSubstream> NetworkBehaviourEventProcess<CustomProtoOut<TMessage>> for Behaviour<TMessage, TSubstream> {
	fn inject_event(&mut self, event: CustomProtoOut<TMessage>) {
		self.events.push(event.into());
	}
}

impl<TMessage, TSubstream> NetworkBehaviourEventProcess<IdentifyEvent> for Behaviour<TMessage, TSubstream> {
	fn inject_event(&mut self, event: IdentifyEvent) {
		match event {
			IdentifyEvent::Identified { peer_id, mut info, .. } => {
				trace!(target: "sub-libp2p", "Identified {:?} => {:?}", peer_id, info);
				// TODO: ideally we would delay the first identification to when we open the custom
				//	protocol, so that we only report id info to the service about the nodes we
				//	care about (https://github.com/libp2p/rust-libp2p/issues/876)
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
				self.custom_protocols.add_discovered_nodes(Some(peer_id.clone()));
				self.events.push(BehaviourOut::Identified { peer_id, info });
			}
			IdentifyEvent::Error { .. } => {}
			IdentifyEvent::SendBack { result: Err(ref err), ref peer_id } =>
				debug!(target: "sub-libp2p", "Error when sending back identify info \
					to {:?} => {}", peer_id, err),
			IdentifyEvent::SendBack { .. } => {}
		}
	}
}

impl<TMessage, TSubstream> NetworkBehaviourEventProcess<KademliaOut> for Behaviour<TMessage, TSubstream> {
	fn inject_event(&mut self, out: KademliaOut) {
		match out {
			KademliaOut::Discovered { .. } => {}
			KademliaOut::KBucketAdded { peer_id, .. } => {
				self.custom_protocols.add_discovered_nodes(Some(peer_id));
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

impl<TMessage, TSubstream> NetworkBehaviourEventProcess<PingEvent> for Behaviour<TMessage, TSubstream> {
	fn inject_event(&mut self, event: PingEvent) {
		match event {
			PingEvent { peer, result: Ok(PingSuccess::Ping { rtt }) } => {
				trace!(target: "sub-libp2p", "Ping time with {:?}: {:?}", peer, rtt);
				self.events.push(BehaviourOut::PingSuccess { peer_id: peer, ping_time: rtt });
			}
			_ => ()
		}
	}
}

#[cfg(not(target_os = "unknown"))]
impl<TMessage, TSubstream> NetworkBehaviourEventProcess<MdnsEvent> for Behaviour<TMessage, TSubstream> {
	fn inject_event(&mut self, event: MdnsEvent) {
		match event {
			MdnsEvent::Discovered(list) => {
				self.custom_protocols.add_discovered_nodes(list.into_iter().map(|(peer_id, _)| peer_id));
			},
			MdnsEvent::Expired(_) => {}
		}
	}
}

impl<TMessage, TSubstream> Behaviour<TMessage, TSubstream> {
	fn poll<TEv>(&mut self) -> Async<NetworkBehaviourAction<TEv, BehaviourOut<TMessage>>> {
		if !self.events.is_empty() {
			return Async::Ready(NetworkBehaviourAction::GenerateEvent(self.events.remove(0)))
		}

		Async::NotReady
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
		info!(target: "sub-libp2p", "Discovered external node address: {}", new_addr);
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
