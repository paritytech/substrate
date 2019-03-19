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

use crate::custom_proto::{CustomProtos, CustomProtosOut, RegisteredProtocols};
use crate::{NetworkConfiguration, ProtocolId};
use futures::prelude::*;
use libp2p::NetworkBehaviour;
use libp2p::core::{Multiaddr, PeerId, ProtocolsHandler, PublicKey};
use libp2p::core::swarm::{ConnectedPoint, NetworkBehaviour, NetworkBehaviourAction};
use libp2p::core::swarm::{NetworkBehaviourEventProcess, PollParameters};
use libp2p::identify::{Identify, IdentifyEvent, protocol::IdentifyInfo};
use libp2p::kad::{Kademlia, KademliaOut, KadConnectionType};
use libp2p::ping::{Ping, PingEvent};
use log::{debug, trace, warn};
use std::{cmp, io, fmt, time::Duration, time::Instant};
use tokio_io::{AsyncRead, AsyncWrite};
use tokio_timer::Delay;
use void;

/// General behaviour of the network.
#[derive(NetworkBehaviour)]
#[behaviour(out_event = "BehaviourOut<TMessage>", poll_method = "poll")]
pub struct Behaviour<TMessage, TSubstream> {
	/// Periodically ping nodes, and close the connection if it's unresponsive.
	ping: Ping<TSubstream>,
	/// Custom protocols (dot, bbq, sub, etc.).
	custom_protocols: CustomProtos<TMessage, TSubstream>,
	/// Discovers nodes of the network. Defined below.
	discovery: DiscoveryBehaviour<TSubstream>,
	/// Periodically identifies the remote and responds to incoming requests.
	identify: Identify<TSubstream>,

	/// Queue of events to produce for the outside.
	#[behaviour(ignore)]
	events: Vec<BehaviourOut<TMessage>>,
}

impl<TMessage, TSubstream> Behaviour<TMessage, TSubstream> {
	/// Builds a new `Behaviour`.
	// TODO: redundancy between config and local_public_key (https://github.com/libp2p/rust-libp2p/issues/745)
	pub fn new(config: &NetworkConfiguration, local_public_key: PublicKey, protocols: RegisteredProtocols<TMessage>) -> Self {
		let identify = {
			let proto_version = "/substrate/1.0".to_string();
			let user_agent = format!("{} ({})", config.client_version, config.node_name);
			Identify::new(proto_version, user_agent, local_public_key.clone())
		};

		let local_peer_id = local_public_key.into_peer_id();
		let custom_protocols = CustomProtos::new(config, &local_peer_id, protocols);

		Behaviour {
			ping: Ping::new(),
			custom_protocols,
			discovery: DiscoveryBehaviour::new(local_peer_id),
			identify,
			events: Vec::new(),
		}
	}

	/// Sends a message to a peer using the given custom protocol.
	///
	/// Has no effect if the custom protocol is not open with the given peer.
	///
	/// Also note that even we have a valid open substream, it may in fact be already closed
	/// without us knowing, in which case the packet will not be received.
	#[inline]
	pub fn send_custom_message(&mut self, target: &PeerId, protocol_id: ProtocolId, data: TMessage) {
		self.custom_protocols.send_packet(target, protocol_id, data)
	}

	/// Returns the number of peers in the topology.
	pub fn num_topology_peers(&self) -> usize {
		self.custom_protocols.num_topology_peers()
	}

	/// Flushes the topology to the disk.
	pub fn flush_topology(&mut self) -> Result<(), io::Error> {
		self.custom_protocols.flush_topology()
	}

	/// Perform a cleanup pass, removing all obsolete addresses and peers.
	///
	/// This should be done from time to time.
	pub fn cleanup(&mut self) {
		self.custom_protocols.cleanup();
	}

	/// Returns the list of reserved nodes.
	pub fn reserved_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.custom_protocols.reserved_peers()
	}

	/// Try to add a reserved peer.
	pub fn add_reserved_peer(&mut self, peer_id: PeerId, addr: Multiaddr) {
		self.custom_protocols.add_reserved_peer(peer_id, addr)
	}

	/// Try to remove a reserved peer.
	///
	/// If we are in reserved mode and we were connected to a node with this peer ID, then this
	/// method will disconnect it and return its index.
	pub fn remove_reserved_peer(&mut self, peer_id: PeerId) {
		self.custom_protocols.remove_reserved_peer(peer_id)
	}

	/// Returns true if we only accept reserved nodes.
	pub fn is_reserved_only(&self) -> bool {
		self.custom_protocols.is_reserved_only()
	}

	/// Start accepting all peers again if we weren't.
	pub fn accept_unreserved_peers(&mut self) {
		self.custom_protocols.accept_unreserved_peers()
	}

	/// Start refusing non-reserved nodes. Returns the list of nodes that have been disconnected.
	pub fn deny_unreserved_peers(&mut self) {
		self.custom_protocols.deny_unreserved_peers()
	}

	/// Disconnects a peer and bans it for a little while.
	///
	/// Same as `drop_node`, except that the same peer will not be able to reconnect later.
	#[inline]
	pub fn ban_node(&mut self, peer_id: PeerId) {
		self.custom_protocols.ban_peer(peer_id)
	}

	/// Returns a list of all the peers that are banned, and until when.
	pub fn banned_nodes(&self) -> impl Iterator<Item = (&PeerId, Instant)> {
		self.custom_protocols.banned_peers()
	}

	/// Returns true if we try to open protocols with the given peer.
	pub fn is_enabled(&self, peer_id: &PeerId) -> bool {
		self.custom_protocols.is_enabled(peer_id)
	}

	/// Returns the list of protocols we have open with the given peer.
	pub fn open_protocols<'a>(&'a self, peer_id: &'a PeerId) -> impl Iterator<Item = ProtocolId> + 'a {
		self.custom_protocols.open_protocols(peer_id)
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

	/// Returns the list of peers in the topology.
	pub fn known_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.custom_protocols.known_peers()
	}

	/// Returns a list of addresses known for this peer, and their reputation score.
	pub fn known_addresses(&mut self, peer_id: &PeerId) -> impl Iterator<Item = (&Multiaddr, u32)> {
		self.custom_protocols.known_addresses(peer_id)
	}
}

/// Event that can be emitted by the behaviour.
#[derive(Debug)]
pub enum BehaviourOut<TMessage> {
	/// Opened a custom protocol with the remote.
	CustomProtocolOpen {
		/// Identifier of the protocol.
		protocol_id: ProtocolId,
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
		/// Identifier of the protocol.
		protocol_id: ProtocolId,
		/// Reason why the substream closed. If `Ok`, then it's a graceful exit (EOF).
		result: io::Result<()>,
	},

	/// Receives a message on a custom protocol substream.
	CustomMessage {
		/// Id of the peer the message came from.
		peer_id: PeerId,
		/// Protocol which generated the message.
		protocol_id: ProtocolId,
		/// Message that has been received.
		message: TMessage,
	},

	/// A substream with a remote is clogged. We should avoid sending more data to it if possible.
	Clogged {
		/// Id of the peer the message came from.
		peer_id: PeerId,
		/// Protocol which generated the message.
		protocol_id: ProtocolId,
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

impl<TMessage> From<CustomProtosOut<TMessage>> for BehaviourOut<TMessage> {
	fn from(other: CustomProtosOut<TMessage>) -> BehaviourOut<TMessage> {
		match other {
			CustomProtosOut::CustomProtocolOpen { protocol_id, version, peer_id, endpoint } => {
				BehaviourOut::CustomProtocolOpen { protocol_id, version, peer_id, endpoint }
			}
			CustomProtosOut::CustomProtocolClosed { protocol_id, peer_id, result } => {
				BehaviourOut::CustomProtocolClosed { protocol_id, peer_id, result }
			}
			CustomProtosOut::CustomMessage { protocol_id, peer_id, message } => {
				BehaviourOut::CustomMessage { protocol_id, peer_id, message }
			}
			CustomProtosOut::Clogged { protocol_id, peer_id, messages } => {
				BehaviourOut::Clogged { protocol_id, peer_id, messages }
			}
		}
	}
}

impl<TMessage, TSubstream> NetworkBehaviourEventProcess<void::Void> for Behaviour<TMessage, TSubstream> {
	fn inject_event(&mut self, event: void::Void) {
		void::unreachable(event)
	}
}

impl<TMessage, TSubstream> NetworkBehaviourEventProcess<CustomProtosOut<TMessage>> for Behaviour<TMessage, TSubstream> {
	fn inject_event(&mut self, event: CustomProtosOut<TMessage>) {
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
					warn!(target: "sub-libp2p", "Node {:?} id reported more than 30 addresses",
						peer_id);
					info.listen_addrs.truncate(30);
				}
				for addr in &info.listen_addrs {
					self.discovery.kademlia.add_connected_address(&peer_id, addr.clone());
				}
				self.custom_protocols.add_discovered_addrs(
					&peer_id,
					info.listen_addrs.iter().map(|addr| (addr.clone(), true))
				);
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
			KademliaOut::Discovered { peer_id, addresses, ty } => {
				self.custom_protocols.add_discovered_addrs(
					&peer_id,
					addresses.into_iter().map(|addr| (addr, ty == KadConnectionType::Connected))
				);
			}
			KademliaOut::FindNodeResult { key, closer_peers } => {
				trace!(target: "sub-libp2p", "Kademlia query for {:?} yielded {:?} results",
					key, closer_peers.len());
				if closer_peers.is_empty() {
					warn!(target: "sub-libp2p", "Kademlia random query has yielded empty results");
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
			PingEvent::PingSuccess { peer, time } => {
				trace!(target: "sub-libp2p", "Ping time with {:?}: {:?}", peer, time);
				self.events.push(BehaviourOut::PingSuccess { peer_id: peer, ping_time: time });
			}
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
	/// Kademlia requests and answers.
	kademlia: Kademlia<TSubstream>,
	/// Stream that fires when we need to perform the next random Kademlia query.
	next_kad_random_query: Delay,
	/// After `next_kad_random_query` triggers, the next one triggers after this duration.
	duration_to_next_kad: Duration,
}

impl<TSubstream> DiscoveryBehaviour<TSubstream> {
	fn new(local_peer_id: PeerId) -> Self {
		DiscoveryBehaviour {
			kademlia: Kademlia::without_init(local_peer_id),
			next_kad_random_query: Delay::new(Instant::now()),
			duration_to_next_kad: Duration::from_secs(1),
		}
	}
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
		self.kademlia.addresses_of_peer(peer_id)
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
					debug!(target: "sub-libp2p", "Starting random Kademlia request for {:?}",
						random_peer_id);
					self.kademlia.find_node(random_peer_id);

					// Reset the `Delay` to the next random.
					self.next_kad_random_query.reset(Instant::now() + self.duration_to_next_kad);
					self.duration_to_next_kad = cmp::min(self.duration_to_next_kad * 2,
						Duration::from_secs(60));
				},
				Err(err) => {
					warn!(target: "sub-libp2p", "Kad query timer errored: {:?}", err);
					break
				}
			}
		}

		Async::NotReady
	}
}

/// The severity of misbehaviour of a peer that is reported.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Severity {
	/// Peer is timing out. Could be bad connectivity of overload of work on either of our sides.
	Timeout,
	/// Peer has been notably useless. E.g. unable to answer a request that we might reasonably consider
	/// it could answer.
	Useless(String),
	/// Peer has behaved in an invalid manner. This doesn't necessarily need to be Byzantine, but peer
	/// must have taken concrete action in order to behave in such a way which is wantanly invalid.
	Bad(String),
}

impl fmt::Display for Severity {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Severity::Timeout => write!(fmt, "Timeout"),
			Severity::Useless(r) => write!(fmt, "Useless ({})", r),
			Severity::Bad(r) => write!(fmt, "Bad ({})", r),
		}
	}
}

