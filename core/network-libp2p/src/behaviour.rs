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
use bytes::Bytes;
use futures::prelude::*;
use libp2p::NetworkBehaviour;
use libp2p::core::{PeerId, ProtocolsHandler};
use libp2p::core::swarm::{ConnectedPoint, NetworkBehaviour, NetworkBehaviourAction};
use libp2p::core::swarm::{NetworkBehaviourEventProcess, PollParameters};
use libp2p::identify::{Identify, IdentifyEvent, protocol::IdentifyInfo};
use libp2p::kad::{Kademlia, KademliaOut, KademliaTopology};
use libp2p::ping::{Ping, PingEvent};
use log::{debug, trace, warn};
use std::{cmp, io, time::Duration, time::Instant};
use tokio_io::{AsyncRead, AsyncWrite};
use tokio_timer::Delay;
use void;

/// General behaviour of the network.
#[derive(NetworkBehaviour)]
#[behaviour(out_event = "BehaviourOut", poll_method = "poll")]
pub struct Behaviour<TSubstream> {
	/// Periodically ping nodes, and close the connection if it's unresponsive.
	ping: Ping<TSubstream>,
	/// Custom protocols (dot, bbq, sub, etc.).
	custom_protocols: CustomProtos<TSubstream>,
	/// Discovers nodes of the network. Defined below.
	discovery: DiscoveryBehaviour<TSubstream>,
	/// Periodically identifies the remote and responds to incoming requests.
	identify: Identify<TSubstream>,

	/// Queue of events to produce for the outside.
	#[behaviour(ignore)]
	events: Vec<BehaviourOut>,
}

impl<TSubstream> Behaviour<TSubstream> {
	/// Builds a new `Behaviour`.
	// TODO: redundancy between config and local_peer_id (https://github.com/libp2p/rust-libp2p/issues/745)
	pub fn new(config: &NetworkConfiguration, local_peer_id: PeerId, protocols: RegisteredProtocols) -> Self {
		let identify = {
			let proto_version = "/substrate/1.0".to_string();
			let user_agent = format!("{} ({})", config.client_version, config.node_name);
			Identify::new(proto_version, user_agent)
		};

		Behaviour {
			ping: Ping::new(),
			custom_protocols: CustomProtos::new(config, protocols),
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
	pub fn send_custom_message(&mut self, target: &PeerId, protocol_id: ProtocolId, data: impl Into<Bytes>) {
		self.custom_protocols.send_packet(target, protocol_id, data)
	}

	/// Try to add a reserved peer.
	pub fn add_reserved_peer(&mut self, peer_id: PeerId) {
		self.custom_protocols.add_reserved_peer(peer_id)
	}

	/// Try to remove a reserved peer.
	///
	/// If we are in reserved mode and we were connected to a node with this peer ID, then this
	/// method will disconnect it and return its index.
	pub fn remove_reserved_peer(&mut self, peer_id: PeerId) {
		self.custom_protocols.remove_reserved_peer(peer_id)
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
}

/// Event that can be emitted by the behaviour.
#[derive(Debug)]
pub enum BehaviourOut {
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
		/// Data that has been received.
		data: Bytes,
	},

	/// We have obtained debug information from a peer.
	Identified {
		/// Id of the peer that has been identified.
		peer_id: PeerId,
		/// Information about the peer.
		info: IdentifyInfo,
	},
}

impl From<CustomProtosOut> for BehaviourOut {
	fn from(other: CustomProtosOut) -> BehaviourOut {
		match other {
			CustomProtosOut::CustomProtocolOpen { protocol_id, version, peer_id, endpoint } => {
				BehaviourOut::CustomProtocolOpen { protocol_id, version, peer_id, endpoint }
			},
			CustomProtosOut::CustomProtocolClosed { protocol_id, peer_id, result } => {
				BehaviourOut::CustomProtocolClosed { protocol_id, peer_id, result }
			},
			CustomProtosOut::CustomMessage { protocol_id, peer_id, data } => {
				BehaviourOut::CustomMessage { protocol_id, peer_id, data }
			},
		}
	}
}

impl<TSubstream> NetworkBehaviourEventProcess<void::Void> for Behaviour<TSubstream> {
	fn inject_event(&mut self, event: void::Void) {
		void::unreachable(event)
	}
}

impl<TSubstream> NetworkBehaviourEventProcess<CustomProtosOut> for Behaviour<TSubstream> {
	fn inject_event(&mut self, event: CustomProtosOut) {
		self.events.push(event.into());
	}
}

impl<TSubstream> NetworkBehaviourEventProcess<IdentifyEvent> for Behaviour<TSubstream> {
	fn inject_event(&mut self, event: IdentifyEvent) {
		match event {
			IdentifyEvent::Identified { peer_id, info, .. } => {
				trace!(target: "sub-libp2p", "Identified {:?} => {:?}", peer_id, info);
				// TODO: ideally we would delay the first identification to when we open the custom
				//	protocol, so that we only report id info to the service about the nodes we
				//	care about (https://github.com/libp2p/rust-libp2p/issues/876)
				self.events.push(BehaviourOut::Identified { peer_id, info });
			}
			IdentifyEvent::Error { .. } => {}
		}
	}
}

impl<TSubstream> NetworkBehaviourEventProcess<KademliaOut> for Behaviour<TSubstream> {
	fn inject_event(&mut self, out: KademliaOut) {
		// We only ever use Kademlia for discovering nodes, and nodes discovered by Kademlia are
		// automatically added to the topology. Therefore we don't need to perform any further
		// action.
		match out {
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

impl<TSubstream> NetworkBehaviourEventProcess<PingEvent> for Behaviour<TSubstream> {
	fn inject_event(&mut self, event: PingEvent) {
		match event {
			PingEvent::PingSuccess { peer, time } => {
				trace!(target: "sub-libp2p", "Ping time with {:?}: {:?}", peer, time);
			}
		}
	}
}

impl<TSubstream> Behaviour<TSubstream> {
	fn poll<TEv>(&mut self) -> Async<NetworkBehaviourAction<TEv, BehaviourOut>> {
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

impl<TSubstream, TTopology> NetworkBehaviour<TTopology> for DiscoveryBehaviour<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
	TTopology: KademliaTopology,
{
	type ProtocolsHandler = <Kademlia<TSubstream> as NetworkBehaviour<TTopology>>::ProtocolsHandler;
	type OutEvent = <Kademlia<TSubstream> as NetworkBehaviour<TTopology>>::OutEvent;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		NetworkBehaviour::<TTopology>::new_handler(&mut self.kademlia)
	}

	fn inject_connected(&mut self, peer_id: PeerId, endpoint: ConnectedPoint) {
		NetworkBehaviour::<TTopology>::inject_connected(&mut self.kademlia, peer_id, endpoint)
	}

	fn inject_disconnected(&mut self, peer_id: &PeerId, endpoint: ConnectedPoint) {
		NetworkBehaviour::<TTopology>::inject_disconnected(&mut self.kademlia, peer_id, endpoint)
	}

	fn inject_node_event(
		&mut self,
		peer_id: PeerId,
		event: <Self::ProtocolsHandler as ProtocolsHandler>::OutEvent,
	) {
		NetworkBehaviour::<TTopology>::inject_node_event(&mut self.kademlia, peer_id, event)
	}

	fn poll(
		&mut self,
		params: &mut PollParameters<TTopology>,
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

