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

use crate::custom_proto::handler::{CustomProtosHandler, CustomProtosHandlerOut, CustomProtosHandlerIn};
use crate::custom_proto::topology::NetTopology;
use crate::custom_proto::upgrade::{CustomMessage, RegisteredProtocols};
use crate::{NetworkConfiguration, NonReservedPeerMode, ProtocolId};
use crate::parse_str_addr;
use fnv::{FnvHashMap, FnvHashSet};
use futures::prelude::*;
use libp2p::core::swarm::{ConnectedPoint, NetworkBehaviour, NetworkBehaviourAction, PollParameters};
use libp2p::core::{protocols_handler::ProtocolsHandler, Endpoint, Multiaddr, PeerId};
use log::{debug, trace, warn};
use smallvec::SmallVec;
use std::{cmp, error, io, marker::PhantomData, path::Path, time::Duration, time::Instant};
use tokio_io::{AsyncRead, AsyncWrite};
use tokio_timer::Delay;

// File where the network topology is stored.
const NODES_FILE: &str = "nodes.json";
// Duration during which a peer is disabled.
const PEER_DISABLE_DURATION: Duration = Duration::from_secs(5 * 60);

/// Network behaviour that handles opening substreams for custom protocols with other nodes.
pub struct CustomProtos<TMessage, TSubstream> {
	/// List of protocols to open with peers. Never modified.
	registered_protocols: RegisteredProtocols<TMessage>,

	/// Topology of the network.
	topology: NetTopology,

	/// List of custom protocols that we have open with remotes.
	open_protocols: Vec<(PeerId, ProtocolId)>,

	/// List of peer handlers that were enabled.
	///
	/// Note that it is possible for a peer to be in the shutdown process, in which case it will
	/// not be in this list but will be present in `open_protocols`.
	/// It is also possible that we have *just* enabled a peer, in which case it will be in this
	/// list but not in `open_protocols`.
	enabled_peers: FnvHashSet<PeerId>,

	/// Maximum number of incoming non-reserved connections, taken from the config. Never modified.
	max_incoming_connections: usize,

	/// Maximum number of outgoing non-reserved connections, taken from the config. Never modified.
	max_outgoing_connections: usize,

	/// If true, only reserved peers can connect.
	reserved_only: bool,

	/// List of the IDs of the peers we are connected to, and whether we're dialing or listening.
	connected_peers: FnvHashMap<PeerId, ConnectedPoint>,

	/// List of the IDs of the reserved peers. We always try to maintain a connection these peers.
	reserved_peers: FnvHashSet<PeerId>,

	/// List of the IDs of peers that are forbidden, and the moment their ban expires.
	banned_peers: Vec<(PeerId, Instant)>,

	/// When this delay expires, we need to synchronize our active connectons with the
	/// network topology.
	next_connect_to_nodes: Delay,

	/// Events to produce from `poll()`.
	events: SmallVec<[NetworkBehaviourAction<CustomProtosHandlerIn<TMessage>, CustomProtosOut<TMessage>>; 4]>,

	/// Marker to pin the generics.
	marker: PhantomData<TSubstream>,
}

/// Event that can be emitted by the `CustomProtos`.
#[derive(Debug)]
pub enum CustomProtosOut<TMessage> {
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

	/// The substream used by the protocol is pretty large. We should print avoid sending more
	/// messages on it if possible.
	Clogged {
		/// Id of the peer which is clogged.
		peer_id: PeerId,
		/// Protocol which has a problem.
		protocol_id: ProtocolId,
		/// Copy of the messages that are within the buffer, for further diagnostic.
		messages: Vec<TMessage>,
	},
}

impl<TMessage, TSubstream> CustomProtos<TMessage, TSubstream> {
	/// Creates a `CustomProtos`.
	pub fn new(config: &NetworkConfiguration, local_peer_id: &PeerId, registered_protocols: RegisteredProtocols<TMessage>) -> Self {
		// Initialize the topology of the network.
		let mut topology = if let Some(ref path) = config.net_config_path {
			let path = Path::new(path).join(NODES_FILE);
			debug!(target: "sub-libp2p", "Initializing peer store for JSON file {:?}", path);
			NetTopology::from_file(local_peer_id.clone(), path)
		} else {
			debug!(target: "sub-libp2p", "No peers file configured ; peers won't be saved");
			NetTopology::memory(local_peer_id.clone())
		};

		// Add the bootstrap nodes to the topology.
		for bootnode in config.boot_nodes.iter() {
			if let Ok((peer_id, addr)) = parse_str_addr(bootnode) {
				topology.add_bootstrap_addr(&peer_id, addr.clone());
			}
		}

		let max_incoming_connections = config.in_peers as usize;
		let max_outgoing_connections = config.out_peers as usize;

		// Expected maximum number of connections.
		let connec_cap = max_incoming_connections
			.saturating_add(max_outgoing_connections)
			.saturating_add(4); // We add an arbitrary number for reserved peers slots

		// Expected maximum number of substreams.
		let open_protos_cap = connec_cap.saturating_mul(registered_protocols.len());

		CustomProtos {
			registered_protocols,
			topology,
			max_incoming_connections,
			max_outgoing_connections,
			reserved_only: config.non_reserved_mode == NonReservedPeerMode::Deny,
			connected_peers: Default::default(),
			reserved_peers: Default::default(),
			banned_peers: Vec::new(),
			open_protocols: Vec::with_capacity(open_protos_cap),
			enabled_peers: FnvHashSet::with_capacity_and_hasher(connec_cap, Default::default()),
			next_connect_to_nodes: Delay::new(Instant::now()),
			events: SmallVec::new(),
			marker: PhantomData,
		}
	}

	/// Returns the list of reserved nodes.
	pub fn reserved_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.reserved_peers.iter()
	}

	/// Adds a reserved peer.
	pub fn add_reserved_peer(&mut self, peer_id: PeerId, addr: Multiaddr) {
		self.topology.add_bootstrap_addr(&peer_id, addr);
		self.reserved_peers.insert(peer_id);

		// Trigger a `connect_to_nodes` round.
		self.next_connect_to_nodes = Delay::new(Instant::now());
	}

	/// Removes a reserved peer.
	///
	/// If we are in reserved mode and we were connected to a node with this peer ID, then this
	/// method will disconnect it and return its index.
	pub fn remove_reserved_peer(&mut self, peer_id: PeerId) {
		self.reserved_peers.remove(&peer_id);
	}

	/// Returns true if we only accept reserved nodes.
	pub fn is_reserved_only(&self) -> bool {
		self.reserved_only
	}

	/// Start accepting all peers again if we weren't.
	pub fn accept_unreserved_peers(&mut self) {
		if !self.reserved_only {
			return
		}

		self.reserved_only = false;
		// Trigger a `connect_to_nodes` round.
		self.next_connect_to_nodes = Delay::new(Instant::now());
	}

	/// Start refusing non-reserved nodes.
	pub fn deny_unreserved_peers(&mut self) {
		if self.reserved_only {
			return
		}

		self.reserved_only = true;

		// Disconnecting nodes that are connected to us and that aren't reserved
		let reserved_peers = &mut self.reserved_peers;
		let events = &mut self.events;
		self.enabled_peers.retain(move |peer_id| {
			if reserved_peers.contains(peer_id) {
				return true
			}
			events.push(NetworkBehaviourAction::SendEvent {
				peer_id: peer_id.clone(),
				event: CustomProtosHandlerIn::Disable,
			});
			false
		})
	}

	/// Disconnects the given peer if we are connected to it.
	pub fn disconnect_peer(&mut self, peer: &PeerId) {
		if self.reserved_peers.contains(peer) {
			warn!(target: "sub-libp2p", "Ignored attempt to disconnect reserved peer {:?}", peer);
			return;
		}

		if self.enabled_peers.remove(peer) {
			self.events.push(NetworkBehaviourAction::SendEvent {
				peer_id: peer.clone(),
				event: CustomProtosHandlerIn::Disable,
			});
		}
	}

	/// Disconnects the given peer if we are connected to it and disables it for a little while.
	pub fn ban_peer(&mut self, peer_id: PeerId) {
		if self.reserved_peers.contains(&peer_id) {
			warn!(target: "sub-libp2p", "Ignored attempt to ban reserved peer {:?}", peer_id);
			return;
		}

		// Peer is already banned
		if let Some(pos) = self.banned_peers.iter().position(|(p, _)| p == &peer_id) {
			if self.banned_peers[pos].1 > Instant::now() {
				return
			} else {
				self.banned_peers.remove(pos);
			}
		}

		self.banned_peers.push((peer_id.clone(), Instant::now() + PEER_DISABLE_DURATION));
		if self.enabled_peers.remove(&peer_id) {
			self.events.push(NetworkBehaviourAction::SendEvent {
				peer_id,
				event: CustomProtosHandlerIn::Disable,
			});
		}
	}

	/// Returns a list of all the peers that are banned, and until when.
	pub fn banned_peers(&self) -> impl Iterator<Item = (&PeerId, Instant)> {
		self.banned_peers.iter().map(|&(ref id, until)| (id, until))
	}

	/// Returns true if we try to open protocols with the given peer.
	pub fn is_enabled(&self, peer_id: &PeerId) -> bool {
		self.enabled_peers.contains(peer_id)
	}

	/// Returns the list of protocols we have open with the given peer.
	pub fn open_protocols<'a>(&'a self, peer_id: &'a PeerId) -> impl Iterator<Item = ProtocolId> + 'a {
		self.open_protocols
			.iter()
			.filter(move |(p, _)| p == peer_id)
			.map(|(_, proto)| *proto)
	}

	/// Sends a message to a peer using the given custom protocol.
	///
	/// Has no effect if the custom protocol is not open with the given peer.
	///
	/// Also note that even we have a valid open substream, it may in fact be already closed
	/// without us knowing, in which case the packet will not be received.
	pub fn send_packet(&mut self, target: &PeerId, protocol_id: ProtocolId, message: TMessage) {
		self.events.push(NetworkBehaviourAction::SendEvent {
			peer_id: target.clone(),
			event: CustomProtosHandlerIn::SendCustomMessage {
				protocol: protocol_id,
				message,
			}
		});
	}

	/// Indicates to the topology that we have discovered new addresses for a given node.
	pub fn add_discovered_addrs<I>(
		&mut self,
		peer_id: &PeerId,
		addrs: I,
	) where I: Iterator<Item = (Multiaddr, bool)> {
		if self.topology.add_discovered_addrs(peer_id, addrs) {
			// Trigger a `connect_to_nodes` round.
			self.next_connect_to_nodes = Delay::new(Instant::now());
		}
	}

	/// Returns the number of peers in the topology.
	pub fn num_topology_peers(&self) -> usize {
		self.topology.num_peers()
	}

	/// Flushes the topology to the disk.
	pub fn flush_topology(&mut self) -> Result<(), io::Error> {
		self.topology.flush_to_disk()
	}

	/// Perform a cleanup pass, removing all obsolete addresses and peers.
	///
	/// This should be done from time to time.
	pub fn cleanup(&mut self) {
		self.topology.cleanup();
	}

	/// Returns the list of peers in the topology.
	pub fn known_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.topology.known_peers()
	}

	/// Returns a list of addresses known for this peer, and their reputation score.
	pub fn known_addresses(&mut self, peer_id: &PeerId) -> impl Iterator<Item = (&Multiaddr, u32)> {
		self.topology.addresses_of_peer(peer_id, true)
	}

	/// Updates the attempted connections to nodes.
	///
	/// Also updates `next_connect_to_nodes` with the earliest known moment when we need to
	/// update connections again.
	fn connect_to_nodes(&mut self, params: &mut PollParameters) {
		// Value of `Instant::now()` grabbed once at the beginning.
		let now = Instant::now();

		// Make sure we are connected or connecting to all the reserved nodes.
		for reserved in self.reserved_peers.iter() {
			// TODO: don't generate an event if we're already in a pending connection (https://github.com/libp2p/rust-libp2p/issues/697)
			if !self.enabled_peers.contains(&reserved) {
				self.events.push(NetworkBehaviourAction::DialPeer { peer_id: reserved.clone() });
			}
		}

		// We're done with reserved node; return early if there's nothing more to do.
		if self.reserved_only {
			// We set a timeout to 60 seconds for trying to connect again, however in practice
			// a round will happen as soon as we fail to dial, disconnect from a node, allow
			// unreserved nodes, and so on.
			self.next_connect_to_nodes.reset(now + Duration::from_secs(60));
			return
		}

		// Counter of number of connections to open, decreased when we open one.
		let mut num_to_open = {
			let num_outgoing_connections = self.enabled_peers
				.iter()
				.filter(|p| self.connected_peers.get(p).map(|c| c.is_dialer()).unwrap_or(false))
				.filter(|p| !self.reserved_peers.contains(p))
				.count();
			self.max_outgoing_connections - num_outgoing_connections
		};
		trace!(target: "sub-libp2p", "Connect-to-nodes round; attempting to fill {:?} slots",
			num_to_open);

		// We first try to enable existing connections.
		for peer_id in self.connected_peers.keys() {
			if num_to_open == 0 {
				break
			}

			if self.enabled_peers.contains(peer_id) {
				continue;
			}

			if let Some((_, expire)) = self.banned_peers.iter().find(|(p, _)| p == peer_id) {
				if *expire >= now {
					continue;
				}
			}

			trace!(target: "sub-libp2p", "Enabling custom protocols with {:?} (active)", peer_id);
			num_to_open -= 1;
			self.events.push(NetworkBehaviourAction::SendEvent {
				peer_id: peer_id.clone(),
				event: CustomProtosHandlerIn::Enable(Endpoint::Dialer),
			});
		}

		// Then, try to open new connections.
		let local_peer_id = params.local_peer_id().clone();
		let (to_try, will_change) = self.topology.addrs_to_attempt();
		for (peer_id, _) in to_try {
			if num_to_open == 0 {
				break
			}

			if peer_id == &local_peer_id {
				continue
			}

			if self.connected_peers.contains_key(&peer_id) {
				continue
			}

			if let Some((_, ban_end)) = self.banned_peers.iter().find(|(p, _)| p == peer_id) {
				if *ban_end > now {
					continue
				}
			}

			num_to_open -= 1;
			self.events.push(NetworkBehaviourAction::DialPeer { peer_id: peer_id.clone() });
		}

		// Next round is when we expect the topology will change.
		self.next_connect_to_nodes.reset(cmp::min(will_change, now + Duration::from_secs(60)));
	}
}

impl<TMessage, TSubstream> NetworkBehaviour for CustomProtos<TMessage, TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
	TMessage: CustomMessage,
{
	type ProtocolsHandler = CustomProtosHandler<TMessage, TSubstream>;
	type OutEvent = CustomProtosOut<TMessage>;

	fn new_handler(&mut self) -> Self::ProtocolsHandler {
		CustomProtosHandler::new(self.registered_protocols.clone())
	}

	fn addresses_of_peer(&mut self, peer_id: &PeerId) -> Vec<Multiaddr> {
		self.topology.addresses_of_peer(peer_id, false).map(|(a, _)| a.clone()).collect()
	}

	fn inject_connected(&mut self, peer_id: PeerId, endpoint: ConnectedPoint) {
		// When a peer connects, its handler is initially in the disabled state. We make sure that
		// the peer is allowed, and if so we put it in the enabled state.

		self.connected_peers.insert(peer_id.clone(), endpoint.clone());

		let is_reserved = self.reserved_peers.contains(&peer_id);
		if self.reserved_only && !is_reserved {
			debug!(target: "sub-libp2p", "Ignoring {:?} because we're in reserved mode", peer_id);
			self.events.push(NetworkBehaviourAction::SendEvent {
				peer_id: peer_id.clone(),
				event: CustomProtosHandlerIn::Disable,
			});
			return
		}

		// Check whether peer is banned.
		if !is_reserved {
			if let Some((_, expire)) = self.banned_peers.iter().find(|(p, _)| p == &peer_id) {
				if *expire >= Instant::now() {
					debug!(target: "sub-libp2p", "Ignoring banned peer {:?}", peer_id);
					self.events.push(NetworkBehaviourAction::SendEvent {
						peer_id: peer_id.clone(),
						event: CustomProtosHandlerIn::Disable,
					});
					return
				}
			}
		}

		// Check the limits on the ingoing and outgoing connections.
		match endpoint {
			ConnectedPoint::Dialer { .. } => {
				let num_outgoing = self.enabled_peers.iter()
					.filter(|p| self.connected_peers.get(p).map(|c| c.is_dialer()).unwrap_or(false))
					.filter(|p| !self.reserved_peers.contains(p))
					.count();

				debug_assert!(num_outgoing <= self.max_outgoing_connections);
				if num_outgoing == self.max_outgoing_connections {
					self.events.push(NetworkBehaviourAction::SendEvent {
						peer_id: peer_id.clone(),
						event: CustomProtosHandlerIn::Disable,
					});
					return
				}
			}
			ConnectedPoint::Listener { .. } => {
				let num_ingoing = self.enabled_peers.iter()
					.filter(|p| self.connected_peers.get(p).map(|c| c.is_listener()).unwrap_or(false))
					.filter(|p| !self.reserved_peers.contains(p))
					.count();

				debug_assert!(num_ingoing <= self.max_incoming_connections);
				if num_ingoing == self.max_incoming_connections {
					debug!(target: "sub-libp2p", "Ignoring incoming connection from {:?} because \
						we're full", peer_id);
					self.events.push(NetworkBehaviourAction::SendEvent {
						peer_id: peer_id.clone(),
						event: CustomProtosHandlerIn::Disable,
					});
					return
				}
			}
		}

		// If everything is fine, enable the node.
		debug_assert!(!self.enabled_peers.contains(&peer_id));
		// We ask the handler to actively open substreams only if we are the dialer; otherwise
		// the two nodes will race to be the first to open the unique allowed substream.
		if endpoint.is_dialer() {
			trace!(target: "sub-libp2p", "Enabling custom protocols with {:?} (active)", peer_id);
			self.events.push(NetworkBehaviourAction::SendEvent {
				peer_id: peer_id.clone(),
				event: CustomProtosHandlerIn::Enable(Endpoint::Dialer),
			});
		} else {
			trace!(target: "sub-libp2p", "Enabling custom protocols with {:?} (passive)", peer_id);
			self.events.push(NetworkBehaviourAction::SendEvent {
				peer_id: peer_id.clone(),
				event: CustomProtosHandlerIn::Enable(Endpoint::Listener),
			});
		}

		self.topology.set_connected(&peer_id, &endpoint);
		self.enabled_peers.insert(peer_id);
	}

	fn inject_disconnected(&mut self, peer_id: &PeerId, endpoint: ConnectedPoint) {
		let was_connected = self.connected_peers.remove(&peer_id);
		debug_assert!(was_connected.is_some());

		self.topology.set_disconnected(peer_id, &endpoint);

		while let Some(pos) = self.open_protocols.iter().position(|(p, _)| p == peer_id) {
			let (_, protocol_id) = self.open_protocols.remove(pos);

			let event = CustomProtosOut::CustomProtocolClosed {
				protocol_id,
				peer_id: peer_id.clone(),
				result: Ok(()),
			};

			self.events.push(NetworkBehaviourAction::GenerateEvent(event));
		}

		// Trigger a `connect_to_nodes` round.
		self.next_connect_to_nodes = Delay::new(Instant::now());

		self.enabled_peers.remove(peer_id);
	}

	fn inject_dial_failure(&mut self, peer_id: Option<&PeerId>, addr: &Multiaddr, error: &dyn error::Error) {
		if let Some(peer_id) = peer_id.as_ref() {
			debug!(target: "sub-libp2p", "Failed to reach peer {:?} through {} => {:?}", peer_id, addr, error);
			self.topology.set_unreachable(addr);

			// Trigger a `connect_to_nodes` round.
			self.next_connect_to_nodes = Delay::new(Instant::now());

		} else {
			// This code path is only reached if `peer_id` is None, which means that we dialed an
			// address without knowing the `PeerId` to expect. We don't currently do that, except
			// in one situation: for convenience, we accept bootstrap node addresses in the format
			// `IP:PORT`.
			// There is no reason this trigger a `connect_to_nodes` round in that situation.
			debug!(target: "sub-libp2p", "Failed to reach {} => {:?}", addr, error);
			self.topology.set_unreachable(addr);
		}
	}

	fn inject_node_event(
		&mut self,
		source: PeerId,
		event: <Self::ProtocolsHandler as ProtocolsHandler>::OutEvent,
	) {
		match event {
			CustomProtosHandlerOut::CustomProtocolClosed { protocol_id, result } => {
				let pos = self.open_protocols.iter().position(|(s, p)|
					s == &source && p == &protocol_id
				);

				if let Some(pos) = pos {
					self.open_protocols.remove(pos);
				} else {
					debug_assert!(false, "Couldn't find protocol in open_protocols");
				}

				let event = CustomProtosOut::CustomProtocolClosed {
					protocol_id,
					result,
					peer_id: source,
				};

				self.events.push(NetworkBehaviourAction::GenerateEvent(event));
			}
			CustomProtosHandlerOut::CustomProtocolOpen { protocol_id, version } => {
				debug_assert!(!self.open_protocols.iter().any(|(s, p)|
					s == &source && p == &protocol_id
				));
				self.open_protocols.push((source.clone(), protocol_id));

				let endpoint = self.connected_peers.get(&source)
					.expect("We only receive events from connected nodes; QED").clone();
				let event = CustomProtosOut::CustomProtocolOpen {
					protocol_id,
					version,
					peer_id: source,
					endpoint,
				};

				self.events.push(NetworkBehaviourAction::GenerateEvent(event));
			}
			CustomProtosHandlerOut::CustomMessage { protocol_id, message } => {
				debug_assert!(self.open_protocols.iter().any(|(s, p)|
					s == &source && p == &protocol_id
				));
				let event = CustomProtosOut::CustomMessage {
					peer_id: source,
					protocol_id,
					message,
				};

				self.events.push(NetworkBehaviourAction::GenerateEvent(event));
			}
			CustomProtosHandlerOut::Clogged { protocol_id, messages } => {
				debug_assert!(self.open_protocols.iter().any(|(s, p)|
					s == &source && p == &protocol_id
				));
				warn!(target: "sub-libp2p", "Queue of packets to send to {:?} (protocol: {:?}) is \
					pretty large", source, protocol_id);
				self.events.push(NetworkBehaviourAction::GenerateEvent(CustomProtosOut::Clogged {
					peer_id: source,
					protocol_id,
					messages,
				}));
			}
			CustomProtosHandlerOut::ProtocolError { protocol_id, error, is_severe } => {
				if is_severe {
					warn!(target: "sub-libp2p", "Network misbehaviour from {:?} with protocol \
						{:?}: {:?}", source, protocol_id, error);
					self.ban_peer(source);
				} else {
					debug!(target: "sub-libp2p", "Network misbehaviour from {:?} with protocol \
						{:?}: {:?}", source, protocol_id, error);
					self.disconnect_peer(&source);
				}
			}
		}
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
		loop {
			match self.next_connect_to_nodes.poll() {
				Ok(Async::Ready(())) => self.connect_to_nodes(params),
				Ok(Async::NotReady) => break,
				Err(err) => {
					warn!(target: "sub-libp2p", "Connect-to-nodes timer errored: {:?}", err);
					break
				}
			}
		}

		// Clean up `banned_peers`
		self.banned_peers.retain(|(_, end)| *end > Instant::now());
		self.banned_peers.shrink_to_fit();

		if !self.events.is_empty() {
			return Async::Ready(self.events.remove(0))
		}

		Async::NotReady
	}
}
