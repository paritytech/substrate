// Copyright 2018 Parity Technologies (UK) Ltd.
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

use bytes::Bytes;
use custom_proto::RegisteredProtocols;
use fnv::FnvHashMap;
use futures::{prelude::*, Stream};
use libp2p::{Multiaddr, multiaddr::Protocol, PeerId};
use libp2p::core::{muxing, Endpoint, PublicKey};
use libp2p::core::nodes::node::Substream;
use libp2p::core::nodes::swarm::{ConnectedPoint, Swarm as Libp2pSwarm, HandlerFactory};
use libp2p::core::nodes::swarm::{SwarmEvent as Libp2pSwarmEvent, Peer as SwarmPeer};
use libp2p::core::transport::boxed::Boxed;
use libp2p::kad::{KadConnecController, KadFindNodeRespond};
use libp2p::secio;
use node_handler::{SubstrateOutEvent, SubstrateNodeHandler, SubstrateInEvent, IdentificationRequest};
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
use std::{mem, sync::Arc};
use transport;
use {Error, NodeIndex, ProtocolId};

/// Starts a swarm.
///
/// Returns a stream that must be polled regularly in order for the networking to function.
pub fn start_swarm(
	registered_custom: RegisteredProtocols,
	local_private_key: secio::SecioKeyPair,
) -> Result<Swarm, Error> {
	// Private and public keys.
	let local_public_key = local_private_key.to_public_key();
	let local_peer_id = local_public_key.clone().into_peer_id();

	// Build the transport layer. This is what allows us to listen or to reach nodes.
	let transport = transport::build_transport(local_private_key);

	// Build the underlying libp2p swarm.
	let swarm = Libp2pSwarm::with_handler_builder(transport, HandlerBuilder(Arc::new(registered_custom)));

	Ok(Swarm {
		swarm,
		local_public_key,
		local_peer_id,
		listening_addrs: Vec::new(),
		node_by_peer: Default::default(),
		nodes_info: Default::default(),
		next_node_index: 0,
	})
}

/// Dummy structure that exists because we need to be able to express the type. Otherwise we would
/// use a closure.
#[derive(Clone)]
struct HandlerBuilder(Arc<RegisteredProtocols>);
impl HandlerFactory for HandlerBuilder
{
	type Handler = SubstrateNodeHandler<Substream<Muxer>>;

	#[inline]
	fn new_handler(&self, addr: ConnectedPoint) -> Self::Handler {
		SubstrateNodeHandler::new(self.0.clone(), addr)
	}
}

/// Event produced by the swarm.
pub enum SwarmEvent {
	/// We have successfully connected to a node.
	///
	/// The node is in pending node, and should be accepted by calling `accept_node(node_index)`
	/// or denied by calling `drop_node(node_index)`.
	NodePending {
		/// Index of the node.
		node_index: NodeIndex,
		/// Public key of the node as a peer id.
		peer_id: PeerId,
		/// Whether we dialed the node or if it came to us.
		endpoint: ConnectedPoint,
	},

	/// The connection to a peer has changed.
	Reconnected {
		/// Index of the node.
		node_index: NodeIndex,
		/// The new endpoint.
		endpoint: ConnectedPoint,
		/// List of custom protocols that were closed in the process.
		closed_custom_protocols: Vec<ProtocolId>,
	},

	/// Closed connection to a node, either gracefully or because of an error.
	///
	/// It is guaranteed that this node has been opened with a `NewNode` event beforehand. However
	/// not all `ClosedCustomProtocol` events have been dispatched.
	NodeClosed {
		/// Index of the node.
		node_index: NodeIndex,
		/// Peer id we were connected to.
		peer_id: PeerId,
		/// List of custom protocols that were still open.
		closed_custom_protocols: Vec<ProtocolId>,
	},

	/// Failed to dial an address.
	DialFail {
		/// Address that failed.
		address: Multiaddr,
		/// Reason why we failed.
		error: IoError,
	},

	/// Report information about the node.
	NodeInfos {
		/// Index of the node.
		node_index: NodeIndex,
		/// The client version. Note that it can be anything and should not be trusted.
		client_version: String,
		/// Multiaddresses the node is listening on.
		listen_addrs: Vec<Multiaddr>,
	},

	/// A custom protocol substream has been opened with a node.
	OpenedCustomProtocol {
		/// Index of the node.
		node_index: NodeIndex,
		/// Protocol that has been opened.
		protocol: ProtocolId,
		/// Version of the protocol that was opened.
		version: u8,
	},

	/// A custom protocol substream has been closed.
	ClosedCustomProtocol {
		/// Index of the node.
		node_index: NodeIndex,
		/// Protocol that has been closed.
		protocol: ProtocolId,
	},

	/// Receives a message on a custom protocol stream.
	CustomMessage {
		/// Index of the node.
		node_index: NodeIndex,
		/// Protocol which generated the message.
		protocol_id: ProtocolId,
		/// Data that has been received.
		data: Bytes,
	},

	/// The node has been determined to be unresponsive.
	UnresponsiveNode {
		/// Index of the node.
		node_index: NodeIndex,
	},

	/// The node works but we can't do anything useful with it.
	UselessNode {
		/// Index of the node.
		node_index: NodeIndex,
	},

	/// Opened a Kademlia substream with the node.
	// TODO: the controller API is bad, but we need to make changes in libp2p to improve that
	KadOpen {
		/// Index of the node.
		node_index: NodeIndex,
		/// The Kademlia controller. Allows making queries.
		controller: KadConnecController,
	},

	/// The remote wants us to answer a Kademlia `FIND_NODE` request.
	///
	/// The `responder` should be used to answer that query.
	// TODO: this API with the "responder" is bad, but changing it requires modifications in libp2p
	KadFindNode {
		/// Index of the node that wants an answer.
		node_index: NodeIndex,
		/// The value being searched.
		searched: PeerId,
		/// Object to use to respond to the request.
		responder: KadFindNodeRespond,
	},

	/// A Kademlia substream has been closed.
	KadClosed {
		/// Index of the node.
		node_index: NodeIndex,
		/// Reason why it has been closed. `Ok` means that it's been closed gracefully.
		result: Result<(), IoError>,
	},
}

/// Network swarm. Must be polled regularly in order for the networking to work.
pub struct Swarm {
	/// Stream of events of the swarm.
	swarm: Libp2pSwarm<
		Boxed<(PeerId, Muxer)>,
		SubstrateInEvent,
		SubstrateOutEvent<Substream<Muxer>>,
		HandlerBuilder
	>,

	/// Public key of the local node.
	local_public_key: PublicKey,

	/// Peer id of the local node.
	local_peer_id: PeerId,

	/// Addresses we know we're listening on. Only includes NAT traversed addresses.
	listening_addrs: Vec<Multiaddr>,

	/// For each peer id, the corresponding node index.
	node_by_peer: FnvHashMap<PeerId, NodeIndex>,

	/// All the nodes tasks. Must be maintained consistent with `node_by_peer`.
	nodes_info: FnvHashMap<NodeIndex, NodeInfo>,

	/// Next key to use when we insert a new entry in `nodes_info`.
	next_node_index: NodeIndex,
}

/// Local information about a peer.
struct NodeInfo {
	/// The peer id. Must be maintained consistent with the rest of the state.
	peer_id: PeerId,

	/// Whether we opened the connection or the remote opened it.
	endpoint: Endpoint,

	/// List of custom protocol substreams that are open.
	open_protocols: Vec<ProtocolId>,
}

/// The muxer used by the transport.
type Muxer = muxing::StreamMuxerBox;

impl Swarm {
	/// Start listening on a multiaddr.
	#[inline]
	pub fn listen_on(&mut self, addr: Multiaddr) -> Result<Multiaddr, Multiaddr> {
		match self.swarm.listen_on(addr) {
			Ok(mut addr) => {
				addr.append(Protocol::P2p(self.local_peer_id.clone().into()));
				info!(target: "sub-libp2p", "Local node address is: {}", addr);
				Ok(addr)
			},
			Err(addr) => Err(addr)
		}
	}

    /// Returns an iterator that produces the list of addresses we're listening on.
    #[inline]
    pub fn listeners(&self) -> impl Iterator<Item = &Multiaddr> {
        self.swarm.listeners()
    }

	/// Adds an external address. Sent to other nodes when they query it.
	#[inline]
	pub fn add_external_address(&mut self, addr: Multiaddr) {
		self.listening_addrs.push(addr);
	}

	/// Returns an iterator to our known external addresses.
	#[inline]
	pub fn external_addresses(&self) -> impl Iterator<Item = &Multiaddr> {
		self.listening_addrs.iter()
	}

	/// Returns all the nodes that are currently active.
	#[inline]
	pub fn nodes<'a>(&'a self) -> impl Iterator<Item = NodeIndex> + 'a {
		self.nodes_info.keys().cloned()
	}

	/// Returns the latest node connected to this peer ID.
	#[inline]
	pub fn latest_node_by_peer_id(&self, peer_id: &PeerId) -> Option<NodeIndex> {
		self.node_by_peer.get(peer_id).map(|&i| i)
	}

	/// Endpoint of the node.
	///
	/// Returns `None` if the index is invalid.
	#[inline]
	pub fn node_endpoint(&self, node_index: NodeIndex) -> Option<Endpoint> {
		self.nodes_info.get(&node_index).map(|i| i.endpoint)
	}

	/// Sends a message to a peer using the custom protocol.
	// TODO: report invalid node index or protocol?
	pub fn send_custom_message(
		&mut self,
		node_index: NodeIndex,
		protocol: ProtocolId,
		data: Vec<u8>
	) {
		if let Some(info) = self.nodes_info.get_mut(&node_index) {
			if let Some(mut connected) = self.swarm.peer(info.peer_id.clone()).as_connected() {
				connected.send_event(SubstrateInEvent::SendCustomMessage { protocol, data });
			} else {
				error!(target: "sub-libp2p", "Tried to send message to {:?}, but we're not \
					connected to it", info.peer_id);
			}
		} else {
			error!(target: "sub-libp2p", "Tried to send message to invalid node index {:?}",
				node_index);
		}
	}

	/// Returns the peer id of a node we're connected to.
	#[inline]
	pub fn peer_id_of_node(&self, node_index: NodeIndex) -> Option<&PeerId> {
		self.nodes_info.get(&node_index).map(|i| &i.peer_id)
	}

	/// If we're not already dialing the given peer, start dialing it and return false.
	/// If we're dialing, adds the address to the queue of addresses to try (if not already) and
	/// return false.
	/// If we're already connected, do nothing and return true.
	///
	/// Returns an error if the address is not supported.
	pub fn ensure_connection(&mut self, peer_id: PeerId, addr: Multiaddr) -> Result<bool, ()> {
		match self.swarm.peer(peer_id.clone()) {
			SwarmPeer::Connected(_) => Ok(true),
			SwarmPeer::PendingConnect(mut peer) => {
				peer.append_multiaddr_attempt(addr);
				Ok(false)
			},
			SwarmPeer::NotConnected(peer) => {
				trace!(target: "sub-libp2p", "Starting to connect to {:?} through {}",
					peer_id, addr);
				match peer.connect(addr) {
					Ok(_) => Ok(false),
					Err(_) => Err(()),
				}
			},
		}
	}

	/// Start dialing an address, not knowing which peer ID to expect.
	#[inline]
	pub fn dial(&mut self, addr: Multiaddr) -> Result<(), Multiaddr> {
		self.swarm.dial(addr)
	}

	/// After receiving a `NodePending` event, you should call either `accept_node` or `drop_node`
	/// with the specified index.
	///
	/// Returns an error if the node index is invalid, or if it was already accepted.
	pub fn accept_node(&mut self, node_index: NodeIndex) -> Result<(), ()> {
		// TODO: detect if already accepted?
		let peer_id = match self.nodes_info.get(&node_index) {
			Some(info) => &info.peer_id,
			None => return Err(())
		};

		match self.swarm.peer(peer_id.clone()) {
			SwarmPeer::Connected(mut peer) => {
				peer.send_event(SubstrateInEvent::Accept);
				Ok(())
			},
			SwarmPeer::PendingConnect(_) | SwarmPeer::NotConnected(_) => {
				error!(target: "sub-libp2p", "State inconsistency detected in accept_node ; \
					nodes_info is not in sync with the underlying swarm");
				Err(())
			},
		}
	}

	/// Disconnects a peer.
	///
	/// If the peer is connected, this disconnects it.
	/// If the peer hasn't been accepted yet, this immediately drops it.
	///
	/// Returns the list of custom protocol substreams that were opened.
	#[inline]
	pub fn drop_node(&mut self, node_index: NodeIndex) -> Result<Vec<ProtocolId>, ()> {
		let info = match self.nodes_info.remove(&node_index) {
			Some(i) => i,
			None => {
				error!(target: "sub-libp2p", "Trying to close non-existing node #{}", node_index);
				return Err(());
			},
		};

		let idx_in_hashmap = self.node_by_peer.remove(&info.peer_id);
		debug_assert_eq!(idx_in_hashmap, Some(node_index));

		if let Some(connected) = self.swarm.peer(info.peer_id.clone()).as_connected() {
			connected.close();
		} else {
			error!(target: "sub-libp2p", "State inconsistency: node_by_peer and nodes_info are \
				not in sync with the underlying swarm");
		}

		Ok(info.open_protocols)
	}

	/// Opens a Kademlia substream with the given node. A `KadOpen` event will later be produced
	/// for the given node.
	///
	/// If a Kademlia substream is already open, also produces a `KadOpen` event.
	///
	/// Returns an error if the node index is invalid.
	pub fn open_kademlia(&mut self, node_index: NodeIndex) -> Result<(), ()> {
		if let Some(info) = self.nodes_info.get_mut(&node_index) {
			if let Some(mut connected) = self.swarm.peer(info.peer_id.clone()).as_connected() {
				connected.send_event(SubstrateInEvent::OpenKademlia);
				Ok(())
			} else {
				error!(target: "sub-libp2p", "Tried to open Kademlia with {:?}, but we're not \
					connected to it", info.peer_id);
				Err(())
			}
		} else {
			error!(target: "sub-libp2p", "Tried to open Kademlia with invalid node index {:?}",
				node_index);
			Err(())
		}
	}

	/// Adds an address the given peer observes us as.
	fn add_observed_addr(&mut self, peer_id: &PeerId, observed_addr: &Multiaddr) {
		for mut addr in self.swarm.nat_traversal(observed_addr) {
			// Ignore addresses we already know about.
			if self.listening_addrs.iter().any(|a| a == &addr) {
				continue;
			}

			debug!(target: "sub-libp2p",
				"NAT traversal: {:?} observes us as {}; registering {} as one of our own addresses",
				peer_id,
				observed_addr,
				addr
			);

			self.listening_addrs.push(addr.clone());
			addr.append(Protocol::P2p(self.local_peer_id.clone().into()));
			info!(target: "sub-libp2p", "New external node address: {}", addr);
		}
	}

	/// Responds to an answer to send back identification information.
	fn respond_to_identify_request(
		&mut self,
		requester: &PeerId,
		responder: IdentificationRequest<Substream<Muxer>>
	) {
		let peer = match self.swarm.peer(requester.clone()).as_connected() {
			Some(p) => p,
			None => {
				debug!(target: "sub-libp2p", "Ignoring identify request from {:?} because we are \
					disconnected", requester);
				return;
			}
		};

		let observed_addr = match peer.endpoint() {
			&ConnectedPoint::Dialer { ref address } => address,
			&ConnectedPoint::Listener { ref send_back_addr, .. } => send_back_addr,
		};

		trace!(target: "sub-libp2p", "Responding to identify request from {:?}", requester);
		responder.respond(
			self.local_public_key.clone(),
			self.listening_addrs.clone(),
			&observed_addr,
		);
	}

	/// Processes an event received by the swarm.
	///
	/// Optionally returns an event to report back to the outside.
	///
	/// > **Note**: Must be called from inside `poll()`, otherwise it will panic. This method
	/// > shouldn't be made public because of this requirement.
	fn process_network_event(
		&mut self,
		event: Libp2pSwarmEvent<Boxed<(PeerId, Muxer)>, SubstrateOutEvent<Substream<Muxer>>>
	) -> Option<SwarmEvent> {
		match event {
			Libp2pSwarmEvent::Connected { peer_id, endpoint } => {
				let node_index = self.next_node_index.clone();
				self.next_node_index += 1;
				self.node_by_peer.insert(peer_id.clone(), node_index);
				self.nodes_info.insert(node_index, NodeInfo {
					peer_id: peer_id.clone(),
					endpoint: match endpoint {
						ConnectedPoint::Listener { .. } => Endpoint::Listener,
						ConnectedPoint::Dialer { .. } => Endpoint::Dialer,
					},
					open_protocols: Vec::new(),
				});

				return Some(SwarmEvent::NodePending {
					node_index,
					peer_id,
					endpoint
				});
			}
			Libp2pSwarmEvent::Replaced { peer_id, endpoint, .. } => {
				let node_index = *self.node_by_peer.get(&peer_id)
					.expect("node_by_peer is always kept in sync with the inner swarm");
				let infos = self.nodes_info.get_mut(&node_index)
					.expect("nodes_info is always kept in sync with the swarm");
				debug_assert_eq!(infos.peer_id, peer_id);
				infos.endpoint = match endpoint {
					ConnectedPoint::Listener { .. } => Endpoint::Listener,
					ConnectedPoint::Dialer { .. } => Endpoint::Dialer,
				};
				let closed_custom_protocols = mem::replace(&mut infos.open_protocols, Vec::new());

				return Some(SwarmEvent::Reconnected {
					node_index,
					endpoint,
					closed_custom_protocols,
				});
			},
			Libp2pSwarmEvent::NodeClosed { peer_id, .. } => {
				debug!(target: "sub-libp2p", "Connection to {:?} closed gracefully", peer_id);
				let node_index = self.node_by_peer.remove(&peer_id)
					.expect("node_by_peer is always kept in sync with the inner swarm");
				let infos = self.nodes_info.remove(&node_index)
					.expect("nodes_info is always kept in sync with the inner swarm");
				debug_assert_eq!(infos.peer_id, peer_id);
				return Some(SwarmEvent::NodeClosed {
					node_index,
					peer_id,
					closed_custom_protocols: infos.open_protocols,
				});
			},
			Libp2pSwarmEvent::NodeError { peer_id, error, .. } => {
				debug!(target: "sub-libp2p", "Closing {:?} because of error: {:?}", peer_id, error);
				let node_index = self.node_by_peer.remove(&peer_id)
					.expect("node_by_peer is always kept in sync with the inner swarm");
				let infos = self.nodes_info.remove(&node_index)
					.expect("nodes_info is always kept in sync with the inner swarm");
				debug_assert_eq!(infos.peer_id, peer_id);
				return Some(SwarmEvent::NodeClosed {
					node_index,
					peer_id,
					closed_custom_protocols: infos.open_protocols,
				});
			},
			Libp2pSwarmEvent::DialError { multiaddr, error, .. } =>
				return Some(SwarmEvent::DialFail {
					address: multiaddr,
					error,
				}),
			Libp2pSwarmEvent::UnknownPeerDialError { multiaddr, error } =>
				return Some(SwarmEvent::DialFail {
					address: multiaddr,
					error,
				}),
			Libp2pSwarmEvent::PublicKeyMismatch {
				actual_peer_id,
				multiaddr,
				expected_peer_id,
				..
			} => {
				debug!(target: "sub-libp2p", "When dialing {:?} through {}, public key mismatch, \
					actual = {:?}", expected_peer_id, multiaddr, actual_peer_id);
				return Some(SwarmEvent::DialFail {
					address: multiaddr,
					error: IoError::new(IoErrorKind::Other, "Public key mismatch"),
				});
			},
			Libp2pSwarmEvent::ListenerClosed { listen_addr, result, .. } => {
				warn!(target: "sub-libp2p", "Listener closed for {}: {:?}", listen_addr, result);
				if self.swarm.listeners().count() == 0 {
					warn!(target: "sub-libp2p", "No listener left");
				}
			},
			Libp2pSwarmEvent::NodeEvent { peer_id, event } =>
				if let Some(event) = self.handle_node_event(peer_id, event) {
					return Some(event);
				},
			Libp2pSwarmEvent::IncomingConnection { listen_addr, send_back_addr } =>
				trace!(target: "sub-libp2p", "Incoming connection with {} on listener {}",
					send_back_addr, listen_addr),
			Libp2pSwarmEvent::IncomingConnectionError { listen_addr, send_back_addr, error } =>
				trace!(target: "sub-libp2p", "Incoming connection with {} on listener {} \
					errored: {:?}", send_back_addr, listen_addr, error),
		}

		None
	}

	/// Processes an event obtained by a node in the swarm.
	///
	/// Optionally returns an event that the service must emit.
	///
	/// > **Note**: The event **must** have been produced by the swarm, otherwise state
	/// > inconsistencies will likely happen.
	fn handle_node_event(
		&mut self,
		peer_id: PeerId,
		event: SubstrateOutEvent<Substream<Muxer>>
	) -> Option<SwarmEvent> {
		// Obtain the peer id and whether the node has been closed earlier.
		// If the node has been closed, do not generate any additional event about it.
		let node_index = *self.node_by_peer.get(&peer_id)
			.expect("node_by_peer is always kept in sync with the underlying swarm");

		match event {
			SubstrateOutEvent::Unresponsive => {
				debug!(target: "sub-libp2p", "Node {:?} is unresponsive", peer_id);
				Some(SwarmEvent::UnresponsiveNode { node_index })
			},
			SubstrateOutEvent::Useless => {
				debug!(target: "sub-libp2p", "Node {:?} is useless", peer_id);
				Some(SwarmEvent::UselessNode { node_index })
			},
			SubstrateOutEvent::PingStart => {
				trace!(target: "sub-libp2p", "Pinging {:?}", peer_id);
				None
			},
			SubstrateOutEvent::PingSuccess(ping) => {
				trace!(target: "sub-libp2p", "Pong from {:?} in {:?}", peer_id, ping);
				None
			},
			SubstrateOutEvent::Identified { info, observed_addr } => {
				self.add_observed_addr(&peer_id, &observed_addr);
				trace!(target: "sub-libp2p", "Client version of {:?}: {:?}", peer_id, info.agent_version);
				if !info.agent_version.contains("substrate") {
					info!(target: "sub-libp2p", "Connected to non-substrate node {:?}: {}",
						peer_id, info.agent_version);
				}

				Some(SwarmEvent::NodeInfos {
					node_index,
					client_version: info.agent_version,
					listen_addrs: info.listen_addrs,
				})
			},
			SubstrateOutEvent::IdentificationRequest(request) => {
				self.respond_to_identify_request(&peer_id, request);
				None
			},
			SubstrateOutEvent::KadFindNode { searched, responder } => {
				Some(SwarmEvent::KadFindNode { node_index, searched, responder })
			},
			SubstrateOutEvent::KadOpen(ctrl) => {
				trace!(target: "sub-libp2p", "Opened Kademlia substream with {:?}", peer_id);
				Some(SwarmEvent::KadOpen { node_index, controller: ctrl })
			},
			SubstrateOutEvent::KadClosed(result) => {
				trace!(target: "sub-libp2p", "Closed Kademlia substream with {:?}: {:?}", peer_id, result);
				Some(SwarmEvent::KadClosed { node_index, result })
			},
			SubstrateOutEvent::CustomProtocolOpen { protocol_id, version } => {
				trace!(target: "sub-libp2p", "Opened custom protocol with {:?}", peer_id);
				self.nodes_info.get_mut(&node_index)
					.expect("nodes_info is kept in sync with the underlying swarm")
					.open_protocols.push(protocol_id);
				Some(SwarmEvent::OpenedCustomProtocol {
					node_index,
					protocol: protocol_id,
					version,
				})
			},
			SubstrateOutEvent::CustomProtocolClosed { protocol_id, result } => {
				trace!(target: "sub-libp2p", "Closed custom protocol with {:?}: {:?}", peer_id, result);
				self.nodes_info.get_mut(&node_index)
					.expect("nodes_info is kept in sync with the underlying swarm")
					.open_protocols.retain(|p| p != &protocol_id);
				Some(SwarmEvent::ClosedCustomProtocol {
					node_index,
					protocol: protocol_id,
				})
			},
			SubstrateOutEvent::CustomMessage { protocol_id, data } => {
				Some(SwarmEvent::CustomMessage {
					node_index,
					protocol_id,
					data,
				})
			},
			SubstrateOutEvent::SubstreamUpgradeFail(err) => {
				debug!(target: "sub-libp2p", "Error while negotiating final protocol \
					with {:?}: {:?}", peer_id, err);
				None
			},
		}
	}
}

impl Stream for Swarm {
	type Item = SwarmEvent;
	type Error = IoError;

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		loop {
			match self.swarm.poll() {
				Async::Ready(Some(event)) =>
					if let Some(event) = self.process_network_event(event) {
						return Ok(Async::Ready(Some(event)));
					}
				Async::NotReady => return Ok(Async::NotReady),
				Async::Ready(None) => unreachable!("The Swarm stream never ends"),
			}
		}
	}
}
