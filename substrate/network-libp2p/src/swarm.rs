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
use futures::{prelude::*, Stream, sync::mpsc, task};
use libp2p::{Multiaddr, multiaddr::AddrComponent, PeerId};
use libp2p::core::{muxing, Endpoint, PublicKey};
use libp2p::core::nodes::node::Substream;
use libp2p::core::nodes::swarm::{ConnectedPoint, Swarm as Libp2pSwarm};
use libp2p::core::nodes::swarm::{SwarmEvent as Libp2pSwarmEvent, Peer as SwarmPeer};
use libp2p::core::transport::boxed::Boxed;
use libp2p::kad::{KadConnecController, KadFindNodeRespond};
use libp2p::secio;
use node_handler::{NodeEvent, NodeHandler, IdentificationRequest};
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
use std::mem;
use std::sync::Arc;
use std::time::Duration;
use tokio_executor;
use transport;
use {Error, NodeIndex, PacketId, ProtocolId};

/// Starts a swarm.
///
/// Returns a stream that must be polled regularly in order for the networking to function.
pub fn start_swarm<TUserData>(
	registered_custom: Arc<RegisteredProtocols<TUserData>>,
	local_private_key: secio::SecioKeyPair,
) -> Result<Swarm<TUserData>, Error> {
	// Private and public keys.
	let local_public_key = local_private_key.to_public_key();
	let local_peer_id = local_public_key.clone().into_peer_id();

	// Build the transport layer. This is what allows us to listen or to reach nodes.
	let transport = transport::build_transport(local_private_key);

	// Build the underlying libp2p swarm.
	let swarm = Libp2pSwarm::new(transport);

	let (node_tasks_events_tx, node_tasks_events_rx) = mpsc::unbounded();
	Ok(Swarm {
		swarm,
		local_public_key,
		local_peer_id,
		listening_addrs: Vec::new(),
		registered_custom,
		node_by_peer: Default::default(),
		nodes_info: Default::default(),
		next_node_index: 0,
		node_tasks_events_rx,
		node_tasks_events_tx,
		tasks_to_spawn: Vec::new(),
		to_notify: None,
	})
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

	/// Closed connection to a node.
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

	/// Report the duration of the ping for the given node.
	PingDuration(NodeIndex, Duration),

	/// Report the address of a node if it was not previously known.
	NodeAddress {
		/// Index of the node.
		node_index: NodeIndex,
		/// Address of the node.
		address: Multiaddr,
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
		/// Identifier of the packet.
		packet_id: u8,
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
pub struct Swarm<TUserData> {
	/// Stream of events of the swarm.
	swarm: Libp2pSwarm<Boxed<(PeerId, Muxer)>, Muxer, ()>,

	/// Public key of the local node.
	local_public_key: PublicKey,

	/// Peer id of the local node.
	local_peer_id: PeerId,

	/// Addresses we know we're listening on. Only includes NAT traversed addresses.
	listening_addrs: Vec<Multiaddr>,

	/// List of registered custom protocols.
	registered_custom: Arc<RegisteredProtocols<TUserData>>,

	/// For each peer id, the corresponding node index.
	/// This is filled when the swarm receives a node, and is emptied when the node handler closes.
	///
	/// Note that we may temporarily have multiple node indices pointing to the same peer ID. This
	/// hash map only contains the latest node for each given peer.
	/// Nodes that are not in this list should all be in the closing state.
	node_by_peer: FnvHashMap<PeerId, NodeIndex>,

	/// All the nodes tasks. Must be maintained consistent with `node_by_peer`.
	///
	/// # How it works
	///
	/// First, the `swarm` generates events about connected nodes. This creates an entry in
	/// `nodes_info` and `node_by_peer`, where the node is in pending mode. Accepting the node
	/// spawns a background task and puts a sender in `nodes_info`.
	///
	/// If the `swarm` tells us that a node is closed, or if the user wants to drop a peer, we
	/// destroy that sender, which tells the background task that it needs to stop.
	///
	/// Once the background task stops, we remove the entries in `node_by_peer` and `nodes_info`.
	///
	/// In order to maintain a consistent state, at no point we should close the sender without
	/// removing the peer from the nework first (removing a peer from the network is
	/// instantaneous), and at no point should we remove entries before the background task is
	/// stopped.
	nodes_info: FnvHashMap<NodeIndex, NodeInfo>,

	/// Next key to use when we insert a new entry in `nodes_info`.
	next_node_index: NodeIndex,

	/// Events received by the node tasks. If `None`, means that the task finished for this node.
	node_tasks_events_rx: mpsc::UnboundedReceiver<(NodeIndex, Option<NodeEvent<Substream<Muxer>>>)>,

	/// Sending side of `node_tasks_events_rx`. Meant to be cloned and sent to background tasks.
	node_tasks_events_tx: mpsc::UnboundedSender<(NodeIndex, Option<NodeEvent<Substream<Muxer>>>)>,

	/// List of tasks to spawn when we're in a polling context.
	tasks_to_spawn: Vec<NodeTask<TUserData>>,

	/// Task to notify when an element is added to `tasks_to_spawn`.
	to_notify: Option<task::Task>,
}

/// Local information about a peer.
struct NodeInfo {
	/// The peer id. Must be maintained consistent with the rest of the state.
	peer_id: PeerId,

	/// Whether we opened the connection or the remote opened it.
	endpoint: Endpoint,

	/// State of the node.
	state: NodeState,

	/// List of custom protocol substreams that are open.
	open_protocols: Vec<ProtocolId>,
}

/// State of the node.
enum NodeState {
	/// The node is waiting to be accepted or denied.
	/// Contains both ends of a channel, so that we can start appending messages that will be
	/// processed once the node gets accepted.
	Pending(mpsc::UnboundedSender<OutToTaskMsg>, mpsc::UnboundedReceiver<OutToTaskMsg>),

	/// The node is active. The sender can be used to dispatch messages to the background task.
	/// Destroying the sender will close the background task.
	Accepted(mpsc::UnboundedSender<OutToTaskMsg>),

	/// The node is closing. We dropped the sender, and thus.
	Closing,

	/// The node has been closed by calling `drop_node`. Same as `closing`, except that we must
	/// must not generate any event about this node anymore.
	Closed,
}

impl NodeState {
	/// Returns the inner sender, if any.
	#[inline]
	fn as_sender(&mut self) -> Option<&mut mpsc::UnboundedSender<OutToTaskMsg>> {
		match *self {
			NodeState::Pending(ref mut tx, _) => Some(tx),
			NodeState::Accepted(ref mut tx) => Some(tx),
			NodeState::Closing => None,
			NodeState::Closed => None,
		}
	}

	/// Returns `true` for `NodeState::Closed`.
	#[inline]
	fn is_closed(&self) -> bool {
		match *self {
			NodeState::Pending(_, _) => false,
			NodeState::Accepted(_) => false,
			NodeState::Closing => false,
			NodeState::Closed => true,
		}
	}

	/// Switches the state to `Closing`, unless we're already closing or closed.
	#[inline]
	fn close_if_necessary(&mut self) {
		match *self {
			NodeState::Pending(_, _) | NodeState::Accepted(_) => (),
			NodeState::Closing | NodeState::Closed => return,
		};

		*self = NodeState::Closing;
	}
}

/// Message from the service to one of the background node tasks.
enum OutToTaskMsg {
	/// Must call `inject_substream()` on the node handler.
	InjectSubstream {
		substream: Substream<muxing::StreamMuxerBox>,
		endpoint: Endpoint,
	},

	/// Must call `open_kademlia()` on the node handler.
	OpenKademlia,

	/// Must call `send_custom_message()` on the node handler.
	SendCustomMessage {
		protocol: ProtocolId,
		packet_id: PacketId,
		data: Vec<u8>,
	},
}

type Muxer = muxing::StreamMuxerBox;

impl<TUserData> Swarm<TUserData>
	where TUserData: Clone + Send + Sync + 'static {
	/// Start listening on a multiaddr.
	#[inline]
	pub fn listen_on(&mut self, addr: Multiaddr) -> Result<Multiaddr, Multiaddr> {
		match self.swarm.listen_on(addr) {
			Ok(mut addr) => {
				addr.append(AddrComponent::P2P(self.local_peer_id.clone().into()));
				info!(target: "sub-libp2p", "Local node address is: {}", addr);
				Ok(addr)
			},
			Err(addr) => Err(addr)
		}
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
		packet_id: PacketId,
		data: Vec<u8>
	) {
		if let Some(info) = self.nodes_info.get_mut(&node_index) {
			if let Some(ref mut sender) = info.state.as_sender() {
				let msg = OutToTaskMsg::SendCustomMessage { protocol, packet_id, data };
				let _ = sender.unbounded_send(msg);
			}
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
	#[inline]
	pub fn accept_node(&mut self, node_index: NodeIndex) -> Result<(), ()> {
		let info = match self.nodes_info.get_mut(&node_index) {
			Some(i) => i,
			None => return Err(()),
		};

		let out_commands_rx = match mem::replace(&mut info.state, NodeState::Closing) {
			NodeState::Pending(tx, rx) => {
				info.state = NodeState::Accepted(tx);
				rx
			},
			other => {
				info.state = other;
				return Err(())
			},
		};

		self.tasks_to_spawn.push(NodeTask {
			node_index,
			handler: Some(NodeHandler::new(self.registered_custom.clone())),
			out_commands_rx,
			node_tasks_events_tx: self.node_tasks_events_tx.clone(),
		});

		if let Some(to_notify) = self.to_notify.take() {
			to_notify.notify();
		}

		Ok(())
	}

	/// Disconnects a peer.
	///
	/// If the peer is connected, this disconnects it.
	/// If the peer hasn't been accepted yet, this immediately drops it.
	///
	/// Returns the list of custom protocol substreams that were opened.
	#[inline]
	pub fn drop_node(&mut self, node_index: NodeIndex) -> Result<Vec<ProtocolId>, ()> {
		let mut must_remove = false;

		let ret = {
			let info = match self.nodes_info.get_mut(&node_index) {
				Some(i) => i,
				None => {
					error!(target: "sub-libp2p", "Trying to close non-existing node #{}", node_index);
					return Err(());
				},
			};

			if let Some(connected) = self.swarm.peer(info.peer_id.clone()).as_connected() {
				connected.close();
			}

			// If we don't have a background task yet, remove the entry immediately.
			if let NodeState::Pending(_, _) = info.state {
				must_remove = true;
				Vec::new()
			} else {
				// There may be events pending on the rx side about this node, so we switch it to
				// the `Closed` state in order to know not emit any more event about it.
				info.state = NodeState::Closed;
				info.open_protocols.clone()
			}
		};

		if must_remove {
			let info = self.nodes_info.remove(&node_index)
				.expect("We checked the key a few lines above");
			self.node_by_peer.remove(&info.peer_id);
		}

		Ok(ret)
	}

	/// Opens a Kademlia substream with the given node. A `KadOpen` event will later be produced
	/// for the given node.
	///
	/// If a Kademlia substream is already open, also produces a `KadOpen` event.
	///
	/// Returns an error if the node index is invalid.
	pub fn open_kademlia(&mut self, node_index: NodeIndex) -> Result<(), ()> {
		if let Some(info) = self.nodes_info.get_mut(&node_index) {
			if let Some(ref mut sender) = info.state.as_sender() {
				let _ = sender.unbounded_send(OutToTaskMsg::OpenKademlia);
				Ok(())
			} else {
				Err(())
			}
		} else {
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
			addr.append(AddrComponent::P2P(self.local_peer_id.clone().into()));
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

		if let Some(address) = peer.multiaddr() {
			trace!(target: "sub-libp2p", "Responding to identify request from {:?}", requester);
			responder.respond(
				self.local_public_key.clone(),
				self.listening_addrs.clone(),
				&address,
			);
		} else {
			// TODO: we have the problem that we don't know the address of the remote instantly
			// even though we could ; making this properly requires a lot of changes in libp2p
			debug!(target: "sub-libp2p", "Ignoring identify request from {:?} because we its \
				address is not known yet", requester);
		}
	}

	/// Handles the swarm opening a connection to the given peer.
	///
	/// Returns the `NewNode` event to produce.
	///
	/// > **Note**: Must be called from inside `poll()`, otherwise it will panic. This method
	/// > shouldn't be made public because of this requirement.
	fn handle_connection(
		&mut self,
		peer_id: PeerId,
		endpoint: ConnectedPoint
	) -> Option<SwarmEvent> {
		let (tx, rx) = mpsc::unbounded();

		// Assign the node index.
		let node_index = self.next_node_index.clone();
		self.next_node_index += 1;
		self.node_by_peer.insert(peer_id.clone(), node_index);
		self.nodes_info.insert(node_index, NodeInfo {
			peer_id: peer_id.clone(),
			endpoint: match endpoint {
				ConnectedPoint::Listener { .. } => Endpoint::Listener,
				ConnectedPoint::Dialer { .. } => Endpoint::Dialer,
			},
			state: NodeState::Pending(tx, rx),
			open_protocols: Vec::new(),
		});

		Some(SwarmEvent::NodePending {
			node_index,
			peer_id,
			endpoint
		})
	}

	/// Handles a swarm event about a newly-opened substream for the given peer.
	///
	/// Dispatches the substream to the corresponding task.
	fn handle_new_substream(
		&mut self,
		peer_id: PeerId,
		substream: Substream<Muxer>,
		endpoint: Endpoint,
	) {
		let node_index = match self.node_by_peer.get(&peer_id) {
			Some(i) => *i,
			None => {
				error!(target: "sub-libp2p", "Logic error: new substream for closed node");
				return
			},
		};

		let info = match self.nodes_info.get_mut(&node_index) {
			Some(i) => i,
			None => {
				error!(target: "sub-libp2p", "Logic error: new substream for closed node");
				return
			},
		};

		if let Some(ref mut sender) = info.state.as_sender() {
			let _ = sender.unbounded_send(OutToTaskMsg::InjectSubstream {
				substream,
				endpoint,
			});
		} else {
			error!(target: "sub-libp2p", "Logic error: no background task for {:?}", peer_id);
		}
	}

	/// Processes an event received by the swarm.
	///
	/// Optionally returns an event to report back to the outside.
	///
	/// > **Note**: Must be called from inside `poll()`, otherwise it will panic. This method
	/// > shouldn't be made public because of this requirement.
	fn process_network_event(
		&mut self,
		event: Libp2pSwarmEvent<Boxed<(PeerId, Muxer)>, Muxer, ()>
	) -> Option<SwarmEvent> {
		match event {
			Libp2pSwarmEvent::Connected { peer_id, endpoint } =>
				if let Some(event) = self.handle_connection(peer_id, endpoint) {
					return Some(event);
				},
			Libp2pSwarmEvent::Replaced { peer_id, endpoint, .. } => {
				let node_index = *self.node_by_peer.get(&peer_id).expect("State inconsistency");
				self.nodes_info.get_mut(&node_index).expect("State inconsistency")
					.state.close_if_necessary();
				if let Some(event) = self.handle_connection(peer_id, endpoint) {
					return Some(event);
				}
			},
			Libp2pSwarmEvent::NodeClosed { peer_id, .. } => {
				debug!(target: "sub-libp2p", "Connection to {:?} closed gracefully", peer_id);
				let node_index = *self.node_by_peer.get(&peer_id).expect("State inconsistency");
				self.nodes_info.get_mut(&node_index).expect("State inconsistency")
					.state.close_if_necessary();
			},
			Libp2pSwarmEvent::NodeError { peer_id, error, .. } => {
				debug!(target: "sub-libp2p", "Closing {:?} because of error: {:?}", peer_id, error);
				let node_index = *self.node_by_peer.get(&peer_id).expect("State inconsistency");
				self.nodes_info.get_mut(&node_index).expect("State inconsistency")
					.state.close_if_necessary();
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
			Libp2pSwarmEvent::NodeMultiaddr { peer_id, address: Ok(address) } => {
				trace!(target: "sub-libp2p", "Determined the multiaddr of {:?} => {}",
					peer_id, address);
				if let Some(&node_index) = self.node_by_peer.get(&peer_id) {
					return Some(SwarmEvent::NodeAddress {
						node_index,
						address,
					});
				} else {
					error!(target: "sub-libp2p", "Logic error: no index for {:?}", peer_id);
				}
			},
			Libp2pSwarmEvent::NodeMultiaddr { peer_id, address: Err(err) } =>
				trace!(target: "sub-libp2p", "Error when determining the multiaddr of {:?} => {:?}",
					peer_id, err),
			Libp2pSwarmEvent::IncomingConnection { listen_addr } =>
				trace!(target: "sub-libp2p", "Incoming connection on listener {}", listen_addr),
			Libp2pSwarmEvent::IncomingConnectionError { listen_addr, error } =>
				trace!(target: "sub-libp2p", "Incoming connection on listener {} errored: {:?}",
					listen_addr, error),
			Libp2pSwarmEvent::InboundSubstream { peer_id, substream } =>
				self.handle_new_substream(peer_id, substream, Endpoint::Listener),
			Libp2pSwarmEvent::OutboundSubstream { peer_id, substream, .. } =>
				self.handle_new_substream(peer_id, substream, Endpoint::Dialer),
			Libp2pSwarmEvent::InboundClosed { .. } => {},
			Libp2pSwarmEvent::OutboundClosed { .. } => {},
		}

		None
	}

	/// Polls for what happened on the main network side.
	fn poll_network(&mut self) -> Poll<Option<SwarmEvent>, IoError> {
		loop {
			match self.swarm.poll() {
				Ok(Async::Ready(Some(event))) =>
					if let Some(event) = self.process_network_event(event) {
						return Ok(Async::Ready(Some(event)));
					}
				Ok(Async::NotReady) => return Ok(Async::NotReady),
				Ok(Async::Ready(None)) => unreachable!("The Swarm stream never ends"),
				// TODO: this `Err` contains a `Void` ; remove variant when Rust allows that
				Err(_) => unreachable!("The Swarm stream never errors"),
			}
		}
	}

	/// Polls for what happened on the background node tasks.
	fn poll_node_tasks(&mut self) -> Poll<Option<SwarmEvent>, IoError> {
		loop {
			match self.node_tasks_events_rx.poll() {
				Ok(Async::NotReady) => return Ok(Async::NotReady),
				Ok(Async::Ready(Some((node_index, event)))) =>
					if let Some(event) = self.handle_node_event(node_index, event) {
						return Ok(Async::Ready(Some(event)));
					},
				Ok(Async::Ready(None)) => unreachable!("The tx is in self so the rx never closes"),
				Err(()) => unreachable!("An UnboundedReceiver never errors"),
			}
		}
	}

	/// Processes an event obtained by a node background task.
	///
	/// If the `event` is `None`, that means that the background task finished.
	///
	/// Optionally returns an event that the service must emit.
	///
	/// > **Note**: The event **must** have been produced by a background task, otherwise state
	/// > inconsistencies will likely happen.
	fn handle_node_event(
		&mut self,
		node_index: NodeIndex,
		event: Option<NodeEvent<Substream<Muxer>>>
	) -> Option<SwarmEvent> {
		// Obtain the peer id and whether the node has been closed earlier.
		// If the node has been closed, do not generate any additional event about it.
		let (peer_id, node_is_closed) = {
			let info = self.nodes_info.get_mut(&node_index)
				.expect("Handlers are created when we fill nodes_info, and nodes_info is cleared \
						only when a background task ends");
			(info.peer_id.clone(), info.state.is_closed())
		};

		match event {
			None => {
				let _info = self.nodes_info.remove(&node_index).expect("Inconsistent state");
				// It is possible that the entry in `node_by_peer` doesn't match our node, if a new
				// node was created with the same peer.
				if self.node_by_peer.get(&peer_id) == Some(&node_index) {
					self.node_by_peer.remove(&peer_id);
				}

				// Only generate an event if `drop_node` hasn't been called with this node index.
				if !node_is_closed {
					Some(SwarmEvent::NodeClosed {
						node_index,
						peer_id,
						closed_custom_protocols: Vec::new(),
					})
				} else {
					None
				}
			},
			Some(NodeEvent::Unresponsive) => {
				debug!(target: "sub-libp2p", "Node {:?} is unresponsive", peer_id);
				if !node_is_closed {
					Some(SwarmEvent::UnresponsiveNode { node_index })
				} else {
					None
				}
			},
			Some(NodeEvent::Useless) => {
				debug!(target: "sub-libp2p", "Node {:?} is useless", peer_id);
				if !node_is_closed {
					Some(SwarmEvent::UselessNode { node_index })
				} else {
					None
				}
			},
			Some(NodeEvent::PingStart) => {
				trace!(target: "sub-libp2p", "Pinging {:?}", peer_id);
				None
			},
			Some(NodeEvent::PingSuccess(ping)) => {
				trace!(target: "sub-libp2p", "Pong from {:?} in {:?}", peer_id, ping);
				if !node_is_closed {
					Some(SwarmEvent::PingDuration(node_index, ping))
				} else {
					None
				}
			},
			Some(NodeEvent::Identified { info, observed_addr }) => {
				self.add_observed_addr(&peer_id, &observed_addr);
				trace!(target: "sub-libp2p", "Client version of {:?}: {:?}", peer_id, info.agent_version);
				if !info.agent_version.contains("substrate") {
					info!(target: "sub-libp2p", "Connected to non-substrate node {:?}: {}",
						peer_id, info.agent_version);
				}

				if !node_is_closed {
					Some(SwarmEvent::NodeInfos {
						node_index,
						client_version: info.agent_version,
						listen_addrs: info.listen_addrs,
					})
				} else {
					None
				}
			},
			Some(NodeEvent::IdentificationRequest(request)) => {
				self.respond_to_identify_request(&peer_id, request);
				None
			},
			Some(NodeEvent::KadFindNode { searched, responder }) => {
				if !node_is_closed {
					Some(SwarmEvent::KadFindNode { node_index, searched, responder })
				} else {
					None
				}
			},
			Some(NodeEvent::KadOpen(ctrl)) => {
				trace!(target: "sub-libp2p", "Opened Kademlia substream with {:?}", peer_id);
				if !node_is_closed {
					Some(SwarmEvent::KadOpen { node_index, controller: ctrl })
				} else {
					None
				}
			},
			Some(NodeEvent::KadClosed(result)) => {
				trace!(target: "sub-libp2p", "Closed Kademlia substream with {:?}: {:?}", peer_id, result);
				if !node_is_closed {
					Some(SwarmEvent::KadClosed { node_index, result })
				} else {
					None
				}
			},
			Some(NodeEvent::OutboundSubstreamRequested) => {
				if let Some(mut peer) = self.swarm.peer(peer_id.clone()).as_connected() {
					peer.open_substream(());
				} else {
					error!(target: "sub-libp2p", "Inconsistent state in the service task");
				}
				None
			},
			Some(NodeEvent::CustomProtocolOpen { protocol_id, version }) => {
				trace!(target: "sub-libp2p", "Opened custom protocol with {:?}", peer_id);
				self.nodes_info.get_mut(&node_index).expect("Inconsistent state")
					.open_protocols.push(protocol_id);
				if !node_is_closed {
					Some(SwarmEvent::OpenedCustomProtocol {
						node_index,
						protocol: protocol_id,
						version,
					})
				} else {
					None
				}
			},
			Some(NodeEvent::CustomProtocolClosed { protocol_id, result }) => {
				trace!(target: "sub-libp2p", "Closed custom protocol with {:?}: {:?}", peer_id, result);
				self.nodes_info.get_mut(&node_index).expect("Inconsistent state")
					.open_protocols.retain(|p| p != &protocol_id);
				if !node_is_closed {
					Some(SwarmEvent::ClosedCustomProtocol {
						node_index,
						protocol: protocol_id,
					})
				} else {
					None
				}
			},
			Some(NodeEvent::CustomMessage { protocol_id, packet_id, data }) => {
				if !node_is_closed {
					Some(SwarmEvent::CustomMessage {
						node_index,
						protocol_id,
						packet_id,
						data,
					})
				} else {
					None
				}
			},
			Some(NodeEvent::SubstreamUpgradeFail(err)) => {
				debug!(target: "sub-libp2p", "Error while negotiating final protocol \
					with {:?}: {:?}", peer_id, err);
				None
			},
		}
	}
}

impl<TUserData> Stream for Swarm<TUserData>
	where TUserData: Clone + Send + Sync + 'static {
	type Item = SwarmEvent;
	type Error = IoError;

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		for task in self.tasks_to_spawn.drain(..) {
			tokio_executor::spawn(task);
		}

		match self.poll_network()? {
			Async::Ready(value) => return Ok(Async::Ready(value)),
			Async::NotReady => (),
		}

		match self.poll_node_tasks()? {
			Async::Ready(value) => return Ok(Async::Ready(value)),
			Async::NotReady => (),
		}

		// The only way we reach this is if we went through all the `NotReady` paths above,
		// ensuring the current task is registered everywhere.
		self.to_notify = Some(task::current());
		Ok(Async::NotReady)
	}
}

/// Wraps around a `NodeHandler` and adds communication with the outside through channels.
struct NodeTask<TUserData> {
	node_index: NodeIndex,
	handler: Option<NodeHandler<Substream<Muxer>, TUserData>>,
	out_commands_rx: mpsc::UnboundedReceiver<OutToTaskMsg>,
	node_tasks_events_tx: mpsc::UnboundedSender<(NodeIndex, Option<NodeEvent<Substream<Muxer>>>)>,
}

impl<TUserData> NodeTask<TUserData>
where TUserData: Clone + Send + Sync + 'static
{
	fn handle_out_command(&mut self, command: OutToTaskMsg) {
		match command {
			OutToTaskMsg::InjectSubstream { substream, endpoint } =>
				if let Some(handler) = self.handler.as_mut() {
					handler.inject_substream(substream, endpoint);
				} else {
					error!(target: "sub-libp2p", "Received message after handler is closed");
				},
			OutToTaskMsg::OpenKademlia =>
				if let Some(handler) = self.handler.as_mut() {
					if let Some(ctrl) = handler.open_kademlia() {
						let event = NodeEvent::KadOpen(ctrl);
						let _ = self.node_tasks_events_tx.unbounded_send((self.node_index, Some(event)));
					}
				} else {
					error!(target: "sub-libp2p", "Received message after handler is closed");
				},
			OutToTaskMsg::SendCustomMessage { protocol, packet_id, data } =>
				if let Some(handler) = self.handler.as_mut() {
					handler.send_custom_message(protocol, packet_id, data);
				} else {
					error!(target: "sub-libp2p", "Received message after handler is closed");
				},
		}
	}
}

impl<TUserData> Future for NodeTask<TUserData>
where TUserData: Clone + Send + Sync + 'static
{
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		// Poll for commands sent from the service.
		loop {
			match self.out_commands_rx.poll() {
				Ok(Async::NotReady) => break,
				Ok(Async::Ready(Some(command))) => self.handle_out_command(command),
				Ok(Async::Ready(None)) => {
					if let Some(handler) = self.handler.take() {
						for event in handler.close() {
							let _ = self.node_tasks_events_tx.unbounded_send((self.node_index, Some(event)));
						}
					}
					let _ = self.node_tasks_events_tx.unbounded_send((self.node_index, None));
					return Ok(Async::Ready(()))
				},
				Err(_) => unreachable!("An UnboundedReceiver never errors"),
			}
		}

		// Poll events from the node.
		loop {
			match self.handler.as_mut().map(|h| h.poll()).unwrap_or(Ok(Async::Ready(None))) {
				Ok(Async::Ready(event)) => {
					let finished = event.is_none();
					let _ = self.node_tasks_events_tx.unbounded_send((self.node_index, event));
					// If the node's events stream ends, end the task as well.
					if finished {
						return Ok(Async::Ready(()));
					}
				},
				Ok(Async::NotReady) => break,
				Err(err) => {
					warn!(target: "sub-libp2p", "Error in node handler: {:?}", err);
					return Ok(Async::Ready(()));
				}
			}
		}

		// If we reach here, that means nothing is ready.
		Ok(Async::NotReady)
	}
}
