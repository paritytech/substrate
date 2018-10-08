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
use custom_proto::{RegisteredProtocol, RegisteredProtocols};
use fnv::{FnvHashMap, FnvHashSet};
use futures::{prelude::*, task, Stream};
use futures::sync::{oneshot, mpsc};
use libp2p::{Multiaddr, PeerId};
use libp2p::core::{Endpoint, PublicKey};
use libp2p::core::nodes::swarm::ConnectedPoint;
use libp2p::kad::{KadSystem, KadSystemConfig, KadConnecController, KadPeer};
use libp2p::kad::{KadConnectionType, KadQueryEvent};
use parking_lot::Mutex;
use rand;
use secret::obtain_private_key;
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
use std::iter;
use std::net::SocketAddr;
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant};
use swarm::{self, Swarm, SwarmEvent};
use topology::{DisconnectReason, NetTopology};
use tokio_timer::{Delay, Interval};
use {Error, ErrorKind, NetworkConfiguration, NodeIndex, parse_str_addr};
use {NonReservedPeerMode, ProtocolId};

// File where the network topology is stored.
const NODES_FILE: &str = "nodes.json";
// Duration during which a peer is disabled.
const PEER_DISABLE_DURATION: Duration = Duration::from_secs(5 * 60);

/// Starts the substrate libp2p service.
///
/// Returns a stream that must be polled regularly in order for the networking to function.
pub fn start_service<TProtos>(
	config: NetworkConfiguration,
	registered_custom: TProtos,
) -> Result<Service, Error>
where TProtos: IntoIterator<Item = RegisteredProtocol> {
	// Private and public keys configuration.
	let local_private_key = obtain_private_key(&config)?;
	let local_public_key = local_private_key.to_public_key();
	let local_peer_id = local_public_key.clone().into_peer_id();

	// Build the swarm.
	let registered_custom = RegisteredProtocols(registered_custom.into_iter().collect());
	let mut swarm = swarm::start_swarm(registered_custom, local_private_key)?;

	// Listen on multiaddresses.
	for addr in &config.listen_addresses {
		match swarm.listen_on(addr.clone()) {
			Ok(new_addr) => debug!(target: "sub-libp2p", "Libp2p listening on {}", new_addr),
			Err(_) => {
				warn!(target: "sub-libp2p", "Can't listen on {}, protocol not supported", addr);
				return Err(ErrorKind::BadProtocol.into())
			},
		}
	}

	// Register the external addresses provided by the user.
	for addr in &config.public_addresses {
		swarm.add_external_address(addr.clone());
	}

	// Initialize the topology of the network.
	let mut topology = if let Some(ref path) = config.net_config_path {
		let path = Path::new(path).join(NODES_FILE);
		debug!(target: "sub-libp2p", "Initializing peer store for JSON file {:?}", path);
		NetTopology::from_file(path)
	} else {
		debug!(target: "sub-libp2p", "No peers file configured ; peers won't be saved");
		NetTopology::memory()
	};

	// Create the Kademlia system, containing the kbuckets.
	let kad_system = KadSystem::without_init(KadSystemConfig {
		parallelism: 3,
		local_peer_id,
		kbuckets_timeout: Duration::from_secs(600),
		request_timeout: Duration::from_secs(10),
		known_initial_peers: iter::empty(),
	});

	// Add the bootstrap nodes to the topology and connect to them.
	for bootnode in config.boot_nodes.iter() {
		match parse_str_addr(bootnode) {
			Ok((peer_id, addr)) => {
				topology.add_bootstrap_addr(&peer_id, addr.clone());
				kad_system.update_kbuckets(peer_id.clone());
				if let Err(_) = swarm.ensure_connection(peer_id, addr) {
					warn!(target: "sub-libp2p", "Failed to dial boot node: {}", bootnode);
				}
			},
			Err(_) => {
				// If the format of the bootstrap node is not a multiaddr, try to parse it as
				// a `SocketAddr`. This corresponds to the format `IP:PORT`.
				let addr = match bootnode.parse::<SocketAddr>() { 
					Ok(SocketAddr::V4(socket)) => multiaddr![Ip4(*socket.ip()), Tcp(socket.port())],
					Ok(SocketAddr::V6(socket)) => multiaddr![Ip6(*socket.ip()), Tcp(socket.port())],
					_ => {
						warn!(target: "sub-libp2p", "Not a valid bootnode address: {}", bootnode);
						continue;
					}
				};

				debug!(target: "sub-libp2p", "Dialing {} with no peer id", addr);
				if let Err(addr) = swarm.dial(addr) {
					warn!(target: "sub-libp2p", "Bootstrap address not supported: {}", addr);
				}
			},
		}
	}

	// Initialize the reserved peers.
	let mut reserved_peers = FnvHashSet::default();
	for reserved in config.reserved_nodes.iter() {
		match parse_str_addr(reserved) {
			Ok((peer_id, addr)) => {
				reserved_peers.insert(peer_id.clone());
				topology.add_bootstrap_addr(&peer_id, addr.clone());
				if let Err(_) = swarm.ensure_connection(peer_id, addr) {
					warn!(target: "sub-libp2p", "Failed to dial reserved node: {}", reserved);
				}
			},
			Err(_) =>
				// TODO: also handle the `IP:PORT` format ; however we need to somehow add the
				// reserved ID to `reserved_peers` at some point
				warn!(target: "sub-libp2p", "Not a valid reserved node address: {}", reserved),
		}
	}

	debug!(target: "sub-libp2p", "Topology started with {} entries", topology.num_peers());

	let (kad_new_ctrl_req_tx, kad_new_ctrl_req_rx) = mpsc::unbounded();

	Ok(Service {
		swarm,
		max_incoming_connections: config.max_peers.saturating_sub(config.min_peers) as usize,
		max_outgoing_connections: config.min_peers as usize,
		topology,
		nodes_addresses: Default::default(),
		disabled_peers: Default::default(),
		reserved_peers,
		reserved_only: config.non_reserved_mode == NonReservedPeerMode::Deny,
		kad_system,
		kad_pending_ctrls: Default::default(),
		kad_new_ctrl_req_tx,
		kad_new_ctrl_req_rx,
		kad_queries: Vec::with_capacity(1),
		next_connect_to_nodes: Delay::new(Instant::now()),
		next_kad_random_query: Interval::new(Instant::now() + Duration::from_secs(5), Duration::from_secs(45)),
		cleanup: Interval::new_interval(Duration::from_secs(60)),
		injected_events: Vec::new(),
		to_notify: None,
	})
}

/// Event produced by the service.
pub enum ServiceEvent {
	/// Closed connection to a node.
	///
	/// It is guaranteed that this node has been opened with a `NewNode` event beforehand. However
	/// not all `ClosedCustomProtocol` events have been dispatched.
	NodeClosed {
		/// Index of the node.
		node_index: NodeIndex,
		/// List of custom protocols that were still open.
		closed_custom_protocols: Vec<ProtocolId>,
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

	/// Sustom protocol substreams has been closed.
	///
	/// Same as `ClosedCustomProtocol` but with multiple protocols.
	ClosedCustomProtocols {
		/// Index of the node.
		node_index: NodeIndex,
		/// Protocols that have been closed.
		protocols: Vec<ProtocolId>,
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
}

/// Network service. Must be polled regularly in order for the networking to work.
pub struct Service {
	/// Stream of events of the swarm.
	swarm: Swarm,

	/// Maximum number of incoming non-reserved connections, taken from the config.
	max_incoming_connections: usize,

	/// Maximum number of outgoing non-reserved connections, taken from the config.
	max_outgoing_connections: usize,

	/// For each node we're connected to, how we're connected to it.
	nodes_addresses: FnvHashMap<NodeIndex, ConnectedPoint>,

	/// If true, only reserved peers can connect.
	reserved_only: bool,

	/// List of the IDs of the reserved peers.
	reserved_peers: FnvHashSet<PeerId>,

	/// List of the IDs of disabled peers, and when the ban expires.
	/// Purged at a regular interval.
	disabled_peers: FnvHashMap<PeerId, Instant>,

	/// Topology of the network.
	topology: NetTopology,

	/// Handles the Kademlia queries.
	// TODO: put the kbuckets in the topology instead
	kad_system: KadSystem,

	/// List of Kademlia controller we want to open.
	///
	/// A clone of tihs `Arc` is stored in each Kademlia query stream.
	// TODO: use a better container?
	kad_pending_ctrls: Arc<Mutex<FnvHashMap<PeerId, Vec<oneshot::Sender<KadConnecController>>>>>,

	/// Sender whenever we inserted an entry in `kad_pending_ctrls`, so that we can process it.
	kad_new_ctrl_req_tx: mpsc::UnboundedSender<PeerId>,
	/// Receiver side of `kad_new_ctrl_req_tx`.
	kad_new_ctrl_req_rx: mpsc::UnboundedReceiver<PeerId>,

	/// Active Kademlia queries.
	kad_queries: Vec<Box<Stream<Item = KadQueryEvent<Vec<PeerId>>, Error = IoError> + Send>>,

	/// Future that will fire when we need to connect to new nodes.
	next_connect_to_nodes: Delay,

	/// Stream that fires when we need to perform the next Kademlia query.
	next_kad_random_query: Interval,

	/// Stream that fires when we need to cleanup and flush the topology, and cleanup the disabled
	/// peers.
	cleanup: Interval,

	/// Events to produce on the Stream.
	injected_events: Vec<ServiceEvent>,

	/// Task to notify when elements are added to `injected_events`.
	to_notify: Option<task::Task>,
}

impl Service {
    /// Returns an iterator that produces the list of addresses we're listening on.
	#[inline]
	pub fn listeners(&self) -> impl Iterator<Item = &Multiaddr> {
		self.swarm.listeners()
	}

	/// Returns the peer id of the local node.
	#[inline]
	pub fn peer_id(&self) -> &PeerId {
		self.kad_system.local_peer_id()
	}

	/// Returns the list of all the peers we are connected to.
	#[inline]
	pub fn connected_peers<'a>(&'a self) -> impl Iterator<Item = NodeIndex> + 'a {
		self.nodes_addresses.keys().cloned()
	}

	/// Try to add a reserved peer.
	pub fn add_reserved_peer(&mut self, peer_id: PeerId, addr: Multiaddr) {
		self.reserved_peers.insert(peer_id.clone());
		self.topology.add_bootstrap_addr(&peer_id, addr.clone());
		let _ = self.swarm.ensure_connection(peer_id, addr);
	}

	/// Try to remove a reserved peer.
	///
	/// If we are in reserved mode and we were connected to a node with this peer ID, then this
	/// method will disconnect it and return its index.
	pub fn remove_reserved_peer(&mut self, peer_id: PeerId) -> Option<NodeIndex> {
		self.reserved_peers.remove(&peer_id);
		if self.reserved_only {
			if let Some(node_index) = self.swarm.latest_node_by_peer_id(&peer_id) {
				self.drop_node_inner(node_index, DisconnectReason::NoSlot, None);
				return Some(node_index);
			}
		}
		None
	}

	/// Start accepting all peers again if we weren't.
	pub fn accept_unreserved_peers(&mut self) {
		if self.reserved_only {
			self.reserved_only = false;
			self.connect_to_nodes();
		}
	}

	/// Start refusing non-reserved nodes. Returns the list of nodes that have been disconnected.
	pub fn deny_unreserved_peers(&mut self) -> Vec<NodeIndex> {
		self.reserved_only = true;

		// Disconnect the nodes that are not reserved.
		let to_disconnect: Vec<NodeIndex> = self.swarm
			.nodes()
			.filter(|&n| {
				let peer_id = self.swarm.peer_id_of_node(n)
					.expect("swarm.nodes() always returns valid node indices");
				!self.reserved_peers.contains(peer_id)
			})
			.collect();

		for &node_index in &to_disconnect {
			self.drop_node_inner(node_index, DisconnectReason::NoSlot, None);
		}

		to_disconnect
	}

	/// Returns the `PeerId` of a node.
	#[inline]
	pub fn peer_id_of_node(&self, node_index: NodeIndex) -> Option<&PeerId> {
		self.swarm.peer_id_of_node(node_index)
	}

	/// Returns the way we are connected to a node.
	#[inline]
	pub fn node_endpoint(&self, node_index: NodeIndex) -> Option<&ConnectedPoint> {
		self.nodes_addresses.get(&node_index)
	}

	/// Sends a message to a peer using the custom protocol.
	// TODO: report invalid node index or protocol?
	pub fn send_custom_message(
		&mut self,
		node_index: NodeIndex,
		protocol: ProtocolId,
		data: Vec<u8>
	) {
		self.swarm.send_custom_message(node_index, protocol, data)
	}

	/// Disconnects a peer and bans it for a little while.
	///
	/// Same as `drop_node`, except that the same peer will not be able to reconnect later.
	#[inline]
	pub fn ban_node(&mut self, node_index: NodeIndex) {
		if let Some(peer_id) = self.swarm.peer_id_of_node(node_index) {
			info!(target: "sub-libp2p", "Banned {:?}", peer_id);
		}

		self.drop_node_inner(node_index, DisconnectReason::Banned, Some(PEER_DISABLE_DURATION));
	}

	/// Disconnects a peer.
	///
	/// This is asynchronous and will not immediately close the peer.
	/// Corresponding closing events will be generated once the closing actually happens.
	#[inline]
	pub fn drop_node(&mut self, node_index: NodeIndex) {
		if let Some(peer_id) = self.swarm.peer_id_of_node(node_index) {
			info!(target: "sub-libp2p", "Dropped {:?}", peer_id);
		}

		self.drop_node_inner(node_index, DisconnectReason::Useless, None);
	}

	/// Common implementation of `drop_node` and `ban_node`.
	fn drop_node_inner(
		&mut self,
		node_index: NodeIndex,
		reason: DisconnectReason,
		disable_duration: Option<Duration>
	) {
		let peer_id = match self.swarm.peer_id_of_node(node_index) {
			Some(pid) => pid.clone(),
			None => return,		// TODO: report?
		};

		// Kill the node from the swarm, and inject an event about it.
		let closed_custom_protocols = self.swarm.drop_node(node_index)
			.expect("we checked right above that node is valid");
		self.injected_events.push(ServiceEvent::NodeClosed {
			node_index,
			closed_custom_protocols,
		});

		if let Some(to_notify) = self.to_notify.take() {
			to_notify.notify();
		}

		if let Some(ConnectedPoint::Dialer { address }) = self.nodes_addresses.remove(&node_index) {
			self.topology.report_disconnected(&address, reason);
		}

		if let Some(disable_duration) = disable_duration {
			let timeout = Instant::now() + disable_duration;
			self.disabled_peers.insert(peer_id, timeout);
		}

		self.connect_to_nodes();
	}

	/// Counts the number of non-reserved ingoing connections.
	fn num_ingoing_connections(&self) -> usize {
		self.swarm.nodes()
			.filter(|&i| self.swarm.node_endpoint(i) == Some(Endpoint::Listener) &&
				!self.reserved_peers.contains(&self.swarm.peer_id_of_node(i).unwrap()))
			.count()
	}

	/// Counts the number of non-reserved outgoing connections.
	fn num_outgoing_connections(&self) -> usize {
		self.swarm.nodes()
			.filter(|&i| self.swarm.node_endpoint(i) == Some(Endpoint::Dialer) &&
				!self.reserved_peers.contains(&self.swarm.peer_id_of_node(i).unwrap()))
			.count()
	}

	/// Updates the attempted connections to nodes.
	///
	/// Also updates `next_connect_to_nodes` with the earliest known moment when we need to
	/// update connections again.
	fn connect_to_nodes(&mut self) {
		// Make sure we are connected or connecting to all the reserved nodes.
		for reserved in self.reserved_peers.iter() {
			let addrs = self.topology.addrs_of_peer(&reserved);
			for (addr, _) in addrs {
				let _ = self.swarm.ensure_connection(reserved.clone(), addr.clone());
			}
		}

		// Counter of number of connections to open, decreased when we open one.
		let mut num_to_open = self.max_outgoing_connections - self.num_outgoing_connections();

		let (to_try, will_change) = self.topology.addrs_to_attempt();
		for (peer_id, addr) in to_try {
			if num_to_open == 0 {
				break;
			}

			if peer_id == self.kad_system.local_peer_id() {
				continue;
			}

			if self.disabled_peers.contains_key(&peer_id) {
				continue;
			}

			// It is possible that we are connected to this peer, but the topology doesn't know
			// about that because it is an incoming connection.
			match self.swarm.ensure_connection(peer_id.clone(), addr.clone()) {
				Ok(true) => (),
				Ok(false) => num_to_open -= 1,
				Err(_) => ()
			}
		}

		self.next_connect_to_nodes.reset(will_change);
	}

	/// Starts a random Kademlia query in order to fill the topology.
	///
	/// Query the node IDs that are closest to a random ID.
	/// Note that the randomness doesn't have to be secure, as this only influences which nodes we
	/// end up being connected to.
	fn perform_kad_random_query(&mut self) {
		let random_key = PublicKey::Ed25519((0 .. 32)
			.map(|_| -> u8 { rand::random() }).collect());
		let random_peer_id = random_key.into_peer_id();
		debug!(target: "sub-libp2p", "Start random Kademlia query for {:?}", random_peer_id);

		let kad_pending_ctrls = self.kad_pending_ctrls.clone();
		let kad_new_ctrl_req_tx = self.kad_new_ctrl_req_tx.clone();
		let stream = self.kad_system
			.find_node(random_peer_id, move |who| {
				let (tx, rx) = oneshot::channel();
				let mut kad_pending_ctrls = kad_pending_ctrls.lock();
				kad_pending_ctrls.entry(who.clone()).or_insert(Vec::new()).push(tx);
				let _ = kad_new_ctrl_req_tx.unbounded_send(who.clone());
				rx.map_err(|_| IoError::new(IoErrorKind::Other, "Couldn't reach peer"))
			});

		self.kad_queries.push(Box::new(stream));
	}

	/// If a remote performs a `FIND_NODE` Kademlia request for `searched`, this function builds
	/// the response to send back.
	fn build_kademlia_response(&self, searched: &PeerId) -> Vec<KadPeer> {
		self.kad_system
			.known_closest_peers(searched)
			.map(|who| {
				if who == *self.kad_system.local_peer_id() {
					KadPeer {
						node_id: who.clone(),
						multiaddrs: self.swarm.external_addresses().cloned().collect(),
						connection_ty: KadConnectionType::Connected,
					}
				} else {
					let mut addrs = self.topology.addrs_of_peer(&who)
						.map(|(a, c)| (a.clone(), c))
						.collect::<Vec<_>>();
					let connected = addrs.iter().any(|&(_, conn)| conn);
					// The Kademlia protocol of libp2p doesn't allow specifying which address is valid
					// and which is outdated, therefore in order to stay honest towards the network
					// we only report the addresses we're connected to if we're connected to any.
					if connected {
						addrs.retain(|&(_, connected)| connected);
					}

					KadPeer {
						node_id: who.clone(),
						multiaddrs: addrs.into_iter().map(|(a, _)| a).collect(),
						connection_ty: if connected {
							KadConnectionType::Connected
						} else {
							KadConnectionType::NotConnected
						},
					}
				}
			})
			// TODO: we really want to remove nodes with no multiaddress from
			// the results, but a flaw in the Kad protocol of libp2p makes it
			// impossible to return empty results ; therefore we must at least
			// return ourselves
			.filter(|p| p.node_id == *self.kad_system.local_peer_id() || !p.multiaddrs.is_empty())
			.take(20)
			.collect::<Vec<_>>()
	}

	/// Adds a list of peers to the network topology.
	fn add_discovered_peers(&mut self, list: impl IntoIterator<Item = KadPeer>) {
		for peer in list {
			let connected = match peer.connection_ty {
				KadConnectionType::NotConnected => false,
				KadConnectionType::Connected => true,
				KadConnectionType::CanConnect => true,
				KadConnectionType::CannotConnect => continue,
			};

			self.topology.add_kademlia_discovered_addrs(
				&peer.node_id,
				peer.multiaddrs.iter().map(|a| (a.clone(), connected))
			);
		}

		// Potentially connect to the newly-discovered nodes.
		// TODO: only do so if the topology reports that something new has been added
		self.connect_to_nodes();
	}

	/// Handles the swarm opening a connection to the given peer.
	///
	/// > **Note**: Must be called from inside `poll()`, otherwise it will panic.
	fn handle_connection(
		&mut self,
		node_index: NodeIndex,
		peer_id: PeerId,
		endpoint: ConnectedPoint
	) {
		// Reject connections to our own node, which can happen if the DHT contains `127.0.0.1`
		// for example.
		if &peer_id == self.kad_system.local_peer_id() {
			debug!(target: "sub-libp2p", "Rejected connection to/from ourself: {:?}", endpoint);
			assert_eq!(self.swarm.drop_node(node_index), Ok(Vec::new()));
			if let ConnectedPoint::Dialer { ref address } = endpoint {
				self.topology.report_failed_to_connect(address);
			}
			return;
		}

		// Reject non-reserved nodes if we're in reserved mode.
		let is_reserved = self.reserved_peers.contains(&peer_id);
		if self.reserved_only && !is_reserved {
			debug!(target: "sub-libp2p", "Rejected non-reserved peer {:?}", peer_id);
			assert_eq!(self.swarm.drop_node(node_index), Ok(Vec::new()));
			if let ConnectedPoint::Dialer { ref address } = endpoint {
				self.topology.report_failed_to_connect(address);
			}
			return;
		}

		// Reject connections from disabled peers.
		if let Some(expires) = self.disabled_peers.get(&peer_id) {
			if expires > &Instant::now() {
				info!(target: "sub-libp2p", "Rejected connection from disabled peer: {:?}", peer_id);
				assert_eq!(self.swarm.drop_node(node_index), Ok(Vec::new()));
				if let ConnectedPoint::Dialer { ref address } = endpoint {
					self.topology.report_failed_to_connect(address);
				}
				return;
			}
		}

		match endpoint {
			ConnectedPoint::Listener { ref listen_addr, ref send_back_addr } => {
				if is_reserved || self.num_ingoing_connections() < self.max_incoming_connections {
					debug!(target: "sub-libp2p", "Connected to {:?} through {} on listener {}",
						peer_id, send_back_addr, listen_addr);
				} else {
					info!(target: "sub-libp2p", "Rejected incoming peer {:?} because we are full", peer_id);
					assert_eq!(self.swarm.drop_node(node_index), Ok(Vec::new()));
					return;
				}
			},
			ConnectedPoint::Dialer { ref address } => {
				if is_reserved || self.num_outgoing_connections() < self.max_outgoing_connections {
					debug!(target: "sub-libp2p", "Connected to {:?} through {}", peer_id, address);
					self.topology.report_connected(address, &peer_id);
				} else {
					debug!(target: "sub-libp2p", "Rejected dialed peer {:?} because we are full", peer_id);
					assert_eq!(self.swarm.drop_node(node_index), Ok(Vec::new()));
					return;
				}
			},
		};

		if let Err(_) = self.swarm.accept_node(node_index) {
			error!(target: "sub-libp2p", "accept_node returned an error");
		}

		// We are finally sure that we're connected.

		if let ConnectedPoint::Dialer { ref address } = endpoint {
			self.topology.report_connected(address, &peer_id);
		}
		self.nodes_addresses.insert(node_index, endpoint.clone());

		// If we're waiting for a Kademlia substream for this peer id, open one.
		let kad_pending_ctrls = self.kad_pending_ctrls.lock();
		if kad_pending_ctrls.contains_key(&peer_id) {
			let res = self.swarm.open_kademlia(node_index);
			debug_assert!(res.is_ok());
		}
	}

	/// Processes an event received by the swarm.
	///
	/// Optionally returns an event to report back to the outside.
	///
	/// > **Note**: Must be called from inside `poll()`, otherwise it will panic.
	fn process_network_event(
		&mut self,
		event: SwarmEvent
	) -> Option<ServiceEvent> {
		match event {
			SwarmEvent::NodePending { node_index, peer_id, endpoint } => {
				self.handle_connection(node_index, peer_id, endpoint);
				None
			},
			SwarmEvent::Reconnected { node_index, endpoint, closed_custom_protocols } => {
				if let Some(ConnectedPoint::Dialer { address }) = self.nodes_addresses.remove(&node_index) {
					self.topology.report_disconnected(&address, DisconnectReason::FoundBetterAddr);
				}
				if let ConnectedPoint::Dialer { ref address } = endpoint {
					let peer_id = self.swarm.peer_id_of_node(node_index)
						.expect("the swarm always produces events containing valid node indices");
					self.topology.report_connected(address, peer_id);
				}
				self.nodes_addresses.insert(node_index, endpoint);
				Some(ServiceEvent::ClosedCustomProtocols {
					node_index,
					protocols: closed_custom_protocols,
				})
			},
			SwarmEvent::NodeClosed { node_index, peer_id, closed_custom_protocols } => {
				debug!(target: "sub-libp2p", "Connection to {:?} closed gracefully", peer_id);
				if let Some(ConnectedPoint::Dialer { ref address }) = self.nodes_addresses.get(&node_index) {
					self.topology.report_disconnected(address, DisconnectReason::RemoteClosed);
				}
				self.connect_to_nodes();
				Some(ServiceEvent::NodeClosed {
					node_index,
					closed_custom_protocols,
				})
			},
			SwarmEvent::DialFail { address, error } => {
				debug!(target: "sub-libp2p", "Failed to dial address {}: {:?}", address, error);
				self.topology.report_failed_to_connect(&address);
				self.connect_to_nodes();
				None
			},
			SwarmEvent::UnresponsiveNode { node_index } => {
				let closed_custom_protocols = self.swarm.drop_node(node_index)
					.expect("the swarm always produces events containing valid node indices");
				if let Some(ConnectedPoint::Dialer { address }) = self.nodes_addresses.remove(&node_index) {
					self.topology.report_disconnected(&address, DisconnectReason::Useless);
				}
				Some(ServiceEvent::NodeClosed {
					node_index,
					closed_custom_protocols,
				})
			},
			SwarmEvent::UselessNode { node_index } => {
				let peer_id = self.swarm.peer_id_of_node(node_index)
					.expect("the swarm always produces events containing valid node indices")
					.clone();
				let closed_custom_protocols = self.swarm.drop_node(node_index)
					.expect("the swarm always produces events containing valid node indices");
				self.topology.report_useless(&peer_id);
				if let Some(ConnectedPoint::Dialer { address }) = self.nodes_addresses.remove(&node_index) {
					self.topology.report_disconnected(&address, DisconnectReason::Useless);
				}
				Some(ServiceEvent::NodeClosed {
					node_index,
					closed_custom_protocols,
				})
			},
			SwarmEvent::NodeInfos { node_index, listen_addrs, .. } => {
				let peer_id = self.swarm.peer_id_of_node(node_index)
					.expect("the swarm always produces events containing valid node indices");
				self.topology.add_self_reported_listen_addrs(
					peer_id,
					listen_addrs.into_iter()
				);
				None
			},
			SwarmEvent::KadFindNode { searched, responder, .. } => {
				let response = self.build_kademlia_response(&searched);
				responder.respond(response);
				None
			},
			SwarmEvent::KadOpen { node_index, controller } => {
				let peer_id = self.swarm.peer_id_of_node(node_index)
					.expect("the swarm always produces events containing valid node indices");
				trace!(target: "sub-libp2p", "Opened Kademlia substream with {:?}", peer_id);
				if let Some(list) = self.kad_pending_ctrls.lock().remove(&peer_id) {
					for tx in list {
						let _ = tx.send(controller.clone());
					}
				}
				None
			},
			SwarmEvent::KadClosed { .. } => {
				None
			},
			SwarmEvent::OpenedCustomProtocol { node_index, protocol, version } => {
				let peer_id = self.swarm.peer_id_of_node(node_index)
					.expect("the swarm always produces events containing valid node indices");
				self.kad_system.update_kbuckets(peer_id.clone());
				Some(ServiceEvent::OpenedCustomProtocol {
					node_index,
					protocol,
					version,
				})
			},
			SwarmEvent::ClosedCustomProtocol { node_index, protocol } =>
				Some(ServiceEvent::ClosedCustomProtocol {
					node_index,
					protocol,
				}),
			SwarmEvent::CustomMessage { node_index, protocol_id, data } => {
				let peer_id = self.swarm.peer_id_of_node(node_index)
					.expect("the swarm always produces events containing valid node indices");
				self.kad_system.update_kbuckets(peer_id.clone());
				Some(ServiceEvent::CustomMessage {
					node_index,
					protocol_id,
					data,
				})
			},
		}
	}

	/// Handles a Kademlia query requesting a Kademlia controller with the given peer.
	fn handle_kad_ctrl_request(&mut self, peer_id: PeerId) {
		if let Some(node_index) = self.swarm.latest_node_by_peer_id(&peer_id) {
			if let Err(_) = self.swarm.open_kademlia(node_index) {
				self.kad_pending_ctrls.lock().remove(&peer_id);
			}
		} else {
			let addrs = self.topology.addrs_of_peer(&peer_id);
			let mut one_worked = false;
			for (addr, _) in addrs {
				if let Ok(_) = self.swarm.ensure_connection(peer_id.clone(), addr.clone()) {
					one_worked = true;
				}
			}
			if !one_worked {
				debug!(target: "sub-libp2p", "Couldn't open Kad substream with {:?} \
					because no address is known", peer_id);
				// Closing the senders in order to generate errors on the Kad query.
				self.kad_pending_ctrls.lock().remove(&peer_id);
			}
		}
	}

	/// Polls for what happened on the main network side.
	fn poll_swarm(&mut self) -> Poll<Option<ServiceEvent>, IoError> {
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

	/// Polls the Kademlia system.
	fn poll_kademlia(&mut self) -> Poll<Option<ServiceEvent>, IoError> {
		// Polls the active Kademlia queries.
		// We remove each element from `kad_queries` one by one and add them back if not ready.
		for n in (0 .. self.kad_queries.len()).rev() {
			let mut query = self.kad_queries.swap_remove(n);
			loop {
				match query.poll() {
					Ok(Async::Ready(Some(KadQueryEvent::PeersReported(list)))) =>
						self.add_discovered_peers(list),
					// We don't actually care about the results
					Ok(Async::Ready(Some(KadQueryEvent::Finished(_out)))) => {
						if _out.is_empty() {
							warn!(target: "sub-libp2p", "Random Kademlia request has yielded \
								empty results");
						}
						break
					},
					Ok(Async::Ready(None)) => break,
					Ok(Async::NotReady) => {
						self.kad_queries.push(query);
						break;
					},
					Err(err) => {
						warn!(target: "sub-libp2p", "Kademlia query failed: {:?}", err);
						break;
					},
				}
			}
		}

		// Poll the future that fires when we need to reply to a Kademlia query.
		loop {
			match self.kad_new_ctrl_req_rx.poll() {
				Ok(Async::NotReady) => break,
				Ok(Async::Ready(Some(peer_id))) => self.handle_kad_ctrl_request(peer_id),
				Ok(Async::Ready(None)) => unreachable!("The tx is in self"),
				Err(()) => unreachable!("An UnboundedReceiver never errors"),
			}
		}

		// Poll the future that fires when we need to perform a random Kademlia query.
		loop {
			match self.next_kad_random_query.poll() {
				Ok(Async::NotReady) => break,
				Ok(Async::Ready(Some(_))) => self.perform_kad_random_query(),
				Ok(Async::Ready(None)) => {
					warn!(target: "sub-libp2p", "Kad query timer closed unexpectedly");
					return Ok(Async::Ready(None));
				}
				Err(err) => {
					warn!(target: "sub-libp2p", "Kad query timer errored: {:?}", err);
					return Err(IoError::new(IoErrorKind::Other, err));
				}
			}
		}

		Ok(Async::NotReady)
	}

	// Polls the future that fires when we need to refresh our connections.
	fn poll_next_connect_refresh(&mut self) -> Poll<Option<ServiceEvent>, IoError> {
		loop {
			match self.next_connect_to_nodes.poll() {
				Ok(Async::Ready(())) => self.connect_to_nodes(),
				Ok(Async::NotReady) => return Ok(Async::NotReady),
				Err(err) => {
					warn!(target: "sub-libp2p", "Connect to nodes timer errored: {:?}", err);
					return Err(IoError::new(IoErrorKind::Other, err));
				}
			}
		}
	}

	/// Polls the stream that fires when we need to cleanup and flush the topology.
	fn poll_cleanup(&mut self) -> Poll<Option<ServiceEvent>, IoError> {
		loop {
			match self.cleanup.poll() {
				Ok(Async::NotReady) => return Ok(Async::NotReady),
				Ok(Async::Ready(Some(_))) => {
					debug!(target: "sub-libp2p", "Cleaning and flushing topology");
					self.topology.cleanup();
					if let Err(err) = self.topology.flush_to_disk() {
						warn!(target: "sub-libp2p", "Failed to flush topology: {:?}", err);
					}
					let now = Instant::now();
					self.disabled_peers.retain(move |_, v| *v < now);
					debug!(target: "sub-libp2p", "Topology now contains {} nodes",
						self.topology.num_peers());
				},
				Ok(Async::Ready(None)) => {
					warn!(target: "sub-libp2p", "Topology flush stream ended unexpectedly");
					return Ok(Async::Ready(None));
				}
				Err(err) => {
					warn!(target: "sub-libp2p", "Topology flush stream errored: {:?}", err);
					return Err(IoError::new(IoErrorKind::Other, err));
				}
			}
		}
	}
}

impl Drop for Service {
	fn drop(&mut self) {
		if let Err(err) = self.topology.flush_to_disk() {
			warn!(target: "sub-libp2p", "Failed to flush topology: {:?}", err);
		}
	}
}

impl Stream for Service {
	type Item = ServiceEvent;
	type Error = IoError;

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		if !self.injected_events.is_empty() {
			return Ok(Async::Ready(Some(self.injected_events.remove(0))));
		}

		match self.poll_swarm()? {
			Async::Ready(value) => return Ok(Async::Ready(value)),
			Async::NotReady => (),
		}

		match self.poll_kademlia()? {
			Async::Ready(value) => return Ok(Async::Ready(value)),
			Async::NotReady => (),
		}

		match self.poll_next_connect_refresh()? {
			Async::Ready(value) => return Ok(Async::Ready(value)),
			Async::NotReady => (),
		}

		match self.poll_cleanup()? {
			Async::Ready(value) => return Ok(Async::Ready(value)),
			Async::NotReady => (),
		}

		// The only way we reach this is if we went through all the `NotReady` paths above,
		// ensuring the current task is registered everywhere.
		self.to_notify = Some(task::current());
		Ok(Async::NotReady)
	}
}
