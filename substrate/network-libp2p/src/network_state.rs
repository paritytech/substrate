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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.?

use bytes::Bytes;
use fnv::{FnvHashMap, FnvHashSet};
use futures::sync::mpsc;
use libp2p::core::{multiaddr::ToMultiaddr, Multiaddr, AddrComponent, Endpoint, UniqueConnec};
use libp2p::core::{UniqueConnecState, PeerId, PublicKey};
use libp2p::kad::KadConnecController;
use libp2p::peerstore::{Peerstore, PeerAccess};
use libp2p::peerstore::json_peerstore::JsonPeerstore;
use libp2p::peerstore::memory_peerstore::MemoryPeerstore;
use libp2p::ping::Pinger;
use libp2p::secio;
use {Error, ErrorKind, NetworkConfiguration, NonReservedPeerMode};
use {NodeIndex, ProtocolId, SessionInfo};
use parking_lot::{Mutex, RwLock};
use rand::{self, Rng};
use std::fs;
use std::io::{Error as IoError, ErrorKind as IoErrorKind, Read, Write};
use std::path::Path;
use std::sync::atomic;
use std::{thread, time};
use std::time::{Duration, Instant};

// File where the peers are stored.
const NODES_FILE: &str = "nodes.json";
// File where the private key is stored.
const SECRET_FILE: &str = "secret";
// Duration during which a peer is disabled.
const PEER_DISABLE_DURATION: Duration = Duration::from_secs(5 * 60);

// Common struct shared throughout all the components of the service.
pub struct NetworkState {
	/// Contains the information about the network.
	node_store: NodeStore,

	/// Active connections.
	connections: RwLock<Connections>,

	/// Maximum incoming peers.
	max_incoming_peers: u32,
	/// Maximum outgoing peers.
	max_outgoing_peers: u32,

	/// If true, only reserved peers can connect.
	reserved_only: atomic::AtomicBool,
	/// List of the IDs of the reserved peers.
	reserved_peers: RwLock<FnvHashSet<PeerId>>,

	/// Each node we discover gets assigned a new unique ID. This ID increases linearly.
	next_node_index: atomic::AtomicUsize,

	/// List of the IDs of the disabled peers. These peers will see their
	/// connections refused. Includes the time when the disabling expires.
	disabled_nodes: Mutex<FnvHashMap<PeerId, Instant>>,

	/// Local private key.
	local_private_key: secio::SecioKeyPair,
	/// Local public key.
	local_public_key: PublicKey,
}

enum NodeStore {
	/// Peers are stored in memory. Nothing is stored on disk.
	Memory(MemoryPeerstore),
	/// Peers are stored in a JSON file on the disk.
	Json(JsonPeerstore),
}

struct Connections {
	/// For each libp2p peer ID, the ID of the peer in the API we expose.
	/// Also corresponds to the index in `info_by_peer`.
	peer_by_nodeid: FnvHashMap<PeerId, usize>,

	/// For each peer ID, information about our connection to this peer.
	info_by_peer: FnvHashMap<NodeIndex, PeerConnectionInfo>,
}

struct PeerConnectionInfo {
	/// A list of protocols, and the potential corresponding connection.
	/// The `UniqueConnec` contains a sender and the protocol version.
	/// The sender can be used to transmit data for the remote. Note that the
	/// packet_id has to be inside the `Bytes`.
	protocols: Vec<(ProtocolId, UniqueConnec<(mpsc::UnboundedSender<Bytes>, u8)>)>,

	/// The Kademlia connection to this node.
	kad_connec: UniqueConnec<KadConnecController>,

	/// The ping connection to this node.
	ping_connec: UniqueConnec<Pinger>,

	/// Id of the peer.
	id: PeerId,

	/// True if this connection was initiated by us.
	/// Note that it is theoretically possible that we dial the remote at the
	/// same time they dial us, in which case the protocols may be dispatched
	/// between both connections, and in which case the value here will be racy.
	originated: bool,

	/// Latest known ping duration.
	ping: Mutex<Option<Duration>>,

	/// The client version of the remote, or `None` if not known.
	client_version: Option<String>,

	/// The multiaddress of the remote, or `None` if not known.
	remote_address: Option<Multiaddr>,

	/// The local multiaddress used to communicate with the remote, or `None`
	/// if not known.
	local_address: Option<Multiaddr>,
}

/// Simplified, POD version of PeerConnectionInfo.
#[derive(Debug, Clone)]
pub struct PeerInfo {
	/// Id of the peer.
	pub id: PeerId,

	/// True if this connection was initiated by us.
	/// Note that it is theoretically possible that we dial the remote at the
	/// same time they dial us, in which case the protocols may be dispatched
	/// between both connections, and in which case the value here will be racy.
	pub originated: bool,

	/// Latest known ping duration.
	pub ping: Option<Duration>,

	/// The client version of the remote, or `None` if not known.
	pub client_version: Option<String>,

	/// The multiaddress of the remote, or `None` if not known.
	pub remote_address: Option<Multiaddr>,

	/// The local multiaddress used to communicate with the remote, or `None`
	/// if not known.
	pub local_address: Option<Multiaddr>,
}

impl<'a> From<&'a PeerConnectionInfo> for PeerInfo {
	fn from(i: &'a PeerConnectionInfo) -> PeerInfo {
		PeerInfo {
			id: i.id.clone(),
			originated: i.originated,
			ping: i.ping.lock().clone(),
			client_version: i.client_version.clone(),
			remote_address: i.remote_address.clone(),
			local_address: i.local_address.clone(),
		}
	}
}

impl NetworkState {
	pub fn new(config: &NetworkConfiguration) -> Result<NetworkState, Error> {
		// Private and public keys configuration.
		let local_private_key = obtain_private_key(&config)?;
		let local_public_key = local_private_key.to_public_key();

		// Build the storage for peers, including the bootstrap nodes.
		let node_store = if let Some(ref path) = config.net_config_path {
			let path = Path::new(path).join(NODES_FILE);
			if let Ok(node_store) = JsonPeerstore::new(path.clone()) {
				debug!(target: "sub-libp2p", "Initialized peer store for JSON file {:?}", path);
				NodeStore::Json(node_store)
			} else {
				warn!(target: "sub-libp2p", "Failed to open peer storage {:?}; peers file will be reset", path);
				fs::remove_file(&path).expect("Failed deleting peers.json");

				// we check for about 1s if the file was really deleted and move on
				for _x in 0..200 {
					if !Path::new(&path).exists() {
						break;
					} else {
						debug!("Waiting for effective deletion of invalid/outdate peers.json");
						thread::sleep(time::Duration::from_millis(5));
					}
				}

				if let Ok(peerstore) = JsonPeerstore::new(path.clone()) {
					debug!("peers.json reset");
					NodeStore::Json(peerstore)
				} else {
					warn!(target: "sub-libp2p",
						"Failed to reset peer storage {:?}; peers change will not be saved",
						path
					);
					NodeStore::Memory(MemoryPeerstore::empty())
				}
			}
		} else {
			debug!(target: "sub-libp2p", "No peers file configured ; peers won't be saved");
			NodeStore::Memory(MemoryPeerstore::empty())
		};

		let reserved_peers = {
			let mut reserved_peers = FnvHashSet::with_capacity_and_hasher(
				config.reserved_nodes.len(),
				Default::default()
			);
			for peer in config.reserved_nodes.iter() {
				let id = parse_and_add_to_node_store(peer, &node_store)?;
				reserved_peers.insert(id);
			}
			RwLock::new(reserved_peers)
		};

		let expected_max_peers = config.max_peers as usize + config.reserved_nodes.len();

		Ok(NetworkState {
			node_store,
			max_outgoing_peers: config.min_peers,
			max_incoming_peers: config.max_peers.saturating_sub(config.min_peers),
			connections: RwLock::new(Connections {
				peer_by_nodeid: FnvHashMap::with_capacity_and_hasher(expected_max_peers, Default::default()),
				info_by_peer: FnvHashMap::with_capacity_and_hasher(expected_max_peers, Default::default()),
			}),
			reserved_only: atomic::AtomicBool::new(false),
			reserved_peers,
			next_node_index: atomic::AtomicUsize::new(0),
			disabled_nodes: Mutex::new(Default::default()),
			local_private_key,
			local_public_key,
		})
	}

	/// Returns the private key of the local node.
	pub fn local_private_key(&self) -> &secio::SecioKeyPair {
		&self.local_private_key
	}

	/// Returns the public key of the local node.
	pub fn local_public_key(&self) -> &PublicKey {
		&self.local_public_key
	}

	/// Returns the ID of a random peer of the network.
	///
	/// Returns `None` if we don't know any peer.
	pub fn random_peer(&self) -> Option<PeerId> {
		// TODO: optimize by putting the operation directly in the node_store
		// https://github.com/libp2p/rust-libp2p/issues/316
		let peers = match self.node_store {
			NodeStore::Memory(ref mem) =>
				mem.peers().collect::<Vec<_>>(),
			NodeStore::Json(ref json) =>
				json.peers().collect::<Vec<_>>(),
		};

		if peers.is_empty() {
			return None
		}

		let nth = rand::random::<usize>() % peers.len();
		Some(peers[nth].clone())
	}

	/// Returns all the IDs of the peers on the network we have knowledge of.
	///
	/// This includes peers we are not connected to.
	pub fn known_peers(&self) -> impl Iterator<Item = PeerId> {
		match self.node_store {
			NodeStore::Memory(ref mem) =>
				mem.peers().collect::<Vec<_>>().into_iter(),
			NodeStore::Json(ref json) =>
				json.peers().collect::<Vec<_>>().into_iter(),
		}
	}

	/// Returns true if we are connected to any peer at all.
	pub fn has_connected_peer(&self) -> bool {
		!self.connections.read().peer_by_nodeid.is_empty()
	}

	/// Get a list of all connected peers by id.
	pub fn connected_peers(&self) -> Vec<NodeIndex> {
		self.connections.read().peer_by_nodeid.values().cloned().collect()
	}

	/// Returns true if the given `NodeIndex` is valid.
	///
	/// `NodeIndex`s are never reused, so once this function returns `false` it
	/// will never return `true` again for the same `NodeIndex`.
	pub fn is_peer_connected(&self, peer: NodeIndex) -> bool {
		self.connections.read().info_by_peer.contains_key(&peer)
	}

	/// Reports the ping of the peer. Returned later by `session_info()`.
	/// No-op if the `who` is not valid/expired.
	pub fn report_ping_duration(&self, who: NodeIndex, ping: Duration) {
		let mut connections = self.connections.write();
		let info = match connections.info_by_peer.get_mut(&who) {
			Some(info) => info,
			None => return,
		};
		*info.ping.lock() = Some(ping);
	}

	/// If we're connected to a peer with the given protocol, returns
	/// information about the connection. Otherwise, returns `None`.
	pub fn session_info(&self, peer: NodeIndex, protocol: ProtocolId) -> Option<SessionInfo> {
		let connections = self.connections.read();
		let info = match connections.info_by_peer.get(&peer) {
			Some(info) => info,
			None => return None,
		};

		let protocol_version = match info.protocols.iter().find(|&(ref p, _)| p == &protocol) {
			Some(&(_, ref unique_connec)) =>
				if let Some(val) = unique_connec.poll() {
					val.1 as u32
				} else {
					return None
				}
			None => return None,
		};

		let ping = info.ping.lock().clone();

		Some(SessionInfo {
			id: None,						// TODO: ???? what to do??? wrong format!
			client_version: info.client_version.clone().take().unwrap_or(String::new()),
			protocol_version,
			capabilities: Vec::new(),		// TODO: list of supported protocols ; hard
			peer_capabilities: Vec::new(),	// TODO: difference with `peer_capabilities`?
			ping,
			originated: info.originated,
			remote_address: info.remote_address.as_ref().map(|a| a.to_string())
				.unwrap_or(String::new()),
			local_address: info.local_address.as_ref().map(|a| a.to_string())
				.unwrap_or(String::new()),
		})
	}

	/// If we're connected to a peer with the given protocol, returns the
	/// protocol version. Otherwise, returns `None`.
	pub fn protocol_version(&self, peer: NodeIndex, protocol: ProtocolId) -> Option<u8> {
		let connections = self.connections.read();
		let peer = match connections.info_by_peer.get(&peer) {
			Some(peer) => peer,
			None => return None,
		};

		peer.protocols.iter()
			.find(|p| p.0 == protocol)
			.and_then(|p| p.1.poll())
			.map(|(_, version)| version)
	}

	/// Equivalent to `session_info(peer).map(|info| info.client_version)`.
	pub fn peer_client_version(&self, peer: NodeIndex, protocol: ProtocolId) -> Option<String> {
		// TODO: implement more directly, without going through `session_info`
		self.session_info(peer, protocol)
			.map(|info| info.client_version)
	}

	/// Adds an address discovered by Kademlia.
	/// Note that we don't have to be connected to a peer to add an address.
	pub fn add_kad_discovered_addr(&self, node_id: &PeerId, addr: Multiaddr) {
		trace!(target: "sub-libp2p", "Peer store: adding address {} for {:?}",
			addr, node_id);
		match self.node_store {
			NodeStore::Memory(ref mem) =>
				mem.peer_or_create(node_id)
					.add_addr(addr, Duration::from_secs(3600)),
			NodeStore::Json(ref json) =>
				json.peer_or_create(node_id)
					.add_addr(addr, Duration::from_secs(3600)),
		}
	}

	/// Signals that an address doesn't match the corresponding node ID.
	/// This removes the address from the peer store, so that it is not
	/// returned by `addrs_of_peer` again in the future.
	pub fn set_invalid_kad_address(&self, node_id: &PeerId, addr: &Multiaddr) {
		// TODO: blacklist the address?
		match self.node_store {
			NodeStore::Memory(ref mem) =>
				if let Some(mut peer) = mem.peer(node_id) {
					peer.rm_addr(addr.clone())		// TODO: cloning necessary?
				},
			NodeStore::Json(ref json) =>
				if let Some(mut peer) = json.peer(node_id) {
					peer.rm_addr(addr.clone())		// TODO: cloning necessary?
				},
		}
	}

	/// Returns the known multiaddresses of a peer.
	pub fn addrs_of_peer(&self, node_id: &PeerId) -> Vec<Multiaddr> {
		match self.node_store {
			NodeStore::Memory(ref mem) =>
				mem.peer(node_id)
					.into_iter()
					.flat_map(|p| p.addrs())
					.collect::<Vec<_>>(),
			NodeStore::Json(ref json) =>
				json.peer(node_id)
					.into_iter()
					.flat_map(|p| p.addrs())
					.collect::<Vec<_>>(),
		}
	}

	/// Sets information about a peer.
	pub fn set_peer_info(
		&self,
		node_id: PeerId,
		endpoint: Endpoint,
		client_version: String,
		local_addr: Multiaddr,
		remote_addr: Multiaddr
	) -> Result<NodeIndex, IoError> {
		let mut connections = self.connections.write();
		let who = accept_connection(&mut connections, &self.next_node_index,
			node_id.clone(), endpoint)?;
		let infos = connections.info_by_peer.get_mut(&who)
			.expect("Newly-created peer id is always valid");

		infos.client_version = Some(client_version);
		infos.remote_address = Some(remote_addr);
		infos.local_address = Some(local_addr);

		Ok(who)
	}

	/// Adds a peer to the internal peer store.
	/// Returns an error if the peer address is invalid.
	pub fn add_peer(&self, peer: &str) -> Result<PeerId, Error> {
		parse_and_add_to_node_store(peer, &self.node_store)
	}

	/// Adds a reserved peer to the list of reserved peers.
	/// Returns an error if the peer address is invalid.
	pub fn add_reserved_peer(&self, peer: &str) -> Result<(), Error> {
		let id = parse_and_add_to_node_store(peer, &self.node_store)?;
		self.reserved_peers.write().insert(id);
		Ok(())
	}

	/// Removes the peer from the list of reserved peers. If we're in reserved mode, drops any
	/// active connection to this peer.
	/// Returns an error if the peer address is invalid.
	pub fn remove_reserved_peer(&self, peer: &str) -> Result<(), Error> {
		let id = parse_and_add_to_node_store(peer, &self.node_store)?;
		self.reserved_peers.write().remove(&id);

		// Dropping the peer if we're in reserved mode.
		if self.reserved_only.load(atomic::Ordering::SeqCst) {
			let mut connections = self.connections.write();
			if let Some(who) = connections.peer_by_nodeid.remove(&id) {
				connections.info_by_peer.remove(&who);
			}
		}

		Ok(())
	}

	/// Set the non-reserved peer mode.
	pub fn set_non_reserved_mode(&self, mode: NonReservedPeerMode) {
		match mode {
			NonReservedPeerMode::Accept =>
				self.reserved_only.store(false, atomic::Ordering::SeqCst),
			NonReservedPeerMode::Deny =>
				// TODO: drop existing peers?
				self.reserved_only.store(true, atomic::Ordering::SeqCst),
		}
	}

	/// Returns the number of new outgoing custom connections to peers to
	/// open. This takes into account the number of active peers.
	pub fn should_open_outgoing_custom_connections(&self) -> u32 {
		if self.reserved_only.load(atomic::Ordering::Relaxed) {
			0
		} else {
			let num_open_custom_connections = num_open_custom_connections(&self.connections.read(), &self.reserved_peers.read());
			self.max_outgoing_peers.saturating_sub(num_open_custom_connections.unreserved_outgoing)
		}
	}

	/// Returns true if we are connected to the given node.
	pub fn has_connection(&self, node_id: &PeerId) -> bool {
		let connections = self.connections.read();
		connections.peer_by_nodeid.contains_key(node_id)
	}

	/// Obtains the `UniqueConnec` corresponding to the Kademlia connection to a peer.
	pub fn kad_connection(
		&self,
		node_id: PeerId
	) -> Result<(NodeIndex, UniqueConnec<KadConnecController>), IoError> {
		// TODO: check that the peer is disabled? should disabling a peer also prevent
		//		 kad from working?
		let mut connections = self.connections.write();
		let who = accept_connection(&mut connections, &self.next_node_index,
			node_id, Endpoint::Listener)?;
		let infos = connections.info_by_peer.get_mut(&who)
			.expect("Newly-created peer id is always valid");
		let connec = infos.kad_connec.clone();
		Ok((who, connec))
	}

	/// Obtains the `UniqueConnec` corresponding to the Ping connection to a peer.
	pub fn ping_connection(
		&self,
		node_id: PeerId
	) -> Result<(NodeIndex, UniqueConnec<Pinger>), IoError> {
		let mut connections = self.connections.write();
		let who = accept_connection(&mut connections, &self.next_node_index,
			node_id, Endpoint::Listener)?;
		let infos = connections.info_by_peer.get_mut(&who)
			.expect("Newly-created peer id is always valid");
		let connec = infos.ping_connec.clone();
		Ok((who, connec))
	}

	/// Cleans up inactive connections and returns a list of
	/// connections to ping.
	pub fn cleanup_and_prepare_ping(
		&self
	) -> Vec<(NodeIndex, PeerId, UniqueConnec<Pinger>)> {
		let mut connections = self.connections.write();
		let connections = &mut *connections;
		let peer_by_nodeid = &mut connections.peer_by_nodeid;
		let info_by_peer = &mut connections.info_by_peer;

		let mut ret = Vec::with_capacity(info_by_peer.len());
		info_by_peer.retain(|&who, infos| {
			// Remove the peer if neither Kad nor any protocol is alive.
			if !infos.kad_connec.is_alive() &&
				!infos.protocols.iter().any(|(_, conn)| conn.is_alive())
			{
				peer_by_nodeid.remove(&infos.id);
				trace!(target: "sub-libp2p", "Cleaning up expired peer \
					#{:?} ({:?})", who, infos.id);
				return false;
			}

			ret.push((who, infos.id.clone(), infos.ping_connec.clone()));
			true
		});
		ret
	}

	/// Try to add a new connection to a node in the list.
	///
	/// Returns a `NodeIndex` to allow further interfacing with this connection.
	/// Note that all `NodeIndex`s are unique and never reused.
	///
	/// Can return an error if we are refusing the connection to the remote.
	///
	/// You must pass an `UnboundedSender` which will be used by the `send`
	/// method. Actually sending the data is not covered by this code.
	///
	/// The various methods of the `NetworkState` that close a connection do
	/// so by dropping this sender.
	pub fn custom_proto(
		&self,
		node_id: PeerId,
		protocol_id: ProtocolId,
		endpoint: Endpoint,
	) -> Result<(NodeIndex, UniqueConnec<(mpsc::UnboundedSender<Bytes>, u8)>), IoError> {
		let mut connections = self.connections.write();

		if is_peer_disabled(&self.disabled_nodes, &node_id) {
			debug!(target: "sub-libp2p", "Refusing node {:?} because it was disabled", node_id);
			return Err(IoError::new(IoErrorKind::PermissionDenied, "disabled peer"))
		}

		let who = accept_connection(&mut connections, &self.next_node_index,
			node_id.clone(), endpoint)?;

		let num_open_connections = num_open_custom_connections(&connections, &self.reserved_peers.read());

		let infos = connections.info_by_peer.get_mut(&who)
			.expect("Newly-created peer id is always valid");

		let node_is_reserved = self.reserved_peers.read().contains(&infos.id);
		if !node_is_reserved {
			if self.reserved_only.load(atomic::Ordering::Relaxed) ||
				(endpoint == Endpoint::Listener &&
				 num_open_connections.unreserved_incoming >= self.max_incoming_peers) ||
				(endpoint == Endpoint::Dialer &&
				 num_open_connections.unreserved_outgoing >= self.max_outgoing_peers)
			{
				debug!(target: "sub-libp2p", "Refusing node {:?} because we reached the max number of peers", node_id);
				return Err(IoError::new(IoErrorKind::PermissionDenied, "maximum number of peers reached"))
			}
		}

		if let Some((_, ref uconn)) = infos.protocols.iter().find(|&(prot, _)| prot == &protocol_id) {
			return Ok((who, uconn.clone()))
		}

		let unique_connec = UniqueConnec::empty();
		infos.protocols.push((protocol_id.clone(), unique_connec.clone()));
		Ok((who, unique_connec))
	}

	/// Sends some data to the given peer, using the sender that was passed
	/// to the `UniqueConnec` of `custom_proto`.
	pub fn send(&self, protocol: ProtocolId, who: NodeIndex, message: Bytes) -> Result<(), Error> {
		if let Some(peer) = self.connections.read().info_by_peer.get(&who) {
			let sender = peer.protocols.iter().find(|elem| elem.0 == protocol)
				.and_then(|e| e.1.poll())
				.map(|e| e.0);
			if let Some(sender) = sender {
				sender.unbounded_send(message)
					.map_err(|err| ErrorKind::Io(IoError::new(IoErrorKind::Other, err)))?;
				Ok(())
			} else {
				// We are connected to this peer, but not with the current
				// protocol.
				debug!(target: "sub-libp2p",
					"Tried to send message to peer {} for which we aren't connected with the requested protocol",
					who
				);
				return Err(ErrorKind::PeerNotFound.into())
			}
		} else {
			debug!(target: "sub-libp2p", "Tried to send message to invalid peer ID {}", who);
			return Err(ErrorKind::PeerNotFound.into())
		}
	}

	/// Get the info on a peer, if there's an active connection.
	pub fn peer_info(&self, who: NodeIndex) -> Option<PeerInfo> {
		self.connections.read().info_by_peer.get(&who).map(Into::into)
	}

	/// Reports that an attempt to make a low-level ping of the peer failed.
	pub fn report_ping_failed(&self, who: NodeIndex) {
		self.drop_peer(who);
	}

	/// Disconnects a peer, if a connection exists (ie. drops the Kademlia
	/// controller, and the senders that were stored in the `UniqueConnec` of
	/// `custom_proto`).
	pub fn drop_peer(&self, who: NodeIndex) {
		let mut connections = self.connections.write();
		if let Some(peer_info) = connections.info_by_peer.remove(&who) {
			trace!(target: "sub-libp2p", "Destroying peer #{} {:?} ; kademlia = {:?} ; num_protos = {:?}",
				who,
				peer_info.id,
				peer_info.kad_connec.is_alive(),
				peer_info.protocols.iter().filter(|c| c.1.is_alive()).count());
			let old = connections.peer_by_nodeid.remove(&peer_info.id);
			debug_assert_eq!(old, Some(who));
		}
	}

	/// Disconnects all the peers.
	/// This destroys all the Kademlia controllers and the senders that were
	/// stored in the `UniqueConnec` of `custom_proto`.
	pub fn disconnect_all(&self) {
		let mut connec = self.connections.write();
		*connec = Connections {
			info_by_peer: FnvHashMap::with_capacity_and_hasher(
				connec.peer_by_nodeid.capacity(), Default::default()),
			peer_by_nodeid: FnvHashMap::with_capacity_and_hasher(
				connec.peer_by_nodeid.capacity(), Default::default()),
		};
	}

	/// Disables a peer for `PEER_DISABLE_DURATION`. This adds the peer to the
	/// list of disabled peers, and  drops any existing connections if
	/// necessary (ie. drops the sender that was stored in the `UniqueConnec`
	/// of `custom_proto`).
	pub fn ban_peer(&self, who: NodeIndex, reason: &str) {
		// TODO: what do we do if the peer is reserved?
		// TODO: same logging as in disconnect_peer
		let mut connections = self.connections.write();
		let peer_info = if let Some(peer_info) = connections.info_by_peer.remove(&who) {
			if let (&Some(ref client_version), &Some(ref remote_address)) = (&peer_info.client_version, &peer_info.remote_address) {
				info!(target: "network", "Peer {} (version: {}, address: {}) disabled. {}", who, client_version, remote_address, reason);
			} else {
				info!(target: "network", "Peer {} disabled. {}", who, reason);
			}
			let old = connections.peer_by_nodeid.remove(&peer_info.id);
			debug_assert_eq!(old, Some(who));
			peer_info
		} else {
			return
		};

		drop(connections);
		let timeout = Instant::now() + PEER_DISABLE_DURATION;
		self.disabled_nodes.lock().insert(peer_info.id.clone(), timeout);
	}

	/// Flushes the caches to the disk.
	///
	/// This is done in an atomical way, so that an error doesn't corrupt
	/// anything.
	pub fn flush_caches_to_disk(&self) -> Result<(), IoError> {
		match self.node_store {
			NodeStore::Memory(_) => Ok(()),
			NodeStore::Json(ref json) =>
				match json.flush() {
					Ok(()) => {
						debug!(target: "sub-libp2p", "Flushed JSON peer store to disk");
						Ok(())
					}
					Err(err) => {
						warn!(target: "sub-libp2p", "Failed to flush changes to JSON peer store: {}", err);
						Err(err)
					}
				}
		}
	}
}

impl Drop for NetworkState {
	fn drop(&mut self) {
		let _ = self.flush_caches_to_disk();
	}
}

/// Assigns a `NodeIndex` to a node, or returns an existing ID if any exists.
///
/// The function only accepts already-locked structs, so that we don't risk
/// any deadlock.
fn accept_connection(
	connections: &mut Connections,
	next_node_index: &atomic::AtomicUsize,
	node_id: PeerId,
	endpoint: Endpoint
) -> Result<NodeIndex, IoError> {
	let peer_by_nodeid = &mut connections.peer_by_nodeid;
	let info_by_peer = &mut connections.info_by_peer;

	let who = *peer_by_nodeid.entry(node_id.clone()).or_insert_with(|| {
		let new_id = next_node_index.fetch_add(1, atomic::Ordering::Relaxed);
		trace!(target: "sub-libp2p", "Creating new peer #{:?} for {:?}", new_id, node_id);

		info_by_peer.insert(new_id, PeerConnectionInfo {
			protocols: Vec::new(),    // TODO: Vec::with_capacity(num_registered_protocols),
			kad_connec: UniqueConnec::empty(),
			ping_connec: UniqueConnec::empty(),
			id: node_id.clone(),
			originated: endpoint == Endpoint::Dialer,
			ping: Mutex::new(None),
			client_version: None,
			local_address: None,
			remote_address: None,
		});
		new_id
	});

	Ok(who)
}

/// Returns true if a peer is disabled.
fn is_peer_disabled(
	list: &Mutex<FnvHashMap<PeerId, Instant>>,
	peer: &PeerId
) -> bool {
	let mut list = list.lock();
	if let Some(timeout) = list.get(peer).cloned() {
		if timeout > Instant::now() {
			true
		} else {
			list.remove(peer);
			false
		}
	} else {
		false
	}
}

struct OpenCustomConnectionsNumbers {
	/// Total number of open and pending connections.
	pub total: u32,
	/// Unreserved incoming number of open and pending connections.
	pub unreserved_incoming: u32,
	/// Unreserved outgoing number of open and pending connections.
	pub unreserved_outgoing: u32,
}

/// Returns the number of open and pending connections with
/// custom protocols.
fn num_open_custom_connections(connections: &Connections, reserved_peers: &FnvHashSet<PeerId>) -> OpenCustomConnectionsNumbers {
	let filtered = connections
		.info_by_peer
		.values()
		.filter(|info|
			info.protocols.iter().any(|&(_, ref connec)|
				match connec.state() {
					UniqueConnecState::Pending | UniqueConnecState::Full => true,
					_ => false
				}
			)
		);

	let mut total: u32 = 0;
	let mut unreserved_incoming: u32 = 0;
	let mut unreserved_outgoing: u32 = 0;

	for info in filtered {
		total += 1;
		let node_is_reserved = reserved_peers.contains(&info.id);
		if !node_is_reserved {
			if !info.originated {
				unreserved_incoming += 1;
			} else {
				unreserved_outgoing += 1;
			}
		}
	}

	OpenCustomConnectionsNumbers {
		total,
		unreserved_incoming,
		unreserved_outgoing,
	}
}

/// Parses an address of the form `/ip4/x.x.x.x/tcp/x/p2p/xxxxxx`, and adds it
/// to the given node_store. Returns the corresponding peer ID.
fn parse_and_add_to_node_store(
	addr_str: &str,
	node_store: &NodeStore
) -> Result<PeerId, Error> {

	let mut addr = addr_str.to_multiaddr().map_err(|_| ErrorKind::AddressParse)?;
	let who = match addr.pop() {
		Some(AddrComponent::P2P(key)) | Some(AddrComponent::IPFS(key)) =>
			PeerId::from_bytes(key).map_err(|_| ErrorKind::AddressParse)?,
		_ => return Err(ErrorKind::AddressParse.into()),
	};

	// Registering the bootstrap node with a TTL of 100000 years   TODO: wrong
	match node_store {
		NodeStore::Memory(ref node_store) =>
			node_store
				.peer_or_create(&who)
				.set_addr_ttl(addr, Duration::from_secs(100000 * 365 * 24 * 3600)),
		NodeStore::Json(ref node_store) =>
			node_store
				.peer_or_create(&who)
				.set_addr_ttl(addr, Duration::from_secs(100000 * 365 * 24 * 3600)),
	}

	Ok(who)
}

/// Obtains or generates the local private key using the configuration.
fn obtain_private_key(config: &NetworkConfiguration)
	-> Result<secio::SecioKeyPair, IoError> {
	if let Some(ref secret) = config.use_secret {
		// Key was specified in the configuration.
		secio::SecioKeyPair::secp256k1_raw_key(&secret[..])
			.map_err(|err| IoError::new(IoErrorKind::InvalidData, err))

	} else {
		if let Some(ref path) = config.net_config_path {
			fs::create_dir_all(Path::new(path))?;

			// Try fetch the key from a the file containing th esecret.
			let secret_path = Path::new(path).join(SECRET_FILE);
			match load_private_key_from_file(&secret_path) {
				Ok(s) => Ok(s),
				Err(err) => {
					// Failed to fetch existing file ; generate a new key
					trace!(target: "sub-libp2p",
						"Failed to load existing secret key file {:?},  generating new key ; err = {:?}",
						secret_path,
						err
					);
					Ok(gen_key_and_try_write_to_file(&secret_path))
				}
			}

		} else {
			// No path in the configuration, nothing we can do except generate
			// a new key.
			let mut key: [u8; 32] = [0; 32];
			rand::rngs::EntropyRng::new().fill(&mut key);
			Ok(secio::SecioKeyPair::secp256k1_raw_key(&key)
				.expect("randomly-generated key with correct len should always be valid"))
		}
	}
}

/// Tries to load a private key from a file located at the given path.
fn load_private_key_from_file<P>(path: P)
	-> Result<secio::SecioKeyPair, IoError>
	where P: AsRef<Path>
	{
	fs::File::open(path)
		.and_then(|mut file| {
			// We are in 2018 and there is still no method on `std::io::Read`
			// that directly returns a `Vec`.
			let mut buf = Vec::new();
			file.read_to_end(&mut buf).map(|_| buf)
		})
		.and_then(|content|
			secio::SecioKeyPair::secp256k1_raw_key(&content)
				.map_err(|err| IoError::new(IoErrorKind::InvalidData, err))
		)
}

/// Generates a new secret key and tries to write it to the given file.
/// Doesn't error if we couldn't open or write to the file.
fn gen_key_and_try_write_to_file<P>(path: P) -> secio::SecioKeyPair
	where P: AsRef<Path> {
	let raw_key: [u8; 32] = rand::rngs::EntropyRng::new().gen();
	let secio_key = secio::SecioKeyPair::secp256k1_raw_key(&raw_key)
		.expect("randomly-generated key with correct len should always be valid");

	// And store the newly-generated key in the file if possible.
	// Errors that happen while doing so are ignored.
	match open_priv_key_file(&path) {
		Ok(mut file) =>
			match file.write_all(&raw_key) {
				Ok(()) => (),
				Err(err) => warn!(target: "sub-libp2p",
					"Failed to write secret key in file {:?} ; err = {:?}",
					path.as_ref(),
					err
				),
			},
		Err(err) => warn!(target: "sub-libp2p",
			"Failed to store secret key in file {:?} ; err = {:?}",
			path.as_ref(),
			err
		),
	}

	secio_key
}

/// Opens a file containing a private key in write mode.
#[cfg(unix)]
fn open_priv_key_file<P>(path: P) -> Result<fs::File, IoError>
	where P: AsRef<Path>
{
	use std::os::unix::fs::OpenOptionsExt;
	fs::OpenOptions::new()
		.write(true)
		.create_new(true)
		.mode(256 | 128)		// 0o600 in decimal
		.open(path)
}
/// Opens a file containing a private key in write mode.
#[cfg(not(unix))]
fn open_priv_key_file<P>(path: P) -> Result<fs::File, IoError>
	where P: AsRef<Path>
{
	fs::OpenOptions::new()
		.write(true)
		.create_new(true)
		.open(path)
}

#[cfg(test)]
mod tests {
	use libp2p::core::{Endpoint, PublicKey};
	use network_state::NetworkState;

	#[test]
	fn refuse_disabled_peer() {
		let state = NetworkState::new(&Default::default()).unwrap();
		let example_peer = PublicKey::Rsa(vec![1, 2, 3, 4]).into_peer_id();

		let (who, _) = state.custom_proto(
			example_peer.clone(),
			[1, 2, 3],
			Endpoint::Dialer
		).unwrap();

		state.ban_peer(who, "Just a test");

		assert!(state.custom_proto(
			example_peer.clone(),
			[1, 2, 3],
			Endpoint::Dialer
		).is_err());
	}
}
