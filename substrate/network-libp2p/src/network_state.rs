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
use libp2p::core::{UniqueConnecState, PeerId as PeerstorePeerId, PublicKey};
use libp2p::kad::KadConnecController;
use libp2p::peerstore::{Peerstore, PeerAccess};
use libp2p::peerstore::json_peerstore::JsonPeerstore;
use libp2p::peerstore::memory_peerstore::MemoryPeerstore;
use libp2p::ping::Pinger;
use libp2p::secio;
use {Error, ErrorKind, NetworkConfiguration, NonReservedPeerMode};
use {PeerId, ProtocolId, SessionInfo};
use parking_lot::{Mutex, RwLock};
use rand::{self, Rng};
use std::cmp;
use std::fs;
use std::io::{Error as IoError, ErrorKind as IoErrorKind, Read, Write};
use std::path::Path;
use std::sync::atomic;
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
	peerstore: PeersStorage,

	/// Active connections.
	connections: RwLock<Connections>,

	/// `min_peers` taken from the configuration.
	min_peers: u32,
	/// `max_peers` taken from the configuration.
	max_peers: u32,

	/// If true, only reserved peers can connect.
	reserved_only: atomic::AtomicBool,
	/// List of the IDs of the reserved peers.
	reserved_peers: RwLock<FnvHashSet<PeerstorePeerId>>,

	/// Each peer gets assigned a new unique ID. This ID increases linearly.
	next_peer_id: atomic::AtomicUsize,

	/// List of the IDs of the disabled peers. These peers will see their
	/// connections refused. Includes the time when the disabling expires.
	disabled_peers: Mutex<FnvHashMap<PeerstorePeerId, Instant>>,

	/// Local private key.
	local_private_key: secio::SecioKeyPair,
	/// Local public key.
	local_public_key: PublicKey,
}

enum PeersStorage {
	/// Peers are stored in memory. Nothing is stored on disk.
	Memory(MemoryPeerstore),
	/// Peers are stored in a JSON file on the disk.
	Json(JsonPeerstore),
}

struct Connections {
	/// For each libp2p peer ID, the ID of the peer in the API we expose.
	/// Also corresponds to the index in `info_by_peer`.
	peer_by_nodeid: FnvHashMap<PeerstorePeerId, usize>,

	/// For each peer ID, information about our connection to this peer.
	info_by_peer: FnvHashMap<PeerId, PeerConnectionInfo>,
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
	id: PeerstorePeerId,

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
	pub id: PeerstorePeerId,

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
		let peerstore = if let Some(ref path) = config.net_config_path {
			let path = Path::new(path).join(NODES_FILE);
			if let Ok(peerstore) = JsonPeerstore::new(path.clone()) {
				debug!(target: "sub-libp2p", "Initialized peer store for JSON \
					file {:?}", path);
				PeersStorage::Json(peerstore)
			} else {
				warn!(target: "sub-libp2p", "Failed to open peer storage {:?} \
					; peers won't be saved", path);
				PeersStorage::Memory(MemoryPeerstore::empty())
			}
		} else {
			debug!(target: "sub-libp2p", "No peers file configured ; peers \
				won't be saved");
			PeersStorage::Memory(MemoryPeerstore::empty())
		};

		let reserved_peers = {
			let mut reserved_peers = FnvHashSet::with_capacity_and_hasher(
				config.reserved_nodes.len(),
				Default::default()
			);
			for peer in config.reserved_nodes.iter() {
				let id = parse_and_add_to_peerstore(peer, &peerstore)?;
				reserved_peers.insert(id);
			}
			RwLock::new(reserved_peers)
		};

		let expected_max_peers = cmp::max(config.max_peers as usize,
			config.reserved_nodes.len());

		Ok(NetworkState {
			peerstore,
			min_peers: config.min_peers,
			max_peers: config.max_peers,
			connections: RwLock::new(Connections {
				peer_by_nodeid: FnvHashMap::with_capacity_and_hasher(expected_max_peers, Default::default()),
				info_by_peer: FnvHashMap::with_capacity_and_hasher(expected_max_peers, Default::default()),
			}),
			reserved_only: atomic::AtomicBool::new(false),
			reserved_peers,
			next_peer_id: atomic::AtomicUsize::new(0),
			disabled_peers: Mutex::new(Default::default()),
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
	pub fn random_peer(&self) -> Option<PeerstorePeerId> {
		// TODO: optimize by putting the operation directly in the peerstore
		// https://github.com/libp2p/rust-libp2p/issues/316
		let peers = match self.peerstore {
			PeersStorage::Memory(ref mem) =>
				mem.peers().collect::<Vec<_>>(),
			PeersStorage::Json(ref json) =>
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
	pub fn known_peers(&self) -> impl Iterator<Item = PeerstorePeerId> {
		match self.peerstore {
			PeersStorage::Memory(ref mem) =>
				mem.peers().collect::<Vec<_>>().into_iter(),
			PeersStorage::Json(ref json) =>
				json.peers().collect::<Vec<_>>().into_iter(),
		}
	}

	/// Returns true if we are connected to any peer at all.
	pub fn has_connected_peer(&self) -> bool {
		!self.connections.read().peer_by_nodeid.is_empty()
	}

	/// Get a list of all connected peers by id.
	pub fn connected_peers(&self) -> Vec<PeerId> {
		self.connections.read().peer_by_nodeid.values().cloned().collect()
	}

	/// Returns true if the given `PeerId` is valid.
	///
	/// `PeerId`s are never reused, so once this function returns `false` it
	/// will never return `true` again for the same `PeerId`.
	pub fn is_peer_connected(&self, peer: PeerId) -> bool {
		self.connections.read().info_by_peer.contains_key(&peer)
	}

	/// Reports the ping of the peer. Returned later by `session_info()`.
	/// No-op if the `peer_id` is not valid/expired.
	pub fn report_ping_duration(&self, peer_id: PeerId, ping: Duration) {
		let connections = self.connections.read();
		let info = match connections.info_by_peer.get(&peer_id) {
			Some(info) => info,
			None => return,
		};

		*info.ping.lock() = Some(ping);
	}

	/// If we're connected to a peer with the given protocol, returns
	/// information about the connection. Otherwise, returns `None`.
	pub fn session_info(&self, peer: PeerId, protocol: ProtocolId)
		-> Option<SessionInfo> {
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
	pub fn protocol_version(&self, peer: PeerId, protocol: ProtocolId)
		-> Option<u8> {
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
	pub fn peer_client_version(&self, peer: PeerId, protocol: ProtocolId)
		-> Option<String> {
		// TODO: implement more directly, without going through `session_info`
		self.session_info(peer, protocol)
			.map(|info| info.client_version)
	}

	/// Adds an address discovered by Kademlia.
	/// Note that we don't have to be connected to a peer to add an address.
	pub fn add_kad_discovered_addr(&self, node_id: &PeerstorePeerId, addr: Multiaddr) {
		trace!(target: "sub-libp2p", "Peer store: adding address {} for {:?}",
			addr, node_id);
		match self.peerstore {
			PeersStorage::Memory(ref mem) =>
				mem.peer_or_create(node_id)
					.add_addr(addr, Duration::from_secs(3600)),
			PeersStorage::Json(ref json) =>
				json.peer_or_create(node_id)
					.add_addr(addr, Duration::from_secs(3600)),
		}
	}

	/// Signals that an address doesn't match the corresponding node ID.
	/// This removes the address from the peer store, so that it is not
	/// returned by `addrs_of_peer` again in the future.
	pub fn set_invalid_kad_address(&self, node_id: &PeerstorePeerId,
		addr: &Multiaddr) {
		// TODO: blacklist the address?
		match self.peerstore {
			PeersStorage::Memory(ref mem) =>
				if let Some(mut peer) = mem.peer(node_id) {
					peer.rm_addr(addr.clone())		// TODO: cloning necessary?
				},
			PeersStorage::Json(ref json) =>
				if let Some(mut peer) = json.peer(node_id) {
					peer.rm_addr(addr.clone())		// TODO: cloning necessary?
				},
		}
	}

	/// Returns the known multiaddresses of a peer.
	pub fn addrs_of_peer(&self, node_id: &PeerstorePeerId) -> Vec<Multiaddr> {
		match self.peerstore {
			PeersStorage::Memory(ref mem) =>
				mem.peer(node_id)
					.into_iter()
					.flat_map(|p| p.addrs())
					.collect::<Vec<_>>(),
			PeersStorage::Json(ref json) =>
				json.peer(node_id)
					.into_iter()
					.flat_map(|p| p.addrs())
					.collect::<Vec<_>>(),
		}
	}

	/// Sets information about a peer.
	pub fn set_peer_info(
		&self,
		node_id: PeerstorePeerId,
		endpoint: Endpoint,
		client_version: String,
		local_addr: Multiaddr,
		remote_addr: Multiaddr
	) -> Result<PeerId, IoError> {
		let mut connections = self.connections.write();
		let peer_id = accept_connection(&mut connections, &self.next_peer_id,
			node_id.clone(), endpoint)?;
		let infos = connections.info_by_peer.get_mut(&peer_id)
			.expect("Newly-created peer id is always valid");

		infos.client_version = Some(client_version);
		infos.remote_address = Some(remote_addr);
		infos.local_address = Some(local_addr);

		Ok(peer_id)
	}

	/// Adds a peer to the internal peer store.
	/// Returns an error if the peer address is invalid.
	pub fn add_peer(&self, peer: &str) -> Result<PeerstorePeerId, Error> {
		parse_and_add_to_peerstore(peer, &self.peerstore)
	}

	/// Adds a reserved peer to the list of reserved peers.
	/// Returns an error if the peer address is invalid.
	pub fn add_reserved_peer(&self, peer: &str) -> Result<(), Error> {
		let id = parse_and_add_to_peerstore(peer, &self.peerstore)?;
		self.reserved_peers.write().insert(id);
		Ok(())
	}

	/// Removes the peer from the list of reserved peers. If we're in reserved mode, drops any
	/// active connection to this peer.
	/// Returns an error if the peer address is invalid.
	pub fn remove_reserved_peer(&self, peer: &str) -> Result<(), Error> {
		let id = parse_and_add_to_peerstore(peer, &self.peerstore)?;
		self.reserved_peers.write().remove(&id);

		// Dropping the peer if we're in reserved mode.
		if self.reserved_only.load(atomic::Ordering::SeqCst) {
			let mut connections = self.connections.write();
			if let Some(peer_id) = connections.peer_by_nodeid.remove(&id) {
				connections.info_by_peer.remove(&peer_id);
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

	/// Returns the number of open and pending connections with
	/// custom protocols.
	pub fn num_open_custom_connections(&self) -> u32 {
		num_open_custom_connections(&self.connections.read())
	}

	/// Returns the number of new outgoing custom connections to peers to
	/// open. This takes into account the number of active peers.
	pub fn should_open_outgoing_custom_connections(&self) -> u32 {
		if self.reserved_only.load(atomic::Ordering::Relaxed) {
			0
		} else {
			self.min_peers.saturating_sub(self.num_open_custom_connections())
		}
	}

	/// Returns true if we are connected to the given node.
	pub fn has_connection(&self, node_id: &PeerstorePeerId) -> bool {
		let connections = self.connections.read();
		connections.peer_by_nodeid.contains_key(node_id)
	}

	/// Obtains the `UniqueConnec` corresponding to the Kademlia connection to a peer.
	pub fn kad_connection(
		&self,
		node_id: PeerstorePeerId
	) -> Result<(PeerId, UniqueConnec<KadConnecController>), IoError> {
		// TODO: check that the peer is disabled? should disabling a peer also prevent
		//		 kad from working?
		let mut connections = self.connections.write();
		let peer_id = accept_connection(&mut connections, &self.next_peer_id,
			node_id, Endpoint::Listener)?;
		let infos = connections.info_by_peer.get_mut(&peer_id)
			.expect("Newly-created peer id is always valid");
		let connec = infos.kad_connec.clone();
		Ok((peer_id, connec))
	}

	/// Obtains the `UniqueConnec` corresponding to the Ping connection to a peer.
	pub fn ping_connection(
		&self,
		node_id: PeerstorePeerId
	) -> Result<(PeerId, UniqueConnec<Pinger>), IoError> {
		let mut connections = self.connections.write();
		let peer_id = accept_connection(&mut connections, &self.next_peer_id,
			node_id, Endpoint::Listener)?;
		let infos = connections.info_by_peer.get_mut(&peer_id)
			.expect("Newly-created peer id is always valid");
		let connec = infos.ping_connec.clone();
		Ok((peer_id, connec))
	}

	/// Cleans up inactive connections and returns a list of
	/// connections to ping.
	pub fn cleanup_and_prepare_ping(
		&self
	) -> Vec<(PeerId, PeerstorePeerId, UniqueConnec<Pinger>)> {
		let mut connections = self.connections.write();
		let connections = &mut *connections;
		let peer_by_nodeid = &mut connections.peer_by_nodeid;
		let info_by_peer = &mut connections.info_by_peer;

		let mut ret = Vec::with_capacity(info_by_peer.len());
		info_by_peer.retain(|&peer_id, infos| {
			// Remove the peer if neither Kad nor any protocol is alive.
			if !infos.kad_connec.is_alive() &&
				!infos.protocols.iter().any(|(_, conn)| conn.is_alive())
			{
				peer_by_nodeid.remove(&infos.id);
				trace!(target: "sub-libp2p", "Cleaning up expired peer \
					#{:?} ({:?})", peer_id, infos.id);
				return false;
			}

			ret.push((peer_id, infos.id.clone(), infos.ping_connec.clone()));
			true
		});
		ret
	}

	/// Try to add a new connection to a node in the list.
	///
	/// Returns a `PeerId` to allow further interfacing with this connection.
	/// Note that all `PeerId`s are unique and never reused.
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
		node_id: PeerstorePeerId,
		protocol_id: ProtocolId,
		endpoint: Endpoint,
	) -> Result<(PeerId, UniqueConnec<(mpsc::UnboundedSender<Bytes>, u8)>), IoError> {
		let mut connections = self.connections.write();

		if is_peer_disabled(&self.disabled_peers, &node_id) {
			debug!(target: "sub-libp2p", "Refusing node {:?} because it was \
				disabled", node_id);
			return Err(IoError::new(IoErrorKind::PermissionDenied,
				"disabled peer"))
		}

		let peer_id = accept_connection(&mut connections, &self.next_peer_id,
			node_id.clone(), endpoint)?;

		let num_open_connections = num_open_custom_connections(&connections);

		let infos = connections.info_by_peer.get_mut(&peer_id)
			.expect("Newly-created peer id is always valid");

		let node_is_reserved = self.reserved_peers.read().contains(&infos.id);
		if !node_is_reserved {
			if self.reserved_only.load(atomic::Ordering::Relaxed) ||
				num_open_connections >= self.max_peers
			{
				debug!(target: "sub-libp2p", "Refusing node {:?} because we \
					reached the max number of peers", node_id);
				return Err(IoError::new(IoErrorKind::PermissionDenied,
					"maximum number of peers reached"))
			}
		}

		if let Some((_, ref uconn)) = infos.protocols.iter().find(|&(prot, _)| prot == &protocol_id) {
			return Ok((peer_id, uconn.clone()))
		}

		let unique_connec = UniqueConnec::empty();
		infos.protocols.push((protocol_id.clone(), unique_connec.clone()));
		Ok((peer_id, unique_connec))
	}

	/// Sends some data to the given peer, using the sender that was passed
	/// to the `UniqueConnec` of `custom_proto`.
	pub fn send(&self, protocol: ProtocolId, peer_id: PeerId, message: Bytes)
		-> Result<(), Error> {
		if let Some(peer) = self.connections.read().info_by_peer.get(&peer_id) {
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
					peer_id
				);
				return Err(ErrorKind::PeerNotFound.into())
			}
		} else {
			debug!(target: "sub-libp2p", "Tried to send message to invalid peer ID {}", peer_id);
			return Err(ErrorKind::PeerNotFound.into())
		}
	}

	/// Get the info on a peer, if there's an active connection.
	pub fn peer_info(&self, who: PeerId) -> Option<PeerInfo> {
		self.connections.read().info_by_peer.get(&who).map(Into::into)
	}

	/// Disconnects a peer, if a connection exists (ie. drops the Kademlia
	/// controller, and the senders that were stored in the `UniqueConnec` of
	/// `custom_proto`).
	pub fn drop_peer(&self, peer_id: PeerId, reason: Option<&str>) {
		let mut connections = self.connections.write();
		if let Some(peer_info) = connections.info_by_peer.remove(&peer_id) {
			if let Some(reason) = reason {
				if let (&Some(ref client_version), &Some(ref remote_address)) = (&peer_info.client_version, &peer_info.remote_address) {
					debug!(target: "sub-libp2p", "Disconnected peer {} (version: {}, address: {}). {}", peer_id, client_version, remote_address, reason);
				} else {
					debug!(target: "sub-libp2p", "Disconnected peer {}. {}", peer_id, reason);
				}
			}

			trace!(target: "sub-libp2p", "Destroying peer #{} {:?} ; \
				kademlia = {:?} ; num_protos = {:?}", peer_id, peer_info.id,
				peer_info.kad_connec.is_alive(),
				peer_info.protocols.iter().filter(|c| c.1.is_alive()).count());
			// TODO: we manually clear the connections as a work-around for
			// networking bugs ; normally it should automatically drop
			for c in peer_info.protocols.iter() { c.1.clear(); }
			peer_info.kad_connec.clear();
			let old = connections.peer_by_nodeid.remove(&peer_info.id);
			debug_assert_eq!(old, Some(peer_id));
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
	pub fn disable_peer(&self, peer_id: PeerId, reason: &str) {
		// TODO: what do we do if the peer is reserved?
		// TODO: same logging as in disconnect_peer
		let mut connections = self.connections.write();
		let peer_info = if let Some(peer_info) = connections.info_by_peer.remove(&peer_id) {
			if let (&Some(ref client_version), &Some(ref remote_address)) = (&peer_info.client_version, &peer_info.remote_address) {
				info!(target: "network", "Peer {} (version: {}, address: {}) disabled. {}", peer_id, client_version, remote_address, reason);
			} else {
				info!(target: "network", "Peer {} disabled. {}", peer_id, reason);
			}
			let old = connections.peer_by_nodeid.remove(&peer_info.id);
			debug_assert_eq!(old, Some(peer_id));
			peer_info
		} else {
			return
		};

		drop(connections);
		let timeout = Instant::now() + PEER_DISABLE_DURATION;
		self.disabled_peers.lock().insert(peer_info.id.clone(), timeout);
	}

	/// Flushes the caches to the disk.
	///
	/// This is done in an atomical way, so that an error doesn't corrupt
	/// anything.
	pub fn flush_caches_to_disk(&self) -> Result<(), IoError> {
		match self.peerstore {
			PeersStorage::Memory(_) => Ok(()),
			PeersStorage::Json(ref json) =>
				match json.flush() {
					Ok(()) => {
						debug!(target: "sub-libp2p", "Flushed JSON peer store \
							to disk");
						Ok(())
					}
					Err(err) => {
						warn!(target: "sub-libp2p", "Failed to flush changes \
							to JSON peer store: {}", err);
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

/// Assigns a `PeerId` to a node, or returns an existing ID if any exists.
///
/// The function only accepts already-locked structs, so that we don't risk
/// any deadlock.
fn accept_connection(
	connections: &mut Connections,
	next_peer_id: &atomic::AtomicUsize,
	node_id: PeerstorePeerId,
	endpoint: Endpoint
) -> Result<PeerId, IoError> {
	let peer_by_nodeid = &mut connections.peer_by_nodeid;
	let info_by_peer = &mut connections.info_by_peer;

	let peer_id = *peer_by_nodeid.entry(node_id.clone()).or_insert_with(|| {
		let new_id = next_peer_id.fetch_add(1, atomic::Ordering::Relaxed);
		trace!(target: "sub-libp2p", "Creating new peer #{:?} for {:?}",
			new_id, node_id);

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

	Ok(peer_id)
}

/// Returns true if a peer is disabled.
fn is_peer_disabled(
	list: &Mutex<FnvHashMap<PeerstorePeerId, Instant>>,
	peer: &PeerstorePeerId
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

/// Returns the number of open and pending connections with
/// custom protocols.
fn num_open_custom_connections(connections: &Connections) -> u32 {
	connections
		.info_by_peer
		.values()
		.filter(|info|
			info.protocols.iter().any(|&(_, ref connec)|
				match connec.state() {
					UniqueConnecState::Pending | UniqueConnecState::Full => true,
					_ => false
				}
			)
		)
		.count() as u32
}

/// Parses an address of the form `/ip4/x.x.x.x/tcp/x/p2p/xxxxxx`, and adds it
/// to the given peerstore. Returns the corresponding peer ID.
fn parse_and_add_to_peerstore(addr_str: &str, peerstore: &PeersStorage)
	-> Result<PeerstorePeerId, Error> {

	let mut addr = addr_str.to_multiaddr().map_err(|_| ErrorKind::AddressParse)?;
	let peer_id = match addr.pop() {
		Some(AddrComponent::P2P(key)) | Some(AddrComponent::IPFS(key)) =>
			PeerstorePeerId::from_bytes(key).map_err(|_| ErrorKind::AddressParse)?,
		_ => return Err(ErrorKind::AddressParse.into()),
	};

	// Registering the bootstrap node with a TTL of 100000 years   TODO: wrong
	match peerstore {
		PeersStorage::Memory(ref peerstore) =>
			peerstore
				.peer_or_create(&peer_id)
				.add_addr(addr, Duration::from_secs(100000 * 365 * 24 * 3600)),
		PeersStorage::Json(ref peerstore) =>
			peerstore
				.peer_or_create(&peer_id)
				.add_addr(addr, Duration::from_secs(100000 * 365 * 24 * 3600)),
	}
	
	Ok(peer_id)
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
					trace!(target: "sub-libp2p", "Failed to load existing \
						secret key file {:?},  generating new key ; err = {:?}",
						secret_path, err);
					Ok(gen_key_and_try_write_to_file(&secret_path))
				}
			}

		} else {
			// No path in the configuration, nothing we can do except generate
			// a new key.
			let mut key: [u8; 32] = [0; 32];
			rand::rngs::EntropyRng::new().fill(&mut key);
			Ok(secio::SecioKeyPair::secp256k1_raw_key(&key)
				.expect("randomly-generated key with correct len should \
					always be valid"))
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
				Err(err) => warn!(target: "sub-libp2p", "Failed to write \
					secret key in file {:?} ; err = {:?}", path.as_ref(), err),
			},
		Err(err) =>
			warn!(target: "sub-libp2p", "Failed to store secret key in file \
				{:?} ; err = {:?}", path.as_ref(), err),
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

		let (peer_id, _) = state.custom_proto(
			example_peer.clone(),
			[1, 2, 3],
			Endpoint::Dialer
		).unwrap();

		state.disable_peer(peer_id, "Just a test");

		assert!(state.custom_proto(
			example_peer.clone(),
			[1, 2, 3],
			Endpoint::Dialer
		).is_err());
	}
}
