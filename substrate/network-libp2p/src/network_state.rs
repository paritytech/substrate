// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

use bytes::Bytes;
use fnv::{FnvHashMap, FnvHashSet};
use futures::sync::mpsc;
use libp2p::core::{Multiaddr, AddrComponent, Endpoint, PeerId as PeerstorePeerId, PublicKey};
use libp2p::peerstore::{Peerstore, PeerAccess};
use libp2p::peerstore::json_peerstore::JsonPeerstore;
use libp2p::peerstore::memory_peerstore::MemoryPeerstore;
use libp2p::secio;
use network::{Error, ErrorKind, NetworkConfiguration, NonReservedPeerMode};
use network::{PeerId, ProtocolId, SessionInfo};
use parking_lot::{Mutex, RwLock};
use rand::{self, Rng};
use std::cmp;
use std::fs::File;
use std::io::{Error as IoError, ErrorKind as IoErrorKind, Read, Write};
use std::path::Path;
use std::sync::atomic;
use std::time::Duration;

// File where the peers are stored.
const NODES_FILE: &str = "nodes.json";
// File where the private key is stored.
const SECRET_FILE: &str = "secret";

// Common struct shared throughout all the components of the service.
pub struct NetworkState {
	// Contains the information about the network.
	peerstore: PeersStorage,

	// Active connections.
	connections: RwLock<Connections>,

	// `min_peers` taken from the configuration.
	min_peers: u32,
	// `max_peers` taken from the configuration.
	max_peers: u32,

	// If true, only reserved peers can connect.
	reserved_only: atomic::AtomicBool,
	// List of the IDs of the reserved peers.
	reserved_peers: RwLock<FnvHashSet<PeerstorePeerId>>,

	// Each peer gets assigned a new unique ID. This ID increases linearly.
	next_peer_id: atomic::AtomicUsize,

	// List of the IDs of the disabled peers. These peers will see their connections refused.
	disabled_peers: RwLock<FnvHashSet<PeerstorePeerId>>,

	// Local private key.
	local_private_key: secio::SecioKeyPair,
	// Local public key.
	local_public_key: PublicKey,
}

enum PeersStorage {
	// Peers are stored in memory. Nothing is stored on disk.
	Memory(MemoryPeerstore),
	// Peers are stored in a JSON file on the disk.
	Json(JsonPeerstore),
}

struct Connections {
	// For each libp2p peer ID, the ID of the peer in the API we expose.
	// Also corresponds to the index in `info_by_peer`.
	peer_by_nodeid: FnvHashMap<PeerstorePeerId, usize>,

	// For each peer ID, information about our connection to this peer.
	info_by_peer: FnvHashMap<PeerId, PeerConnectionInfo>,
}

struct PeerConnectionInfo {
	// A list of message senders per protocol, and the protocol version.
	// The sender can be used to transmit data for the remote. Note that the packet_id has to be
	// inside the `Bytes`.
	// Closing the sender will drop the substream of this protocol.
	senders: Vec<(ProtocolId, mpsc::UnboundedSender<Bytes>, u8)>,

	// Id of the peer.
	id: PeerstorePeerId,

	// True if this connection was initiated by us.
	// Note that it is theoretically possible that we dial the remote at the same time they dial
	// us, in which case the protocols may be dispatched between both connections, and in which
	// case the value here will be racy.
	originated: bool,

	// Latest known ping duration.
	ping: Mutex<Option<Duration>>,

	// The client version of the remote, or `None` if not known.
	client_version: Option<String>,

	// The multiaddress of the remote, or `None` if not known.
	remote_address: Option<Multiaddr>,

	// The local multiaddress used to communicate with the remote, or `None` if not known.
	local_address: Option<Multiaddr>,
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
				debug!(target: "sub-libp2p", "Initialized peer store for JSON file {:?}", path);
				PeersStorage::Json(peerstore)
			} else {
				warn!(target: "sub-libp2p", "Failed to open peer storage {:?} ; peers won't \
											be saved", path);
				PeersStorage::Memory(MemoryPeerstore::empty())
			}
		} else {
			debug!(target: "sub-libp2p", "No peers file configured ; peers won't be saved");
			PeersStorage::Memory(MemoryPeerstore::empty())
		};

		for bootnode in config.boot_nodes.iter() {
			parse_and_add_to_peerstore(bootnode, &peerstore)?;
		}

		let reserved_peers = {
			let mut reserved_peers = FnvHashSet::with_capacity_and_hasher(config.reserved_nodes.len(), Default::default());
			for peer in config.reserved_nodes.iter() {
				let id = parse_and_add_to_peerstore(peer, &peerstore)?;
				reserved_peers.insert(id);
			}
			RwLock::new(reserved_peers)
		};

		let expected_max_peers = cmp::max(config.max_peers as usize, config.reserved_nodes.len());

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
			disabled_peers: RwLock::new(Default::default()),
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

	/// Returns all the IDs of the peer we have knowledge of.
	///
	/// This includes peers we are not connected to.
	pub fn known_peers(&self) -> impl Iterator<Item = PeerstorePeerId> {
		match self.peerstore {
			PeersStorage::Memory(ref mem) => mem.peers().collect::<Vec<_>>().into_iter(),
			PeersStorage::Json(ref json) => json.peers().collect::<Vec<_>>().into_iter(),
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
	/// `PeerId`s are never reused, so once this function returns `false` it will never return
	/// `true` again for the same `PeerId`.
	pub fn is_peer_connected(&self, peer: PeerId) -> bool {
		self.connections.read().info_by_peer.contains_key(&peer)
	}

	/// Reports the ping of the peer. Returned later by `session_info()`.
	/// No-op if the `peer_id` is not valid/expired.
	pub fn report_ping(&self, peer_id: PeerId, ping: Duration) {
		let connections = self.connections.read();
		let info = match connections.info_by_peer.get(&peer_id) {
			Some(info) => info,
			None => return,
		};

		*info.ping.lock() = Some(ping);
	}

	/// If we're connected to a peer with the given protocol, returns information about the
	/// connection. Otherwise, returns `None`.
	pub fn session_info(&self, peer: PeerId, protocol: ProtocolId) -> Option<SessionInfo> {
		let connections = self.connections.read();
		let info = match connections.info_by_peer.get(&peer) {
			Some(info) => info,
			None => return None,
		};

		let protocol_version = match info.senders.iter().find(|&(ref p, _, _)| p == &protocol) {
			Some(&(_, _, version)) => version as u32,
			None => return None,
		};

		/*let node_id = self.peer_by_nodeid.read().iter()
			.find(|&(_, &p)| p == peer)
			.map(|n| n.clone());*/

		let ping = info.ping.lock().clone();

		Some(SessionInfo {
			id: None,						// TODO: ???? what to do??? wrong format!
			client_version: info.client_version.clone().take().unwrap_or(String::new()),
			protocol_version,
			capabilities: Vec::new(),		// TODO: list of supported protocols ; hard
			peer_capabilities: Vec::new(),	// TODO: difference with `peer_capabilities`?
			ping,
			originated: info.originated,
			remote_address: info.remote_address.as_ref().map(|a| a.to_string()).unwrap_or(String::new()),
			local_address: info.local_address.as_ref().map(|a| a.to_string()).unwrap_or(String::new()),
		})
	}

	/// If we're connected to a peer with the given protocol, returns the protocol version.
	/// Otherwise, returns `None`.
	pub fn protocol_version(&self, peer: PeerId, protocol: ProtocolId) -> Option<u8> {
		let connections = self.connections.read();
		let peer = match connections.info_by_peer.get(&peer) {
			Some(peer) => peer,
			None => return None,
		};

		peer.senders.iter().find(|p| p.0 == protocol).map(|p| p.2)
	}

	/// Equivalent to `session_info(peer).map(|info| info.client_version)`.
	pub fn peer_client_version(&self, peer: PeerId, protocol: ProtocolId) -> Option<String> {
		// TODO: implement more directly, without going through `session_info`
		self.session_info(peer, protocol)
			.map(|info| info.client_version)
	}

	/// Adds an address discovered by Kademlia.
	/// Note that we don't have to be connected to a peer to add an address to it.
	pub fn add_kad_discovered_addr(&self, node_id: &PeerstorePeerId, addr: Multiaddr) {
		match self.peerstore {
			PeersStorage::Memory(ref mem) => {
				mem.peer_or_create(node_id)
					.add_addr(addr, Duration::from_secs(3600))
			}
			PeersStorage::Json(ref json) => {
				json.peer_or_create(node_id)
					.add_addr(addr, Duration::from_secs(3600))
			}
		}
	}

	/// Signals that an address doesn't match the corresponding node ID.
	/// This removes the address from the peer store, so that it is not returned by `addrs_of_peer`
	/// again in the future.
	pub fn set_invalid_kad_address(&self, node_id: &PeerstorePeerId, addr: &Multiaddr) {
		// TODO: blacklist the address?
		match self.peerstore {
			PeersStorage::Memory(ref mem) => {
				if let Some(mut peer) = mem.peer(node_id) {
					peer.rm_addr(addr.clone())		// TODO: cloning necessary?
				}
			}
			PeersStorage::Json(ref json) => {
				if let Some(mut peer) = json.peer(node_id) {
					peer.rm_addr(addr.clone())		// TODO: cloning necessary?
				}
			}
		}
	}

	/// Returns the known multiaddresses of a peer.
	pub fn addrs_of_peer(&self, node_id: &PeerstorePeerId) -> Vec<Multiaddr> {
		match self.peerstore {
			PeersStorage::Memory(ref mem) => {
				mem
					.peer(node_id)
					.into_iter()
					.flat_map(|p| p.addrs())
					.collect::<Vec<_>>()
			}
			PeersStorage::Json(ref json) => {
				json
					.peer(node_id)
					.into_iter()
					.flat_map(|p| p.addrs())
					.collect::<Vec<_>>()
			}
		}
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
			NonReservedPeerMode::Accept => {
				self.reserved_only.store(false, atomic::Ordering::SeqCst);
			},
			NonReservedPeerMode::Deny => {
				self.reserved_only.store(true, atomic::Ordering::SeqCst);
				// TODO: drop existing peers?
			},
		}
	}

	/// Returns true if reserved mode is enabled.
	pub fn is_reserved_only(&self) -> bool {
		self.reserved_only.load(atomic::Ordering::Relaxed)
	}

	/// Returns true if we should open a new outgoing connection to a peer.
	/// This takes into account the number of active peers.
	pub fn should_open_outgoing_connecs(&self) -> bool {
		!self.reserved_only.load(atomic::Ordering::Relaxed) &&
			self.connections.read().peer_by_nodeid.len() < self.min_peers as usize
	}

	/// Returns true if we are connected to the given node.
	pub fn has_connection(&self, node_id: &PeerstorePeerId) -> bool {
		let connections = self.connections.read();
		connections.peer_by_nodeid.contains_key(node_id)
	}

	/// Try to add a new connection to a node in the list.
	///
	/// Returns a `PeerId` to allow further interfacing with this connection. Note that all
	/// `PeerId`s are unique and never reused.
	///
	/// Can return an error if we are refusing the connection to the remote.
	///
	/// You must pass an `UnboundedSender` which will be used by the `send` method. Actually
	/// sending the data is not covered by this code.
	///
	/// The various methods of the `NetworkState` that close a connection do so by dropping this
	/// sender.
	pub fn accept_connection(&self, node_id: PeerstorePeerId, protocol_id: ProtocolId, protocol_version: u8, endpoint: Endpoint, msg_tx: mpsc::UnboundedSender<Bytes>) -> Result<PeerId, IoError> {
		if self.disabled_peers.read().contains(&node_id) {
			debug!(target: "sub-libp2p", "Refusing node {:?} because it was disabled", node_id);
			return Err(IoError::new(IoErrorKind::PermissionDenied, "disabled peer"));
		}

		let node_is_reserved = self.reserved_peers.read().contains(&node_id);

		let mut connections = self.connections.write();
		let connections = &mut *connections;
		let peer_by_nodeid = &mut connections.peer_by_nodeid;
		let info_by_peer = &mut connections.info_by_peer;

		if !node_is_reserved {
			if self.reserved_only.load(atomic::Ordering::Relaxed) ||
				peer_by_nodeid.len() >= self.max_peers as usize
			{
				debug!(target: "sub-libp2p", "Refusing node {:?} because we reached the max \
												number of peers", node_id);
				return Err(IoError::new(IoErrorKind::PermissionDenied, "maximum number of peers reached"));
			}
		}

		let peer_id = *peer_by_nodeid.entry(node_id.clone()).or_insert_with(|| {
			let new_id = self.next_peer_id.fetch_add(1, atomic::Ordering::Relaxed);
			info_by_peer.insert(new_id, PeerConnectionInfo {
				senders: Vec::new(),    // TODO: Vec::with_capacity(num_registered_protocols),
				id: node_id.clone(),
				originated: endpoint == Endpoint::Dialer,
				ping: Mutex::new(None),
				client_version: None,
				local_address: None,
				remote_address: None,
			});
			new_id
		});

		let senders = &mut info_by_peer.get_mut(&peer_id).expect("network state inconsistency").senders;
		if !senders.iter().any(|&(prot, _, _)| prot == protocol_id) {
			senders.push((protocol_id.clone(), msg_tx, protocol_version));
		}

		Ok(peer_id)
	}

	/// Sends some data to the given peer, using the sender that was passed to `accept_connection`.
	pub fn send(&self, protocol: ProtocolId, peer_id: PeerId, message: Bytes) -> Result<(), Error> {
		if let Some(peer) = self.connections.read().info_by_peer.get(&peer_id) {
			if let Some(sender) = peer.senders.iter().find(|elem| elem.0 == protocol).map(|e| &e.1) {
				sender.unbounded_send(message)
					.map_err(|err| {
						ErrorKind::Io(IoError::new(IoErrorKind::Other, err))
					})?;
				Ok(())

			} else {
				// We are connected to this peer, but not with the current protocol.
				debug!(target: "sub-libp2p", "Tried to send message to peer {} for which we aren't \
					connected with the requested protocol", peer_id);
				return Err(ErrorKind::PeerNotFound.into());
			}
		} else {
			debug!(target: "sub-libp2p", "Tried to send message to invalid peer ID {}", peer_id);
			return Err(ErrorKind::PeerNotFound.into());
		}
	}

	/// Disconnects a peer, if a connection exists (ie. drops the sender that was passed to
	/// `accept_connection`).
	pub fn disconnect_peer(&self, peer_id: PeerId) {
		let mut connections = self.connections.write();
		if let Some(peer_info) = connections.info_by_peer.remove(&peer_id) {
			let old = connections.peer_by_nodeid.remove(&peer_info.id);
			debug_assert_eq!(old, Some(peer_id));
		}
	}

	/// Disconnects all the peers.
	/// This destroys all the senders that were passed to `accept_connection`.
	pub fn disconnect_all(&self) {
		let mut connec = self.connections.write();
		*connec = Connections {
			info_by_peer: FnvHashMap::with_capacity_and_hasher(connec.peer_by_nodeid.capacity(), Default::default()),
			peer_by_nodeid: FnvHashMap::with_capacity_and_hasher(connec.peer_by_nodeid.capacity(), Default::default()),
		};
	}

	/// Disables a peer. This adds the peer to the list of disabled peers, and drops any existing
	/// connections if necessary (ie. drops the sender that was passed to `accept_connection`).
	pub fn disable_peer(&self, peer_id: PeerId) {
		// TODO: what do we do if the peer is reserved?
		let mut connections = self.connections.write();
		let peer_info = if let Some(peer_info) = connections.info_by_peer.remove(&peer_id) {
			let old = connections.peer_by_nodeid.remove(&peer_info.id);
			debug_assert_eq!(old, Some(peer_id));
			peer_info
		} else {
			return;
		};

		drop(connections);
		self.disabled_peers.write().insert(peer_info.id.clone());
	}

	/// Returns true if a peer is disabled.
	pub fn is_peer_disabled(&self, node_id: &PeerstorePeerId) -> bool {
		self.disabled_peers.read().contains(&node_id)
	}
}

impl Drop for NetworkState {
	fn drop(&mut self) {
		match self.peerstore {
			PeersStorage::Memory(_) => (),
			PeersStorage::Json(ref json) => {
				match json.flush() {
					Ok(()) => {
						debug!(target: "sub-libp2p", "Flushed JSON peer store to disk");
					}
					Err(err) => {
						warn!(target: "sub-libp2p", "Failed to flush changes to JSON \
													peer store: {}", err);
					}
				}
			}
		}
	}
}

// Parses an address of the form `/ip4/x.x.x.x/tcp/x/p2p/xxxxxx`, and adds it to the given
// peerstore. Returns the corresponding peer ID.
fn parse_and_add_to_peerstore(addr_str: &str, peerstore: &PeersStorage)
	-> Result<PeerstorePeerId, Error>
{
	let mut addr: Multiaddr = addr_str.parse().map_err(|_| ErrorKind::AddressParse)?;
	let p2p_component = addr.pop().ok_or(ErrorKind::AddressParse)?;
	let peer_id = match p2p_component {
		AddrComponent::P2P(key) | AddrComponent::IPFS(key) => {
			PeerstorePeerId::from_bytes(key).map_err(|_| ErrorKind::AddressParse)?
		}
		_ => return Err(ErrorKind::BadProtocol.into()),
	};

	// Registering the bootstrap node with a TTL of 100000 years   TODO: wrong
	match peerstore {
		PeersStorage::Memory(ref peerstore) => {
			peerstore
				.peer_or_create(&peer_id)
				.add_addr(addr, Duration::from_secs(100000 * 365 * 24 * 3600));
		}
		PeersStorage::Json(ref peerstore) => {
			peerstore
				.peer_or_create(&peer_id)
				.add_addr(addr, Duration::from_secs(100000 * 365 * 24 * 3600));
		}
	}
	
	Ok(peer_id)
}

// Obtains or generates the private key.
fn obtain_private_key(config: &NetworkConfiguration) -> Result<secio::SecioKeyPair, IoError> {
	Ok(if let Some(ref secret) = config.use_secret {
		secio::SecioKeyPair::secp256k1_raw_key(&secret[..])
			.map_err(|err| IoError::new(IoErrorKind::InvalidData, err))?
	} else {
		if let Some(ref path) = config.net_config_path {
			let secret_path = Path::new(path).join(SECRET_FILE);
			let loaded_secret = File::open(&secret_path)
				.and_then(|mut file| {
					// We are in 2018 and there is still no method on `std::io::Read` that
					// directly returns a `Vec`.
					let mut buf = Vec::new();
					file.read_to_end(&mut buf).map(|_| buf)
				})
				.and_then(|content| {
					secio::SecioKeyPair::secp256k1_raw_key(&content)
						.map_err(|err| IoError::new(IoErrorKind::InvalidData, err))
				});

			if let Ok(loaded_secret) = loaded_secret {
				loaded_secret
			} else {
				let raw_key: [u8; 32] = rand::rngs::EntropyRng::new().gen();
				let secio_key = secio::SecioKeyPair::secp256k1_raw_key(&raw_key)
					.map_err(|err| IoError::new(IoErrorKind::InvalidData, err))?;
				if let Ok(mut file) = File::create(&secret_path) {
					let _ = file.write_all(&raw_key);
				}
				secio_key
			}

		} else {
			let mut key: [u8; 32] = [0; 32];
			rand::rngs::EntropyRng::new().fill(&mut key);
			secio::SecioKeyPair::secp256k1_raw_key(&key)
				.map_err(|err| IoError::new(IoErrorKind::InvalidData, err))?
		}
	})
}

#[cfg(test)]
mod tests {
	use futures::sync::mpsc;
	use libp2p::core::{Endpoint, PublicKey};
	use network_state::NetworkState;

	#[test]
	fn refuse_disabled_peer() {
		let state = NetworkState::new(&Default::default()).unwrap();
		let example_peer = PublicKey::Rsa(vec![1, 2, 3, 4]).into_peer_id();

		let peer_id = state.accept_connection(example_peer.clone(), [1, 2, 3], 1, Endpoint::Dialer, mpsc::unbounded().0).unwrap();
		state.disable_peer(peer_id);

		assert!(state.accept_connection(example_peer.clone(), [1, 2, 3], 1, Endpoint::Dialer, mpsc::unbounded().0).is_err());
	}
}
