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

use crate::{
	behaviour::Behaviour, behaviour::BehaviourOut, secret::obtain_private_key_from_config,
	transport
};
use crate::custom_proto::{RegisteredProtocol, RegisteredProtocols};
use crate::topology::NetTopology;
use crate::{Error, NetworkConfiguration, NodeIndex, ProtocolId, parse_str_addr};
use bytes::Bytes;
use fnv::FnvHashMap;
use futures::{prelude::*, Stream};
use libp2p::{multiaddr::Protocol, Multiaddr, PeerId, multiaddr};
use libp2p::core::{Swarm, nodes::Substream, transport::boxed::Boxed, muxing::StreamMuxerBox};
use libp2p::core::nodes::ConnectedPoint;
use log::{debug, info, warn};
use std::collections::hash_map::Entry;
use std::fs;
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
use std::net::SocketAddr;
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;
use tokio_timer::Interval;

// File where the network topology is stored.
const NODES_FILE: &str = "nodes.json";

/// Starts the substrate libp2p service.
///
/// Returns a stream that must be polled regularly in order for the networking to function.
pub fn start_service<TProtos>(
	config: NetworkConfiguration,
	registered_custom: TProtos,
) -> Result<Service, Error>
where TProtos: IntoIterator<Item = RegisteredProtocol> {

	if let Some(ref path) = config.net_config_path {
		fs::create_dir_all(Path::new(path))?;
	}

	// Private and public keys configuration.
	let local_private_key = obtain_private_key_from_config(&config)?;
	let local_public_key = local_private_key.to_public_key();
	let local_peer_id = local_public_key.clone().into_peer_id();

	// Initialize the topology of the network.
	let mut topology = if let Some(ref path) = config.net_config_path {
		let path = Path::new(path).join(NODES_FILE);
		debug!(target: "sub-libp2p", "Initializing peer store for JSON file {:?}", path);
		NetTopology::from_file(local_public_key, path)
	} else {
		debug!(target: "sub-libp2p", "No peers file configured ; peers won't be saved");
		NetTopology::memory(local_public_key)
	};

	// Register the external addresses provided by the user as our own.
	topology.add_external_addrs(config.public_addresses.clone().into_iter());

	// Build the swarm.
	let (mut swarm, bandwidth) = {
		let registered_custom = RegisteredProtocols(registered_custom.into_iter().collect());
		let behaviour = Behaviour::new(&config, local_peer_id.clone(), registered_custom);
		let (transport, bandwidth) = transport::build_transport(local_private_key);
		(Swarm::new(transport, behaviour, topology), bandwidth)
	};

	// Listen on multiaddresses.
	for addr in &config.listen_addresses {
		match Swarm::listen_on(&mut swarm, addr.clone()) {
			Ok(mut new_addr) => {
				new_addr.append(Protocol::P2p(local_peer_id.clone().into()));
				info!(target: "sub-libp2p", "Local node address is: {}", new_addr);
			},
			Err(err) => warn!(target: "sub-libp2p", "Can't listen on {} because: {:?}", addr, err)
		}
	}

	// Add the bootstrap nodes to the topology and connect to them.
	for bootnode in config.boot_nodes.iter() {
		match parse_str_addr(bootnode) {
			Ok((peer_id, addr)) => {
				Swarm::topology_mut(&mut swarm).add_bootstrap_addr(&peer_id, addr.clone());
				Swarm::dial(&mut swarm, peer_id);
			},
			Err(_) => {
				// If the format of the bootstrap node is not a multiaddr, try to parse it as
				// a `SocketAddr`. This corresponds to the format `IP:PORT`.
				let addr = match bootnode.parse::<SocketAddr>() {
					Ok(SocketAddr::V4(socket)) => multiaddr![Ip4(*socket.ip()), Tcp(socket.port())],
					Ok(SocketAddr::V6(socket)) => multiaddr![Ip6(*socket.ip()), Tcp(socket.port())],
					_ => {
						warn!(target: "sub-libp2p", "Not a valid bootnode address: {}", bootnode);
						continue
					}
				};

				info!(target: "sub-libp2p", "Dialing {} with no peer id. Keep in mind that doing \
					so is vulnerable to man-in-the-middle attacks.", addr);
				if let Err(addr) = Swarm::dial_addr(&mut swarm, addr) {
					warn!(target: "sub-libp2p", "Bootstrap address not supported: {}", addr)
				}
			},
		}
	}

	// Initialize the reserved peers.
	for reserved in config.reserved_nodes.iter() {
		if let Ok((peer_id, addr)) = parse_str_addr(reserved) {
			Swarm::topology_mut(&mut swarm).add_bootstrap_addr(&peer_id, addr);
			swarm.add_reserved_peer(peer_id.clone());
			Swarm::dial(&mut swarm, peer_id);
		} else {
			warn!(target: "sub-libp2p", "Not a valid reserved node address: {}", reserved);
		}
	}

	debug!(target: "sub-libp2p", "Topology started with {} entries",
		Swarm::topology_mut(&mut swarm).num_peers());

	Ok(Service {
		swarm,
		bandwidth,
		nodes_info: Default::default(),
		index_by_id: Default::default(),
		next_node_id: 1,
		cleanup: Interval::new_interval(Duration::from_secs(60)),
		injected_events: Vec::new(),
	})
}

/// Event produced by the service.
#[derive(Debug)]
pub enum ServiceEvent {
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

	/// The substream with a node is clogged. We should avoid sending data to it if possible.
	Clogged {
		/// Index of the node.
		node_index: NodeIndex,
		/// Protocol which generated the message.
		protocol_id: ProtocolId,
		/// Copy of the messages that are within the buffer, for further diagnostic.
		messages: Vec<Bytes>,
	},
}

/// Network service. Must be polled regularly in order for the networking to work.
pub struct Service {
	/// Stream of events of the swarm.
	swarm: Swarm<Boxed<(PeerId, StreamMuxerBox), IoError>, Behaviour<Substream<StreamMuxerBox>>, NetTopology>,

	/// Bandwidth logging system. Can be queried to know the average bandwidth consumed.
	bandwidth: Arc<transport::BandwidthSinks>,

	/// Information about all the nodes we're connected to.
	nodes_info: FnvHashMap<NodeIndex, NodeInfo>,

	/// Opposite of `nodes_info`.
	index_by_id: FnvHashMap<PeerId, NodeIndex>,

	/// Next index to assign to a node.
	next_node_id: NodeIndex,

	/// Stream that fires when we need to cleanup and flush the topology, and cleanup the disabled
	/// peers.
	cleanup: Interval,

	/// Events to produce on the Stream.
	injected_events: Vec<ServiceEvent>,
}

/// Information about a node we're connected to.
#[derive(Debug)]
struct NodeInfo {
	/// Hash of the public key of the node.
	peer_id: PeerId,
	/// How we're connected to the node.
	endpoint: ConnectedPoint,
	/// Version reported by the remote, or `None` if unknown.
	client_version: Option<String>,
}

impl Service {
	/// Returns an iterator that produces the list of addresses we're listening on.
	#[inline]
	pub fn listeners(&self) -> impl Iterator<Item = &Multiaddr> {
		Swarm::listeners(&self.swarm)
	}

	/// Returns the downloaded bytes per second averaged over the past few seconds.
	#[inline]
	pub fn average_download_per_sec(&self) -> u64 {
		self.bandwidth.average_download_per_sec()
	}

	/// Returns the uploaded bytes per second averaged over the past few seconds.
	#[inline]
	pub fn average_upload_per_sec(&self) -> u64 {
		self.bandwidth.average_upload_per_sec()
	}

	/// Returns the peer id of the local node.
	#[inline]
	pub fn peer_id(&self) -> &PeerId {
		Swarm::local_peer_id(&self.swarm)
	}

	/// Returns the list of all the peers we are connected to.
	#[inline]
	pub fn connected_peers<'a>(&'a self) -> impl Iterator<Item = NodeIndex> + 'a {
		self.nodes_info.keys().cloned()
	}

	/// Try to add a reserved peer.
	pub fn add_reserved_peer(&mut self, peer_id: PeerId, addr: Multiaddr) {
		Swarm::topology_mut(&mut self.swarm).add_bootstrap_addr(&peer_id, addr);
		self.swarm.add_reserved_peer(peer_id);
	}

	/// Try to remove a reserved peer.
	///
	/// If we are in reserved mode and we were connected to a node with this peer ID, then this
	/// method will disconnect it.
	pub fn remove_reserved_peer(&mut self, peer_id: PeerId) {
		self.swarm.remove_reserved_peer(peer_id);
	}

	/// Start accepting all peers again if we weren't.
	#[inline]
	pub fn accept_unreserved_peers(&mut self) {
		self.swarm.accept_unreserved_peers();
	}

	/// Start refusing non-reserved nodes. Disconnects the nodes that we are connected to that
	/// aren't reserved.
	pub fn deny_unreserved_peers(&mut self) {
		self.swarm.deny_unreserved_peers();
	}

	/// Returns the `PeerId` of a node.
	#[inline]
	pub fn peer_id_of_node(&self, node_index: NodeIndex) -> Option<&PeerId> {
		self.nodes_info.get(&node_index).map(|info| &info.peer_id)
	}

	/// Returns the way we are connected to a node.
	#[inline]
	pub fn node_endpoint(&self, node_index: NodeIndex) -> Option<&ConnectedPoint> {
		self.nodes_info.get(&node_index).map(|info| &info.endpoint)
	}

	/// Returns the client version reported by a node.
	pub fn node_client_version(&self, node_index: NodeIndex) -> Option<&str> {
		self.nodes_info.get(&node_index)
			.and_then(|info| info.client_version.as_ref().map(|s| &s[..]))
	}

	/// Sends a message to a peer using the custom protocol.
	///
	/// Has no effect if the connection to the node has been closed, or if the node index is
	/// invalid.
	pub fn send_custom_message(
		&mut self,
		node_index: NodeIndex,
		protocol: ProtocolId,
		data: Vec<u8>
	) {
		if let Some(peer_id) = self.nodes_info.get(&node_index).map(|info| &info.peer_id) {
			self.swarm.send_custom_message(peer_id, protocol, data);
		} else {
			warn!(target: "sub-libp2p", "Tried to send message to unknown node: {:}", node_index);
		}
	}

	/// Disconnects a peer and bans it for a little while.
	///
	/// Same as `drop_node`, except that the same peer will not be able to reconnect later.
	#[inline]
	pub fn ban_node(&mut self, node_index: NodeIndex) {
		if let Some(info) = self.nodes_info.get(&node_index) {
			info!(target: "sub-libp2p", "Banned {:?} (#{:?}, {:?}, {:?})", info.peer_id,
				node_index, info.endpoint, info.client_version);
			self.swarm.ban_node(info.peer_id.clone());
		}
	}

	/// Disconnects a peer.
	///
	/// This is asynchronous and will not immediately close the peer.
	/// Corresponding closing events will be generated once the closing actually happens.
	#[inline]
	pub fn drop_node(&mut self, node_index: NodeIndex) {
		if let Some(info) = self.nodes_info.get(&node_index) {
			debug!(target: "sub-libp2p", "Dropping {:?} on purpose (#{:?}, {:?}, {:?})",
				info.peer_id, node_index, info.endpoint, info.client_version);
			self.swarm.drop_node(&info.peer_id);
		}
	}

	/// Returns the `NodeIndex` of a peer, or assigns one if none exists.
	fn index_of_peer_or_assign(&mut self, peer: PeerId, endpoint: ConnectedPoint) -> NodeIndex {
		match self.index_by_id.entry(peer) {
			Entry::Occupied(entry) => {
				let id = *entry.get();
				self.nodes_info.insert(id, NodeInfo {
					peer_id: entry.key().clone(),
					endpoint,
					client_version: None,
				});
				id
			},
			Entry::Vacant(entry) => {
				let id = self.next_node_id;
				self.next_node_id += 1;
				self.nodes_info.insert(id, NodeInfo {
					peer_id: entry.key().clone(),
					endpoint,
					client_version: None,
				});
				entry.insert(id);
				id
			},
		}
	}

	/// Polls for what happened on the network.
	fn poll_swarm(&mut self) -> Poll<Option<ServiceEvent>, IoError> {
		loop {
			match self.swarm.poll() {
				Ok(Async::Ready(Some(BehaviourOut::CustomProtocolOpen { protocol_id, peer_id, version, endpoint }))) => {
					debug!(target: "sub-libp2p", "Opened custom protocol with {:?}", peer_id);
					let node_index = self.index_of_peer_or_assign(peer_id, endpoint);
					break Ok(Async::Ready(Some(ServiceEvent::OpenedCustomProtocol {
						node_index,
						protocol: protocol_id,
						version,
					})))
				}
				Ok(Async::Ready(Some(BehaviourOut::CustomProtocolClosed { protocol_id, peer_id, result }))) => {
					debug!(target: "sub-libp2p", "Custom protocol with {:?} closed: {:?}", peer_id, result);
					let node_index = *self.index_by_id.get(&peer_id).expect("index_by_id is always kept in sync with the state of the behaviour");
					break Ok(Async::Ready(Some(ServiceEvent::ClosedCustomProtocol {
						node_index,
						protocol: protocol_id,
					})))
				}
				Ok(Async::Ready(Some(BehaviourOut::CustomMessage { protocol_id, peer_id, data }))) => {
					let node_index = *self.index_by_id.get(&peer_id).expect("index_by_id is always kept in sync with the state of the behaviour");
					break Ok(Async::Ready(Some(ServiceEvent::CustomMessage {
						node_index,
						protocol_id,
						data,
					})))
				}
				Ok(Async::Ready(Some(BehaviourOut::Clogged { protocol_id, peer_id, messages }))) => {
					let node_index = *self.index_by_id.get(&peer_id).expect("index_by_id is always kept in sync with the state of the behaviour");
					break Ok(Async::Ready(Some(ServiceEvent::Clogged {
						node_index,
						protocol_id,
						messages,
					})))
				}
				Ok(Async::Ready(Some(BehaviourOut::Identified { peer_id, info }))) => {
					// Contrary to the other events, this one can happen even on nodes which don't
					// have any open custom protocol slot. Therefore it is not necessarily in the
					// list.
					if let Some(id) = self.index_by_id.get(&peer_id) {
						self.nodes_info.get_mut(id)
							.expect("index_by_id and nodes_info are always kept in sync; QED")
							.client_version = Some(info.agent_version);
					}
				}
				Ok(Async::NotReady) => break Ok(Async::NotReady),
				Ok(Async::Ready(None)) => unreachable!("The Swarm stream never ends"),
				Err(_) => unreachable!("The Swarm never errors"),
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
					Swarm::topology_mut(&mut self.swarm).cleanup();
					if let Err(err) = Swarm::topology_mut(&mut self.swarm).flush_to_disk() {
						warn!(target: "sub-libp2p", "Failed to flush topology: {:?}", err);
					}
					debug!(target: "sub-libp2p", "Topology now contains {} nodes",
						Swarm::topology_mut(&mut self.swarm).num_peers());
				},
				Ok(Async::Ready(None)) => {
					warn!(target: "sub-libp2p", "Topology flush stream ended unexpectedly");
					return Ok(Async::Ready(None))
				}
				Err(err) => {
					warn!(target: "sub-libp2p", "Topology flush stream errored: {:?}", err);
					return Err(IoError::new(IoErrorKind::Other, err))
				}
			}
		}
	}
}

impl Drop for Service {
	fn drop(&mut self) {
		if let Err(err) = Swarm::topology_mut(&mut self.swarm).flush_to_disk() {
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

		match self.poll_cleanup()? {
			Async::Ready(value) => return Ok(Async::Ready(value)),
			Async::NotReady => (),
		}

		// The only way we reach this is if we went through all the `NotReady` paths above,
		// ensuring the current task is registered everywhere.
		Ok(Async::NotReady)
	}
}
