// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
	behaviour::Behaviour, behaviour::BehaviourOut,
	transport, NetworkState, NetworkStatePeer, NetworkStateNotConnectedPeer
};
use crate::custom_proto::{CustomMessage, RegisteredProtocol};
use crate::{NetworkConfiguration, NodeIndex, parse_str_addr};
use fnv::FnvHashMap;
use futures::{prelude::*, Stream};
use libp2p::{multiaddr::Protocol, Multiaddr, PeerId};
use libp2p::core::{Swarm, nodes::Substream, transport::boxed::Boxed, muxing::StreamMuxerBox};
use libp2p::core::nodes::ConnectedPoint;
use log::{debug, error, info, warn};
use std::collections::hash_map::Entry;
use std::fs;
use std::io::{Error as IoError, ErrorKind as IoErrorKind};
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio_timer::Interval;

/// Starts the substrate libp2p service.
///
/// Returns a stream that must be polled regularly in order for the networking to function.
pub fn start_service<TMessage>(
	config: NetworkConfiguration,
	registered_custom: RegisteredProtocol<TMessage>,
) -> Result<Service<TMessage>, IoError>
where TMessage: CustomMessage + Send + 'static {

	if let Some(ref path) = config.net_config_path {
		fs::create_dir_all(Path::new(path))?;
	}

	// Private and public keys configuration.
	let local_identity = config.node_key.clone().into_keypair()?;
	let local_public = local_identity.public();
	let local_peer_id = local_public.clone().into_peer_id();

	// Build the swarm.
	let (mut swarm, bandwidth) = {
		let behaviour = Behaviour::new(&config, local_public, registered_custom);
		let (transport, bandwidth) = transport::build_transport(local_identity);
		(Swarm::new(transport, behaviour, local_peer_id.clone()), bandwidth)
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

	// Add external addresses.
	for addr in &config.public_addresses {
		Swarm::add_external_address(&mut swarm, addr.clone());
	}

	// Connect to the bootnodes.
	for bootnode in config.boot_nodes.iter() {
		match parse_str_addr(bootnode) {
			Ok((peer_id, _)) => Swarm::dial(&mut swarm, peer_id),
			Err(_) => warn!(target: "sub-libp2p", "Not a valid bootnode address: {}", bootnode),
		}
	}

	// Initialize the reserved peers.
	for reserved in config.reserved_nodes.iter() {
		if let Ok((peer_id, addr)) = parse_str_addr(reserved) {
			swarm.add_reserved_peer(peer_id.clone(), addr);
			Swarm::dial(&mut swarm, peer_id);
		} else {
			warn!(target: "sub-libp2p", "Not a valid reserved node address: {}", reserved);
		}
	}

	debug!(target: "sub-libp2p", "Topology started with {} entries",
		swarm.num_topology_peers());

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
pub enum ServiceEvent<TMessage> {
	/// A custom protocol substream has been opened with a node.
	OpenedCustomProtocol {
		/// The Id of the node.
		peer_id: PeerId,
		/// Index of the node.
		node_index: NodeIndex,
		/// Version of the protocol that was opened.
		version: u8,
		/// Node debug info
		debug_info: String,
	},

	/// A custom protocol substream has been closed.
	ClosedCustomProtocol {
		/// Index of the node.
		node_index: NodeIndex,
		/// Node debug info
		debug_info: String,
	},

	/// Receives a message on a custom protocol stream.
	CustomMessage {
		/// Index of the node.
		node_index: NodeIndex,
		/// Message that has been received.
		message: TMessage,
	},

	/// The substream with a node is clogged. We should avoid sending data to it if possible.
	Clogged {
		/// Index of the node.
		node_index: NodeIndex,
		/// Copy of the messages that are within the buffer, for further diagnostic.
		messages: Vec<TMessage>,
	},
}

/// Network service. Must be polled regularly in order for the networking to work.
pub struct Service<TMessage> where TMessage: CustomMessage {
	/// Stream of events of the swarm.
	swarm: Swarm<Boxed<(PeerId, StreamMuxerBox), IoError>, Behaviour<TMessage, Substream<StreamMuxerBox>>>,

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
	injected_events: Vec<ServiceEvent<TMessage>>,
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
	/// Latest ping time with this node.
	latest_ping: Option<Duration>,
}

impl<TMessage> Service<TMessage>
where TMessage: CustomMessage + Send + 'static {
	/// Returns a struct containing tons of useful information about the network.
	pub fn state(&mut self) -> NetworkState {
		let now = Instant::now();

		let connected_peers = {
			let swarm = &mut self.swarm;
			self.nodes_info.values().map(move |info| {
				let known_addresses = swarm.known_addresses(&info.peer_id)
					.map(|(a, s)| (a.clone(), s)).collect();

				(info.peer_id.to_base58(), NetworkStatePeer {
					endpoint: info.endpoint.clone().into(),
					version_string: info.client_version.clone(),
					latest_ping_time: info.latest_ping,
					enabled: swarm.is_enabled(&info.peer_id),
					open: swarm.is_open(&info.peer_id),
					known_addresses,
				})
			}).collect()
		};

		let not_connected_peers = {
			let swarm = &mut self.swarm;
			let index_by_id = &self.index_by_id;
			let list = swarm.known_peers().filter(|p| !index_by_id.contains_key(p))
				.cloned().collect::<Vec<_>>();
			list.into_iter().map(move |peer_id| {
				let known_addresses = swarm.known_addresses(&peer_id)
					.map(|(a, s)| (a.clone(), s)).collect();
				(peer_id.to_base58(), NetworkStateNotConnectedPeer {
					known_addresses,
				})
			}).collect()
		};

		NetworkState {
			peer_id: Swarm::local_peer_id(&self.swarm).to_base58(),
			listened_addresses: Swarm::listeners(&self.swarm).cloned().collect(),
			reserved_peers: self.swarm.reserved_peers().map(|p| p.to_base58()).collect(),
			banned_peers: self.swarm.banned_nodes().map(|(p, until)| {
				let dur = if until > now { until - now } else { Duration::new(0, 0) };
				(p.to_base58(), dur.as_secs())
			}).collect(),
			is_reserved_only: self.swarm.is_reserved_only(),
			average_download_per_sec: self.bandwidth.average_download_per_sec(),
			average_upload_per_sec: self.bandwidth.average_upload_per_sec(),
			connected_peers,
			not_connected_peers,
		}
	}

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
		self.swarm.add_reserved_peer(peer_id, addr);
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
		message: TMessage
	) {
		if let Some(peer_id) = self.nodes_info.get(&node_index).map(|info| &info.peer_id) {
			self.swarm.send_custom_message(peer_id, message);
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

	/// Get debug info for a given peer.
	pub fn peer_debug_info(&self, who: NodeIndex) -> String {
		if let Some(info) = self.nodes_info.get(&who) {
			format!("{:?} (version: {:?}) through {:?}", info.peer_id, info.client_version, info.endpoint)
		} else {
			"unknown".to_string()
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
					latest_ping: None,
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
					latest_ping: None,
				});
				entry.insert(id);
				id
			},
		}
	}

	/// Polls for what happened on the network.
	fn poll_swarm(&mut self) -> Poll<Option<ServiceEvent<TMessage>>, IoError> {
		loop {
			match self.swarm.poll() {
				Ok(Async::Ready(Some(BehaviourOut::CustomProtocolOpen { peer_id, version, endpoint }))) => {
					debug!(target: "sub-libp2p", "Opened custom protocol with {:?}", peer_id);
					let node_index = self.index_of_peer_or_assign(peer_id.clone(), endpoint);
					break Ok(Async::Ready(Some(ServiceEvent::OpenedCustomProtocol {
						peer_id,
						node_index,
						version,
						debug_info: self.peer_debug_info(node_index),
					})))
				}
				Ok(Async::Ready(Some(BehaviourOut::CustomProtocolClosed { peer_id, result }))) => {
					debug!(target: "sub-libp2p", "Custom protocol with {:?} closed: {:?}", peer_id, result);
					let node_index = *self.index_by_id.get(&peer_id).expect("index_by_id is always kept in sync with the state of the behaviour");
					break Ok(Async::Ready(Some(ServiceEvent::ClosedCustomProtocol {
						node_index,
						debug_info: self.peer_debug_info(node_index),
					})))
				}
				Ok(Async::Ready(Some(BehaviourOut::CustomMessage { peer_id, message }))) => {
					let node_index = *self.index_by_id.get(&peer_id).expect("index_by_id is always kept in sync with the state of the behaviour");
					break Ok(Async::Ready(Some(ServiceEvent::CustomMessage {
						node_index,
						message,
					})))
				}
				Ok(Async::Ready(Some(BehaviourOut::Clogged { peer_id, messages }))) => {
					let node_index = *self.index_by_id.get(&peer_id).expect("index_by_id is always kept in sync with the state of the behaviour");
					break Ok(Async::Ready(Some(ServiceEvent::Clogged {
						node_index,
						messages,
					})))
				}
				Ok(Async::Ready(Some(BehaviourOut::Identified { peer_id, info }))) => {
					// Contrary to the other events, this one can happen even on nodes which don't
					// have any open custom protocol slot. Therefore it is not necessarily in the
					// list.
					if let Some(id) = self.index_by_id.get(&peer_id) {
						if let Some(n) = self.nodes_info.get_mut(id) {
							n.client_version = Some(info.agent_version);
						} else {
							error!(target: "sub-libp2p",
								"State inconsistency between index_by_id and nodes_info");
						}
					}
				}
				Ok(Async::Ready(Some(BehaviourOut::PingSuccess { peer_id, ping_time }))) => {
					// Contrary to the other events, this one can happen even on nodes which don't
					// have any open custom protocol slot. Therefore it is not necessarily in the
					// list.
					if let Some(id) = self.index_by_id.get(&peer_id) {
						if let Some(n) = self.nodes_info.get_mut(id) {
							n.latest_ping = Some(ping_time);
						} else {
							error!(target: "sub-libp2p",
								"State inconsistency between index_by_id and nodes_info");
						}
					}
				}
				Ok(Async::NotReady) => break Ok(Async::NotReady),
				Ok(Async::Ready(None)) => unreachable!("The Swarm stream never ends"),
				Err(_) => unreachable!("The Swarm never errors"),
			}
		}
	}

	/// Polls the stream that fires when we need to cleanup and flush the topology.
	fn poll_cleanup(&mut self) -> Poll<Option<ServiceEvent<TMessage>>, IoError> {
		loop {
			match self.cleanup.poll() {
				Ok(Async::NotReady) => return Ok(Async::NotReady),
				Ok(Async::Ready(Some(_))) => {
					debug!(target: "sub-libp2p", "Cleaning and flushing topology");
					self.swarm.cleanup();
					if let Err(err) = self.swarm.flush_topology() {
						warn!(target: "sub-libp2p", "Failed to flush topology: {:?}", err);
					}
					debug!(target: "sub-libp2p", "Topology now contains {} nodes",
						self.swarm.num_topology_peers());
				}
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

impl<TMessage> Drop for Service<TMessage> where TMessage: CustomMessage {
	fn drop(&mut self) {
		if let Err(err) = self.swarm.flush_topology() {
			warn!(target: "sub-libp2p", "Failed to flush topology: {:?}", err);
		}
	}
}

impl<TMessage> Stream for Service<TMessage> where TMessage: CustomMessage + Send + 'static {
	type Item = ServiceEvent<TMessage>;
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
