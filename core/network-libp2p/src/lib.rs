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

//! Networking layer of Substrate.

mod behaviour;
mod custom_proto;
mod error;
mod secret;
mod service_task;
mod traits;
mod transport;

pub use crate::custom_proto::{CustomMessage, CustomMessageId, RegisteredProtocol};
pub use crate::error::{Error, ErrorKind, DisconnectReason};
pub use crate::secret::obtain_private_key;
pub use crate::service_task::{start_service, Service, ServiceEvent};
pub use crate::traits::{NetworkConfiguration, NodeIndex, NodeId, NonReservedPeerMode};
pub use crate::traits::{ProtocolId, Secret, Severity};
pub use libp2p::{Multiaddr, multiaddr::Protocol, build_multiaddr, PeerId, core::PublicKey};

use libp2p::core::nodes::ConnectedPoint;
use serde_derive::Serialize;
use std::{collections::{HashMap, HashSet}, time::Duration};

/// Parses a string address and returns the component, if valid.
pub fn parse_str_addr(addr_str: &str) -> Result<(PeerId, Multiaddr), Error> {
	let mut addr: Multiaddr = addr_str.parse().map_err(|_| ErrorKind::AddressParse)?;
	let who = match addr.pop() {
		Some(Protocol::P2p(key)) =>
			PeerId::from_multihash(key).map_err(|_| ErrorKind::AddressParse)?,
		_ => return Err(ErrorKind::AddressParse.into()),
	};
	Ok((who, addr))
}

/// Returns general information about the networking.
///
/// Meant for general diagnostic purposes.
///
/// **Warning**: This API is not stable.
#[derive(Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct NetworkState {
	/// PeerId of the local node.
	pub peer_id: String,
	/// List of addresses the node is currently listening on.
	pub listened_addresses: HashSet<Multiaddr>,
	// TODO (https://github.com/libp2p/rust-libp2p/issues/978): external_addresses: Vec<Multiaddr>,
	/// If true, we only accept reserved peers.
	pub is_reserved_only: bool,
	/// PeerIds of the nodes that are marked as reserved.
	pub reserved_peers: HashSet<String>,
	/// PeerIds of the nodes that are banned, and how long in the seconds the ban remains.
	pub banned_peers: HashMap<String, u64>,
	/// List of node we're connected to.
	pub connected_peers: HashMap<String, NetworkStatePeer>,
	/// List of node that we know of but that we're not connected to.
	pub not_connected_peers: HashMap<String, NetworkStateNotConnectedPeer>,
	/// Downloaded bytes per second averaged over the past few seconds.
	pub average_download_per_sec: u64,
	/// Uploaded bytes per second averaged over the past few seconds.
	pub average_upload_per_sec: u64,
}

#[derive(Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct NetworkStatePeer {
	/// How we are connected to the node.
	pub endpoint: NetworkStatePeerEndpoint,
	/// Node information, as provided by the node itself. Can be empty if not known yet.
	pub version_string: Option<String>,
	/// Latest ping duration with this node.
	pub latest_ping_time: Option<Duration>,
	/// If true, the peer is "enabled", which means that we try to open Substrate-related protocols
	/// with this peer. If false, we stick to Kademlia and/or other network-only protocols.
	pub enabled: bool,
	/// List of protocols that we have open with the given peer.
	pub open_protocols: HashSet<ProtocolId>,
	/// List of addresses known for this node, with its reputation score.
	pub known_addresses: HashMap<Multiaddr, u32>,
}

#[derive(Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct NetworkStateNotConnectedPeer {
	/// List of addresses known for this node, with its reputation score.
	pub known_addresses: HashMap<Multiaddr, u32>,
}

#[derive(Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum NetworkStatePeerEndpoint {
	/// We are dialing the given address.
	Dialing(Multiaddr),
	/// We are listening.
	Listening {
		/// Address we're listening on that received the connection.
		listen_addr: Multiaddr,
		/// Address data is sent back to.
		send_back_addr: Multiaddr,
	},
}

impl From<ConnectedPoint> for NetworkStatePeerEndpoint {
	fn from(endpoint: ConnectedPoint) -> Self {
		match endpoint {
			ConnectedPoint::Dialer { ref address } =>
				NetworkStatePeerEndpoint::Dialing(address.clone()),
			ConnectedPoint::Listener { ref listen_addr, ref send_back_addr } =>
				NetworkStatePeerEndpoint::Listening {
					listen_addr: listen_addr.clone(),
					send_back_addr: send_back_addr.clone()
				}
		}
	}
}
