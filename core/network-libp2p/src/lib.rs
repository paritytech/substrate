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

//! Networking layer of Substrate.
//!
//! # Overview
//!
//! This crate handles the following network mechanisms:
//!
//! - Discovering nodes that are part of the network.
//! - Connecting to said nodes and accepting incoming connections.
//! - Encrypting communications between nodes.
//! - Ensure that nodes are really the `PeerId` that they pretend to be.
//! - Ensuring that the nodes belong to the same chain as us before reporting a new connection.
//!
//! From the point of view of our node, each other node on the network has a reputation value in
//! the form of an `i32`. We try to establish connections towards nodes with a higher reputation
//! over nodes with a lower reputation.
//!
//! Establishing connections to other nodes is automatically performed by this crate, and there is
//! no way to influence this, except by adjusting reputations.
//!
//! ## About the term "connecting"
//!
//! The documentation of this crate uses the words "connected" and "disconnected". It is important
//! to note that this doesn't correspond to actual TCP/IP connections and disconnections. Libp2p
//! will maintain connections that aren't reported by the API of this crate, and TCP/IP connections
//! can be kept alive even after we have reported a disconnect in order to potentially reuse them.
//!
//! # Usage
//!
//! > **Important**: This crate is unstable and the API and usage may change.
//!
//! The first step is to crate a [`RegisteredProtocol`] describing the protocol, and a
//! [`NetworkConfiguration`] describing the network. Then call [`start_service`] with them, which
//! returns a [`Service`] object and a [`substrate_peerset::PeersetHandle`].
//!
//! The former allows you to know what happens on the network and to send messages, while the
//! latter can be used to adjust the reputations of nodes.
//!
//! You must call the `poll` method of [`Service`] in order to make the network progress and in
//! order to update the internal state of the [`Service`]. Calling `poll` will produce
//! [`ServiceEvent`]s, which inform you of what happened on the network.
//!
//! Please keep in mind that the state of the [`Service`] only updates itself in a way
//! corresponding to the [`ServiceEvent`] that `poll` returns.
//! 
//! Illustration:
//! 
//! - You call [`Service::connected_peers`] to get the list of nodes we are connected to.
//! - If you then call [`Service::connected_peers`] again, the returned list will always be the
//!   same, no matter what happened on the wire.
//! - If you then call [`Service::poll`] and a [`ServiceEvent::OpenedCustomProtocol`] event is
//!   returned, then the concerned node, and only the concerned node, will be added to the list of
//!   nodes we are connected to.
//! - Similarly, if [`Service::poll`] produces a [`ServiceEvent::ClosedCustomProtocol`] event, then
//!   only the concerned node will disappear from the list.
//! - And if [`Service::poll`] returns neither [`ServiceEvent::OpenedCustomProtocol`] nor
//!   [`ServiceEvent::ClosedCustomProtocol`], then the list of connected nodes doesn't change.
//!
//! ## Example
//!
//! ```no_run
//! # use futures::prelude::*;
//! use substrate_network_libp2p::ServiceEvent;
//!
//! let proto = substrate_network_libp2p::RegisteredProtocol::new(&b"hello"[..], &[0]);
//! let config = substrate_network_libp2p::NetworkConfiguration::default();
//! let (mut service, _peerset) = substrate_network_libp2p::start_service(config, proto).unwrap();
//!
//! tokio::run(futures::future::poll_fn(move || {
//! 	loop {
//! 		match service.poll().unwrap() {
//! 			Async::NotReady => return Ok(Async::NotReady),
//! 			Async::Ready(Some(ServiceEvent::OpenedCustomProtocol { peer_id, .. })) => {
//! 				println!("now connected to {:?}", peer_id);
//! 				service.send_custom_message(&peer_id, b"hello world!".to_vec());
//! 			}
//! 			Async::Ready(Some(ServiceEvent::ClosedCustomProtocol { peer_id, .. })) =>
//! 				println!("now disconnected from {:?}", peer_id),
//! 			Async::Ready(Some(ServiceEvent::CustomMessage { peer_id, message })) =>
//! 				println!("received message from {:?}: {:?}", peer_id, message),
//! 			Async::Ready(None) => return Ok(Async::Ready(())),
//! 			_ => {}
//! 		}
//! 	}
//! }));
//! ```
//!

mod behaviour;
mod config;
mod custom_proto;
mod service_task;
mod transport;

pub use crate::config::*;
pub use crate::custom_proto::{CustomMessage, RegisteredProtocol};
pub use crate::config::{NetworkConfiguration, NodeKeyConfig, Secret, NonReservedPeerMode};
pub use crate::service_task::{start_service, Service, ServiceEvent};
pub use libp2p::{Multiaddr, multiaddr, build_multiaddr};
pub use libp2p::{identity, PeerId, core::PublicKey};

use libp2p::core::nodes::ConnectedPoint;
use serde::{Deserialize, Serialize};
use slog_derive::SerdeValue;
use std::{collections::{HashMap, HashSet}, error, fmt, time::Duration};

/// Name of a protocol, transmitted on the wire. Should be unique for each chain.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProtocolId(smallvec::SmallVec<[u8; 6]>);

impl<'a> From<&'a [u8]> for ProtocolId {
	fn from(bytes: &'a [u8]) -> ProtocolId {
		ProtocolId(bytes.into())
	}
}

impl ProtocolId {
	/// Exposes the `ProtocolId` as bytes.
	pub fn as_bytes(&self) -> &[u8] {
		self.0.as_ref()
	}
}

/// Parses a string address and returns the component, if valid.
pub fn parse_str_addr(addr_str: &str) -> Result<(PeerId, Multiaddr), ParseErr> {
	let mut addr: Multiaddr = addr_str.parse()?;

	let who = match addr.pop() {
		Some(multiaddr::Protocol::P2p(key)) => PeerId::from_multihash(key)
			.map_err(|_| ParseErr::InvalidPeerId)?,
		_ => return Err(ParseErr::PeerIdMissing),
	};

	Ok((who, addr))
}

/// Error that can be generated by `parse_str_addr`.
#[derive(Debug)]
pub enum ParseErr {
	/// Error while parsing the multiaddress.
	MultiaddrParse(multiaddr::Error),
	/// Multihash of the peer ID is invalid.
	InvalidPeerId,
	/// The peer ID is missing from the address.
	PeerIdMissing,
}

impl fmt::Display for ParseErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseErr::MultiaddrParse(err) => write!(f, "{}", err),
            ParseErr::InvalidPeerId => write!(f, "Peer id at the end of the address is invalid"),
            ParseErr::PeerIdMissing => write!(f, "Peer id is missing from the address"),
        }
    }
}

impl error::Error for ParseErr {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            ParseErr::MultiaddrParse(err) => Some(err),
            ParseErr::InvalidPeerId => None,
            ParseErr::PeerIdMissing => None,
        }
    }
}

impl From<multiaddr::Error> for ParseErr {
	fn from(err: multiaddr::Error) -> ParseErr {
		ParseErr::MultiaddrParse(err)
	}
}

/// Returns general information about the networking.
///
/// Meant for general diagnostic purposes.
///
/// **Warning**: This API is not stable.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, SerdeValue)]
#[serde(rename_all = "camelCase")]
pub struct NetworkState {
	/// PeerId of the local node.
	pub peer_id: String,
	/// List of addresses the node is currently listening on.
	pub listened_addresses: HashSet<Multiaddr>,
	/// List of addresses the node knows it can be reached as.
	pub external_addresses: HashSet<Multiaddr>,
	/// List of node we're connected to.
	pub connected_peers: HashMap<String, NetworkStatePeer>,
	/// List of node that we know of but that we're not connected to.
	pub not_connected_peers: HashMap<String, NetworkStateNotConnectedPeer>,
	/// Downloaded bytes per second averaged over the past few seconds.
	pub average_download_per_sec: u64,
	/// Uploaded bytes per second averaged over the past few seconds.
	pub average_upload_per_sec: u64,
	/// State of the peerset manager.
	pub peerset: serde_json::Value,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
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
	/// If true, the peer is "open", which means that we have a Substrate-related protocol
	/// with this peer.
	pub open: bool,
	/// List of addresses known for this node.
	pub known_addresses: HashSet<Multiaddr>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NetworkStateNotConnectedPeer {
	/// List of addresses known for this node.
	pub known_addresses: HashSet<Multiaddr>,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
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
			ConnectedPoint::Dialer { address } =>
				NetworkStatePeerEndpoint::Dialing(address),
			ConnectedPoint::Listener { listen_addr, send_back_addr } =>
				NetworkStatePeerEndpoint::Listening {
					listen_addr: listen_addr,
					send_back_addr: send_back_addr
				}
		}
	}
}
