// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

#![warn(unused_extern_crates)]
#![warn(missing_docs)]

//! Substrate-specific P2P networking.
//!
//! **Important**: This crate is unstable and the API and usage may change.
//!
//! # Node identities and addresses
//!
//! In a decentralized network, each node possesses a network private key and a network public key.
//! In Substrate, the keys are based on the ed25519 curve. As of the writing of this documentation,
//! the secp256k1 curve can also be used, but is deprecated. Our local node's keypair must be
//! passed as part of the network configuration.
//!
//! From a node's public key, we can derive its *identity*. In Substrate and libp2p, a node's
//! identity is represented with the [`PeerId`] struct. All network communications between nodes on
//! the network use encryption derived from both sides's keys, which means that **identities cannot
//! be faked**.
//!
//! A node's identity uniquely identifies a machine on the network. If you start two or more
//! clients using the same network key, large interferences will happen.
//!
//! # Substrate's network protocol
//!
//! Substrate's networking protocol is based upon libp2p. It is at the moment not possible and not
//! planned to permit using something else than the libp2p network stack and the rust-libp2p
//! library. However the libp2p framework is very flexible and the rust-libp2p library could be
//! extended to support a wider range of protocols than what is offered by libp2p.
//!
//! ## Discovery mechanisms
//!
//! In order for our node to join a peer-to-peer network, it has to know a list of nodes that are
//! part of said network. This includes nodes identities and their address (how to reach them).
//! Building such a list is called the **discovery** mechanism. There are three mechanisms that
//! Substrate uses:
//!
//! - Bootstrap nodes. These are hard-coded node identities and addresses passed alongside with
//! the network configuration.
//! - mDNS. We perform a UDP broadcast on the local network. Nodes that listen may respond with
//! their identity. More info [here](https://github.com/libp2p/specs/blob/master/discovery/mdns.md).
//! mDNS can be disabled in the network configuration.
//! - Kademlia random walk. Once connected, we perform random Kademlia `FIND_NODE` requests in
//! order for nodes to propagate to us their view of the network. More information about Kademlia
//! can be found [on Wikipedia](https://en.wikipedia.org/wiki/Kademlia).
//!
//! ## Connection establishment
//!
//! When node Alice knows node Bob's identity and address, it can establish a connection with Bob.
//! All connections must always use encryption and multiplexing. While some node addresses (eg.
//! addresses using `/quic`) already imply which encryption and/or multiplexing to use, for others
//! the **multistream-select** protocol is used in order to negotiate an encryption layer and/or a
//! multiplexing layer.
//!
//! The connection establishment mechanism is called the **transport**.
//!
//! As of the writing of this documentation, the following base-layer protocols are supported by
//! Substrate:
//!
//! - TCP/IP for addresses of the form `/ip4/1.2.3.4/tcp/5`. Once the TCP connection is open, an
//! encryption and a multiplexing layer are negotiated on top.
//! - WebSockets for addresses of the form `/ip4/1.2.3.4/tcp/5/ws`. A TCP/IP connection is open and
//! the WebSockets protocol is negotiated on top. Communications then happen inside WebSockets data
//! frames. Encryption and multiplexing are additionally negotiated again inside this channel.
//! - DNS for addresses of the form `/dns4/example.com/tcp/5` or `/dns4/example.com/tcp/5/ws`. A
//! node's address can contain a domain name.
//!
//! The following encryption protocols are supported:
//!
//! - [Secio](https://github.com/libp2p/specs/tree/master/secio). A TLS-1.2-like protocol but
//! without certificates. Support for secio will likely be deprecated in the far future.
//! - [Noise](https://noiseprotocol.org/). Support for noise is very experimental. The details are
//! very blurry and may change at any moment.
//!
//! The following multiplexing protocols are supported:
//!
//! - [Mplex](https://github.com/libp2p/specs/tree/master/mplex). Support for mplex will likely
//! be deprecated in the future.
//! - [Yamux](https://github.com/hashicorp/yamux/blob/master/spec.md).
//!
//! ## Substreams
//!
//! Once a connection has been established and uses multiplexing, substreams can be opened. When
//! a substream is open, the **multistream-select** protocol is used to negotiate which protocol to
//! use on that given substream. In practice, Substrate opens the following substreams:
//!
//! - We periodically open an ephemeral substream in order to ping the remote and check whether the
//! connection is still alive. Failure for the remote to reply leads to a disconnection. This uses
//! the libp2p ping protocol.
//! - We periodically open an ephemeral substream in order to ask information from the remote. This
//! is called [the `identify` protocol](https://github.com/libp2p/specs/tree/master/identify).
//! - We periodically open ephemeral substreams for Kademlia random walk queries. Each Kademlia
//! query is done in a new separate substream. This uses the
//! [standard libp2p Kademlia protocol](https://github.com/libp2p/specs/pull/108).
//! - We optionally keep a substream alive for all Substrate-based communications. The name of the
//! protocol negotiated is based on the *protocol ID* passed as part of the network configuration.
//! This protocol ID should be unique for each chain and prevents nodes from different chains from
//! connecting to each other. More information below.
//!
//! ## The Substrate substream
//!
//! Substrate uses a component named the **peerset manager (PSM)**. Through the discovery
//! mechanism, the PSM is aware of the nodes that are part of the network and decides which nodes
//! we should perform Substrate-based communications with. For these nodes, we open a connection
//! if necessary and open a unique substream for Substrate-based communications. If the PSM decides
//! that we should disconnect a node, then that substream is closed.
//!
//! For more information about the PSM, see the *substrate-peerset* crate.
//!
//! Note that at the moment there is no mechanism in place to solve the issues that arise where the
//! two sides of a connection open the unique substream simultaneously. In order to not run into
//! issues, only the dialer of a connection is allowed to open the unique substream. When the
//! substream is closed, the entire connection is closed as well. This is a bug, and should be
//! fixed by improving the protocol.
//!
//! Within the unique Substrate substream, messages encoded using
//! [*parity-scale-codec*](https://github.com/paritytech/parity-scale-codec) are exchanged.
//! The detail of theses messages is not totally in place, but they can be found in the
//! `message.rs` file.
//!
//! Once the substream is open, the first step is an exchange of a *status* message from both
//! sides, containing information such as the chain root hash, head of chain, and so on.
//!
//! Communications within this substream include:
//!
//! - Syncing. Blocks are announced and requested from other nodes.
//! - Light-client requests. When a light client requires information, a random node we have a
//! substream open with is chosen, and the information is requested from it.
//! - Gossiping. Used for example by grandpa.
//! - Network specialization. The network protocol can be specialized through a template parameter
//! of the network service. This specialization is free to send and receive messages with the
//! remote. This is meant to be used by the chain that is being built on top of Substrate
//! (eg. Polkadot).
//!
//! It is intended that in the future each of these components gets more isolated, so that they
//! are free to open and close their own substreams, and so that syncing and light client requests
//! are able to communicate with nodes outside of the range of the PSM.
//!
//! # Usage
//!
//! Using the `substrate-network` crate is done through the [`NetworkWorker`] struct. Create this
//! struct by passing a [`config::Params`], then poll it as if it was a `Future`. You can extract an
//! `Arc<NetworkService>` from the `NetworkWorker`, which can be shared amongst multiple places
//! in order to give orders to the networking.
//!
//! More precise usage details are still being worked on and will likely change in the future.
//!

mod behaviour;
mod chain;
mod custom_proto;
mod debug_info;
mod discovery;
mod on_demand_layer;
#[macro_use]
mod protocol;
mod protocol_behaviour;
mod service;
mod transport;

pub mod config;
pub mod error;

#[cfg(any(test, feature = "test-helpers"))]
pub mod test;

pub use chain::{Client as ClientHandle, FinalityProofProvider};
pub use service::{
	NetworkService, NetworkWorker, FetchFuture, TransactionPool, ManageNetwork,
	NetworkMsg, ExHashT, ReportHandle,
};
pub use config::{NodeKeyConfig, Secret, Secp256k1Secret, Ed25519Secret};
pub use protocol::{PeerInfo, Context, consensus_gossip, event, message, specialization};
pub use protocol::sync::SyncState;
pub use libp2p::{Multiaddr, multiaddr, build_multiaddr};
pub use libp2p::{identity, PeerId, core::PublicKey, wasm_ext::ExtTransport};

pub use message::{generic as generic_message, RequestId, Status as StatusMessage};
pub use event::Event;
pub use error::Error;
pub use protocol::on_demand::AlwaysBadChecker;
pub use on_demand_layer::{OnDemand, RemoteResponse};
#[doc(hidden)]
pub use runtime_primitives::traits::Block as BlockT;

use libp2p::core::nodes::ConnectedPoint;
use serde::{Deserialize, Serialize};
use slog_derive::SerdeValue;
use std::{collections::{HashMap, HashSet}, fmt, time::Duration};

/// Extension trait for `NetworkBehaviour` that also accepts discovering nodes.
pub trait DiscoveryNetBehaviour {
	/// Notify the protocol that we have learned about the existence of nodes.
	///
	/// Can (or most likely will) be called multiple times with the same `PeerId`s.
	///
	/// Also note that there is no notification for expired nodes. The implementer must add a TTL
	/// system, or remove nodes that will fail to reach.
	fn add_discovered_nodes(&mut self, nodes: impl Iterator<Item = PeerId>);
}

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

impl std::error::Error for ParseErr {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
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

/// Part of the `NetworkState` struct. Unstable.
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

/// Part of the `NetworkState` struct. Unstable.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NetworkStateNotConnectedPeer {
	/// List of addresses known for this node.
	pub known_addresses: HashSet<Multiaddr>,
	/// Node information, as provided by the node itself, if we were ever connected to this node.
	pub version_string: Option<String>,
	/// Latest ping duration with this node, if we were ever connected to this node.
	pub latest_ping_time: Option<Duration>,
}

/// Part of the `NetworkState` struct. Unstable.
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
					listen_addr,
					send_back_addr
				}
		}
	}
}
