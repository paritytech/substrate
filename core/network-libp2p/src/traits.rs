// Copyright 2015-2018 Parity Technologies (UK) Ltd.
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

use std::{fmt, iter, net::Ipv4Addr, str};
use libp2p::{multiaddr::Protocol, Multiaddr, PeerId};

/// Protocol / handler id
pub type ProtocolId = [u8; 3];

/// Node public key
pub type NodeId = PeerId;

/// Local (temporary) peer session ID.
pub type NodeIndex = usize;

/// secio secret key;
pub type Secret = [u8; 32];

/// Network service configuration
#[derive(Debug, PartialEq, Clone)]
pub struct NetworkConfiguration {
	/// Directory path to store general network configuration. None means nothing will be saved
	pub config_path: Option<String>,
	/// Directory path to store network-specific configuration. None means nothing will be saved
	pub net_config_path: Option<String>,
	/// Multiaddresses to listen for incoming connections.
	pub listen_addresses: Vec<Multiaddr>,
	/// Multiaddresses to advertise. Detected automatically if empty.
	pub public_addresses: Vec<Multiaddr>,
	/// List of initial node addresses
	pub boot_nodes: Vec<String>,
	/// Use provided node key instead of default
	pub use_secret: Option<Secret>,
	/// Maximum allowed number of incoming connections
	pub in_peers: u32,
	/// Number of outgoing connections we're trying to maintain
	pub out_peers: u32,
	/// List of reserved node addresses.
	pub reserved_nodes: Vec<String>,
	/// The non-reserved peer mode.
	pub non_reserved_mode: NonReservedPeerMode,
	/// Client identifier. Sent over the wire for debugging purposes.
	pub client_version: String,
	/// Name of the node. Sent over the wire for debugging purposes.
	pub node_name: String,
}

impl Default for NetworkConfiguration {
	fn default() -> Self {
		NetworkConfiguration::new()
	}
}

impl NetworkConfiguration {
	/// Create a new instance of default settings.
	pub fn new() -> Self {
		NetworkConfiguration {
			config_path: None,
			net_config_path: None,
			listen_addresses: vec![
				iter::once(Protocol::Ip4(Ipv4Addr::new(0, 0, 0, 0)))
					.chain(iter::once(Protocol::Tcp(30333)))
					.collect()
			],
			public_addresses: Vec::new(),
			boot_nodes: Vec::new(),
			use_secret: None,
			in_peers: 25,
			out_peers: 75,
			reserved_nodes: Vec::new(),
			non_reserved_mode: NonReservedPeerMode::Accept,
			client_version: "unknown".into(),
			node_name: "unknown".into(),
		}
	}

	/// Create new default configuration for localhost-only connection with random port (useful for testing)
	pub fn new_local() -> NetworkConfiguration {
		let mut config = NetworkConfiguration::new();
		config.listen_addresses = vec![
			iter::once(Protocol::Ip4(Ipv4Addr::new(127, 0, 0, 1)))
				.chain(iter::once(Protocol::Tcp(0)))
				.collect()
		];
		config
	}
}

/// The severity of misbehaviour of a peer that is reported.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Severity<'a> {
	/// Peer is timing out. Could be bad connectivity of overload of work on either of our sides.
	Timeout,
	/// Peer has been notably useless. E.g. unable to answer a request that we might reasonably consider
	/// it could answer.
	Useless(&'a str),
	/// Peer has behaved in an invalid manner. This doesn't necessarily need to be Byzantine, but peer
	/// must have taken concrete action in order to behave in such a way which is wantanly invalid.
	Bad(&'a str),
}

impl<'a> fmt::Display for Severity<'a> {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Severity::Timeout => write!(fmt, "Timeout"),
			Severity::Useless(r) => write!(fmt, "Useless ({})", r),
			Severity::Bad(r) => write!(fmt, "Bad ({})", r),
		}
	}
}

/// Non-reserved peer modes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NonReservedPeerMode {
	/// Accept them. This is the default.
	Accept,
	/// Deny them.
	Deny,
}

impl NonReservedPeerMode {
	/// Attempt to parse the peer mode from a string.
	pub fn parse(s: &str) -> Option<Self> {
		match s {
			"accept" => Some(NonReservedPeerMode::Accept),
			"deny" => Some(NonReservedPeerMode::Deny),
			_ => None,
		}
	}
}
