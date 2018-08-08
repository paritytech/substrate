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

use std::fmt;
use std::cmp::Ordering;
use std::iter;
use std::net::Ipv4Addr;
use std::str;
use std::time::Duration;
use io::TimerToken;
use libp2p::{multiaddr::AddrComponent, Multiaddr};
use error::Error;
use ethkey::Secret;
use ethereum_types::H512;

/// Protocol handler level packet id
pub type PacketId = u8;
/// Protocol / handler id
pub type ProtocolId = [u8; 3];

/// Node public key
pub type NodeId = H512;

/// Local (temporary) peer session ID.
pub type NodeIndex = usize;

/// Shared session information
#[derive(Debug, Clone)]
pub struct SessionInfo {
	/// Peer public key
	pub id: Option<NodeId>,
	/// Peer client ID
	pub client_version: String,
	/// Peer RLPx protocol version
	pub protocol_version: u32,
	/// Session protocol capabilities
	pub capabilities: Vec<SessionCapabilityInfo>,
	/// Peer protocol capabilities
	pub peer_capabilities: Vec<PeerCapabilityInfo>,
	/// Peer ping delay
	pub ping: Option<Duration>,
	/// True if this session was originated by us.
	pub originated: bool,
	/// Remote endpoint address of the session
	pub remote_address: String,
	/// Local endpoint address of the session
	pub local_address: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeerCapabilityInfo {
	pub protocol: ProtocolId,
	pub version: u8,
}

impl ToString for PeerCapabilityInfo {
	fn to_string(&self) -> String {
		format!("{}/{}", str::from_utf8(&self.protocol[..]).unwrap_or("???"), self.version)
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SessionCapabilityInfo {
	pub protocol: [u8; 3],
	pub version: u8,
	pub packet_count: u8,
	pub id_offset: u8,
}

impl PartialOrd for SessionCapabilityInfo {
	fn partial_cmp(&self, other: &SessionCapabilityInfo) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Ord for SessionCapabilityInfo {
	fn cmp(&self, b: &SessionCapabilityInfo) -> Ordering {
		// By protocol id first
		if self.protocol != b.protocol {
			return self.protocol.cmp(&b.protocol);
		}
		// By version
		self.version.cmp(&b.version)
	}
}

/// Network service configuration
#[derive(Debug, PartialEq, Clone)]
pub struct NetworkConfiguration {
	/// Directory path to store general network configuration. None means nothing will be saved
	pub config_path: Option<String>,
	/// Directory path to store network-specific configuration. None means nothing will be saved
	pub net_config_path: Option<String>,
	/// IP address to listen for incoming connections. Listen to all connections by default
	pub listen_address: Multiaddr,
	/// IP address to advertise. Detected automatically if none.
	pub public_address: Option<Multiaddr>,
	/// List of initial node addresses
	pub boot_nodes: Vec<String>,
	/// Use provided node key instead of default
	pub use_secret: Option<Secret>,
	/// Minimum number of connected peers to maintain
	pub min_peers: u32,
	/// Maximum allowed number of peers
	pub max_peers: u32,
	/// List of reserved node addresses.
	pub reserved_nodes: Vec<String>,
	/// The non-reserved peer mode.
	pub non_reserved_mode: NonReservedPeerMode,
	/// Client identifier
	pub client_version: String,
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
			listen_address: iter::once(AddrComponent::IP4(Ipv4Addr::new(0, 0, 0, 0)))
				.chain(iter::once(AddrComponent::TCP(30333)))
				.collect(),
			public_address: None,
			boot_nodes: Vec::new(),
			use_secret: None,
			min_peers: 25,
			max_peers: 50,
			reserved_nodes: Vec::new(),
			non_reserved_mode: NonReservedPeerMode::Accept,
			client_version: "Parity-network".into(),
		}
	}

	/// Create new default configuration for localhost-only connection with random port (useful for testing)
	pub fn new_local() -> NetworkConfiguration {
		let mut config = NetworkConfiguration::new();
		config.listen_address = iter::once(AddrComponent::IP4(Ipv4Addr::new(127, 0, 0, 1)))
			.chain(iter::once(AddrComponent::TCP(0)))
			.collect();
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

/// IO access point. This is passed to all IO handlers and provides an interface to the IO subsystem.
pub trait NetworkContext {
	/// Send a packet over the network to another peer.
	fn send(&self, peer: NodeIndex, packet_id: PacketId, data: Vec<u8>);

	/// Send a packet over the network to another peer using specified protocol.
	fn send_protocol(&self, protocol: ProtocolId, peer: NodeIndex, packet_id: PacketId, data: Vec<u8>);

	/// Respond to a current network message. Panics if no there is no packet in the context. If the session is expired returns nothing.
	fn respond(&self, packet_id: PacketId, data: Vec<u8>);

	/// Report peer. Depending on the report, peer may be disconnected and possibly banned.
	fn report_peer(&self, peer: NodeIndex, reason: Severity);

	/// Check if the session is still active.
	fn is_expired(&self) -> bool;

	/// Register a new IO timer. 'IoHandler::timeout' will be called with the token.
	fn register_timer(&self, token: TimerToken, delay: Duration) -> Result<(), Error>;

	/// Returns peer identification string
	fn peer_client_version(&self, peer: NodeIndex) -> String;

	/// Returns information on p2p session
	fn session_info(&self, peer: NodeIndex) -> Option<SessionInfo>;

	/// Returns max version for a given protocol.
	fn protocol_version(&self, protocol: ProtocolId, peer: NodeIndex) -> Option<u8>;

	/// Returns this object's subprotocol name.
	fn subprotocol_name(&self) -> ProtocolId;
}

impl<'a, T> NetworkContext for &'a T where T: ?Sized + NetworkContext {
	fn send(&self, peer: NodeIndex, packet_id: PacketId, data: Vec<u8>) {
		(**self).send(peer, packet_id, data)
	}

	fn send_protocol(&self, protocol: ProtocolId, peer: NodeIndex, packet_id: PacketId, data: Vec<u8>) {
		(**self).send_protocol(protocol, peer, packet_id, data)
	}

	fn respond(&self, packet_id: PacketId, data: Vec<u8>) {
		(**self).respond(packet_id, data)
	}

	fn report_peer(&self, peer: NodeIndex, reason: Severity) {
		(**self).report_peer(peer, reason)
	}

	fn is_expired(&self) -> bool {
		(**self).is_expired()
	}

	fn register_timer(&self, token: TimerToken, delay: Duration) -> Result<(), Error> {
		(**self).register_timer(token, delay)
	}

	fn peer_client_version(&self, peer: NodeIndex) -> String {
		(**self).peer_client_version(peer)
	}

	fn session_info(&self, peer: NodeIndex) -> Option<SessionInfo> {
		(**self).session_info(peer)
	}

	fn protocol_version(&self, protocol: ProtocolId, peer: NodeIndex) -> Option<u8> {
		(**self).protocol_version(protocol, peer)
	}

	fn subprotocol_name(&self) -> ProtocolId {
		(**self).subprotocol_name()
	}
}

/// Network IO protocol handler. This needs to be implemented for each new subprotocol.
/// All the handler function are called from within IO event loop.
/// `Message` is the type for message data.
pub trait NetworkProtocolHandler: Sync + Send {
	/// Initialize the handler
	fn initialize(&self, _io: &NetworkContext) {}
	/// Called when new network packet received.
	fn read(&self, io: &NetworkContext, peer: &NodeIndex, packet_id: u8, data: &[u8]);
	/// Called when new peer is connected. Only called when peer supports the same protocol.
	fn connected(&self, io: &NetworkContext, peer: &NodeIndex);
	/// Called when a previously connected peer disconnects.
	fn disconnected(&self, io: &NetworkContext, peer: &NodeIndex);
	/// Timer function called after a timeout created with `NetworkContext::timeout`.
	fn timeout(&self, _io: &NetworkContext, _timer: TimerToken) {}
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
