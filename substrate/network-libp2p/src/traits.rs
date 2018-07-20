// Copyright 2015-2018 Parity Technologies (UK) Ltd.
// This file is part of Parity.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::net::{SocketAddr, SocketAddrV4, Ipv4Addr};
use std::str::{self, FromStr};
use std::sync::Arc;
use std::time::Duration;
use io::TimerToken;
use ipnetwork::{IpNetwork, IpNetworkError};
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
pub type PeerId = usize;

/// Messages used to communitate with the event loop from other threads.
#[derive(Clone)]
pub enum NetworkIoMessage {
	/// Register a new protocol handler.
	AddHandler {
		/// Handler shared instance.
		handler: Arc<NetworkProtocolHandler + Sync>,
		/// Protocol Id.
		protocol: ProtocolId,
		/// Supported protocol versions and number of packet IDs reserved by the protocol (packet count).
		versions: Vec<(u8, u8)>,
	},
	/// Register a new protocol timer
	AddTimer {
		/// Protocol Id.
		protocol: ProtocolId,
		/// Timer token.
		token: TimerToken,
		/// Timer delay.
		delay: Duration,
	},
	/// Initliaze public interface.
	InitPublicInterface,
	/// Disconnect a peer.
	Disconnect(PeerId),
	/// Disconnect and temporary disable peer.
	DisablePeer(PeerId),
	/// Network has been started with the host as the given enode.
	NetworkStarted(String),
}

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
	pub listen_address: Option<SocketAddr>,
	/// IP address to advertise. Detected automatically if none.
	pub public_address: Option<SocketAddr>,
	/// Port for UDP connections, same as TCP by default
	pub udp_port: Option<u16>,
	/// Enable NAT configuration
	pub nat_enabled: bool,
	/// Enable discovery
	pub discovery_enabled: bool,
	/// List of initial node addresses
	pub boot_nodes: Vec<String>,
	/// Use provided node key instead of default
	pub use_secret: Option<Secret>,
	/// Minimum number of connected peers to maintain
	pub min_peers: u32,
	/// Maximum allowed number of peers
	pub max_peers: u32,
	/// At most `1 / incoming_peers_factor` of incoming connections are allowed.
	pub incoming_peers_factor: u32,
	/// Maximum handshakes
	pub max_handshakes: u32,
	/// Reserved protocols. Peers with <key> protocol get additional <value> connection slots.
	pub reserved_protocols: HashMap<ProtocolId, u32>,
	/// List of reserved node addresses.
	pub reserved_nodes: Vec<String>,
	/// The non-reserved peer mode.
	pub non_reserved_mode: NonReservedPeerMode,
	/// IP filter
	pub ip_filter: IpFilter,
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
			listen_address: None,
			public_address: None,
			udp_port: None,
			nat_enabled: true,
			discovery_enabled: true,
			boot_nodes: Vec::new(),
			use_secret: None,
			min_peers: 25,
			max_peers: 50,
			incoming_peers_factor: 3,
			max_handshakes: 64,
			reserved_protocols: HashMap::new(),
			ip_filter: IpFilter::default(),
			reserved_nodes: Vec::new(),
			non_reserved_mode: NonReservedPeerMode::Accept,
			client_version: "Parity-network".into(),
		}
	}

	/// Create new default configuration with specified listen port.
	pub fn new_with_port(port: u16) -> NetworkConfiguration {
		let mut config = NetworkConfiguration::new();
		config.listen_address = Some(SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(0, 0, 0, 0), port)));
		config
	}

	/// Create new default configuration for localhost-only connection with random port (usefull for testing)
	pub fn new_local() -> NetworkConfiguration {
		let mut config = NetworkConfiguration::new();
		config.listen_address = Some(SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), 0)));
		config.nat_enabled = false;
		config
	}
}

/// IO access point. This is passed to all IO handlers and provides an interface to the IO subsystem.
pub trait NetworkContext {
	/// Send a packet over the network to another peer.
	fn send(&self, peer: PeerId, packet_id: PacketId, data: Vec<u8>) -> Result<(), Error>;

	/// Send a packet over the network to another peer using specified protocol.
	fn send_protocol(&self, protocol: ProtocolId, peer: PeerId, packet_id: PacketId, data: Vec<u8>) -> Result<(), Error>;

	/// Respond to a current network message. Panics if no there is no packet in the context. If the session is expired returns nothing.
	fn respond(&self, packet_id: PacketId, data: Vec<u8>) -> Result<(), Error>;

	/// Disconnect a peer and prevent it from connecting again.
	fn disable_peer(&self, peer: PeerId, reason: &str);

	/// Disconnect peer. Reconnect can be attempted later.
	fn disconnect_peer(&self, peer: PeerId);

	/// Check if the session is still active.
	fn is_expired(&self) -> bool;

	/// Register a new IO timer. 'IoHandler::timeout' will be called with the token.
	fn register_timer(&self, token: TimerToken, delay: Duration) -> Result<(), Error>;

	/// Returns peer identification string
	fn peer_client_version(&self, peer: PeerId) -> String;

	/// Returns information on p2p session
	fn session_info(&self, peer: PeerId) -> Option<SessionInfo>;

	/// Returns max version for a given protocol.
	fn protocol_version(&self, protocol: ProtocolId, peer: PeerId) -> Option<u8>;

	/// Returns this object's subprotocol name.
	fn subprotocol_name(&self) -> ProtocolId;
}

impl<'a, T> NetworkContext for &'a T where T: ?Sized + NetworkContext {
	fn send(&self, peer: PeerId, packet_id: PacketId, data: Vec<u8>) -> Result<(), Error> {
		(**self).send(peer, packet_id, data)
	}

	fn send_protocol(&self, protocol: ProtocolId, peer: PeerId, packet_id: PacketId, data: Vec<u8>) -> Result<(), Error> {
		(**self).send_protocol(protocol, peer, packet_id, data)
	}

	fn respond(&self, packet_id: PacketId, data: Vec<u8>) -> Result<(), Error> {
		(**self).respond(packet_id, data)
	}

	fn disable_peer(&self, peer: PeerId, reason: &str) {
		(**self).disable_peer(peer, reason)
	}

	fn disconnect_peer(&self, peer: PeerId) {
		(**self).disconnect_peer(peer)
	}

	fn is_expired(&self) -> bool {
		(**self).is_expired()
	}

	fn register_timer(&self, token: TimerToken, delay: Duration) -> Result<(), Error> {
		(**self).register_timer(token, delay)
	}

	fn peer_client_version(&self, peer: PeerId) -> String {
		(**self).peer_client_version(peer)
	}

	fn session_info(&self, peer: PeerId) -> Option<SessionInfo> {
		(**self).session_info(peer)
	}

	fn protocol_version(&self, protocol: ProtocolId, peer: PeerId) -> Option<u8> {
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
	fn read(&self, io: &NetworkContext, peer: &PeerId, packet_id: u8, data: &[u8]);
	/// Called when new peer is connected. Only called when peer supports the same protocol.
	fn connected(&self, io: &NetworkContext, peer: &PeerId);
	/// Called when a previously connected peer disconnects.
	fn disconnected(&self, io: &NetworkContext, peer: &PeerId);
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IpFilter {
    pub predefined: AllowIP,
    pub custom_allow: Vec<IpNetwork>,
    pub custom_block: Vec<IpNetwork>,
}

impl Default for IpFilter {
    fn default() -> Self {
        IpFilter {
            predefined: AllowIP::All,
            custom_allow: vec![],
            custom_block: vec![],
        }
    }
}

impl IpFilter {
    /// Attempt to parse the peer mode from a string.
    pub fn parse(s: &str) -> Result<IpFilter, IpNetworkError> {
        let mut filter = IpFilter::default();
        for f in s.split_whitespace() {
            match f {
                "all" => filter.predefined = AllowIP::All,
                "private" => filter.predefined = AllowIP::Private,
                "public" => filter.predefined = AllowIP::Public,
                "none" => filter.predefined = AllowIP::None,
                custom => {
                    if custom.starts_with("-") {
                        filter.custom_block.push(IpNetwork::from_str(&custom.to_owned().split_off(1))?)
                    } else {
                        filter.custom_allow.push(IpNetwork::from_str(custom)?)
                    }
                }
            }
        }
        Ok(filter)
    }
}

/// IP fiter
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AllowIP {
	/// Connect to any address
	All,
	/// Connect to private network only
	Private,
	/// Connect to public network only
	Public,
    /// Block all addresses
    None,
}
