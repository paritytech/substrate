// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Configuration of the networking layer.
//!
//! The [`Params`] struct is the struct that must be passed in order to initialize the networking.
//! See the documentation of [`Params`].

pub use crate::{
	discovery::DEFAULT_KADEMLIA_REPLICATION_FACTOR,
	protocol::NotificationsSink,
	request_responses::{
		IncomingRequest, OutgoingResponse, ProtocolConfig as RequestResponseConfig,
	},
	types::ProtocolName,
};

pub use libp2p::{identity::Keypair, multiaddr, Multiaddr, PeerId};

use crate::peer_store::PeerStoreHandle;
use codec::Encode;
use prometheus_endpoint::Registry;
use zeroize::Zeroize;

pub use sc_network_common::{
	role::{Role, Roles},
	sync::{warp::WarpSyncProvider, SyncMode},
	ExHashT,
};
use sc_utils::mpsc::TracingUnboundedSender;
use sp_runtime::traits::Block as BlockT;

use std::{
	error::Error,
	fmt, fs,
	future::Future,
	io::{self, Write},
	iter,
	net::Ipv4Addr,
	num::NonZeroUsize,
	path::{Path, PathBuf},
	pin::Pin,
	str::{self, FromStr},
};

pub use libp2p::{
	build_multiaddr,
	identity::{self, ed25519},
};

/// Protocol name prefix, transmitted on the wire for legacy protocol names.
/// I.e., `dot` in `/dot/sync/2`. Should be unique for each chain. Always UTF-8.
/// Deprecated in favour of genesis hash & fork ID based protocol names.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ProtocolId(smallvec::SmallVec<[u8; 6]>);

impl<'a> From<&'a str> for ProtocolId {
	fn from(bytes: &'a str) -> ProtocolId {
		Self(bytes.as_bytes().into())
	}
}

impl AsRef<str> for ProtocolId {
	fn as_ref(&self) -> &str {
		str::from_utf8(&self.0[..])
			.expect("the only way to build a ProtocolId is through a UTF-8 String; qed")
	}
}

impl fmt::Debug for ProtocolId {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt::Debug::fmt(self.as_ref(), f)
	}
}

/// Parses a string address and splits it into Multiaddress and PeerId, if
/// valid.
///
/// # Example
///
/// ```
/// # use libp2p::{Multiaddr, PeerId};
/// use sc_network::config::parse_str_addr;
/// let (peer_id, addr) = parse_str_addr(
/// 	"/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV"
/// ).unwrap();
/// assert_eq!(peer_id, "QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".parse::<PeerId>().unwrap());
/// assert_eq!(addr, "/ip4/198.51.100.19/tcp/30333".parse::<Multiaddr>().unwrap());
/// ```
pub fn parse_str_addr(addr_str: &str) -> Result<(PeerId, Multiaddr), ParseErr> {
	let addr: Multiaddr = addr_str.parse()?;
	parse_addr(addr)
}

/// Splits a Multiaddress into a Multiaddress and PeerId.
pub fn parse_addr(mut addr: Multiaddr) -> Result<(PeerId, Multiaddr), ParseErr> {
	let who = match addr.pop() {
		Some(multiaddr::Protocol::P2p(key)) =>
			PeerId::from_multihash(key).map_err(|_| ParseErr::InvalidPeerId)?,
		_ => return Err(ParseErr::PeerIdMissing),
	};

	Ok((who, addr))
}

/// Address of a node, including its identity.
///
/// This struct represents a decoded version of a multiaddress that ends with `/p2p/<peerid>`.
///
/// # Example
///
/// ```
/// # use libp2p::{Multiaddr, PeerId};
/// use sc_network::config::MultiaddrWithPeerId;
/// let addr: MultiaddrWithPeerId =
/// 	"/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".parse().unwrap();
/// assert_eq!(addr.peer_id.to_base58(), "QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV");
/// assert_eq!(addr.multiaddr.to_string(), "/ip4/198.51.100.19/tcp/30333");
/// ```
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq)]
#[serde(try_from = "String", into = "String")]
pub struct MultiaddrWithPeerId {
	/// Address of the node.
	pub multiaddr: Multiaddr,
	/// Its identity.
	pub peer_id: PeerId,
}

impl MultiaddrWithPeerId {
	/// Concatenates the multiaddress and peer ID into one multiaddress containing both.
	pub fn concat(&self) -> Multiaddr {
		let proto = multiaddr::Protocol::P2p(From::from(self.peer_id));
		self.multiaddr.clone().with(proto)
	}
}

impl fmt::Display for MultiaddrWithPeerId {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt::Display::fmt(&self.concat(), f)
	}
}

impl FromStr for MultiaddrWithPeerId {
	type Err = ParseErr;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		let (peer_id, multiaddr) = parse_str_addr(s)?;
		Ok(Self { peer_id, multiaddr })
	}
}

impl From<MultiaddrWithPeerId> for String {
	fn from(ma: MultiaddrWithPeerId) -> String {
		format!("{}", ma)
	}
}

impl TryFrom<String> for MultiaddrWithPeerId {
	type Error = ParseErr;
	fn try_from(string: String) -> Result<Self, Self::Error> {
		string.parse()
	}
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
			Self::MultiaddrParse(err) => write!(f, "{}", err),
			Self::InvalidPeerId => write!(f, "Peer id at the end of the address is invalid"),
			Self::PeerIdMissing => write!(f, "Peer id is missing from the address"),
		}
	}
}

impl std::error::Error for ParseErr {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			Self::MultiaddrParse(err) => Some(err),
			Self::InvalidPeerId => None,
			Self::PeerIdMissing => None,
		}
	}
}

impl From<multiaddr::Error> for ParseErr {
	fn from(err: multiaddr::Error) -> ParseErr {
		Self::MultiaddrParse(err)
	}
}

/// Custom handshake for the notification protocol
#[derive(Debug, Clone)]
pub struct NotificationHandshake(Vec<u8>);

impl NotificationHandshake {
	/// Create new `NotificationHandshake` from an object that implements `Encode`
	pub fn new<H: Encode>(handshake: H) -> Self {
		Self(handshake.encode())
	}

	/// Create new `NotificationHandshake` from raw bytes
	pub fn from_bytes(bytes: Vec<u8>) -> Self {
		Self(bytes)
	}
}

impl std::ops::Deref for NotificationHandshake {
	type Target = Vec<u8>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

/// Configuration for the transport layer.
#[derive(Clone, Debug)]
pub enum TransportConfig {
	/// Normal transport mode.
	Normal {
		/// If true, the network will use mDNS to discover other libp2p nodes on the local network
		/// and connect to them if they support the same chain.
		enable_mdns: bool,

		/// If true, allow connecting to private IPv4/IPv6 addresses (as defined in
		/// [RFC1918](https://tools.ietf.org/html/rfc1918)). Irrelevant for addresses that have
		/// been passed in `::sc_network::config::NetworkConfiguration::boot_nodes`.
		allow_private_ip: bool,
	},

	/// Only allow connections within the same process.
	/// Only addresses of the form `/memory/...` will be supported.
	MemoryOnly,
}

/// The policy for connections to non-reserved peers.
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
			"accept" => Some(Self::Accept),
			"deny" => Some(Self::Deny),
			_ => None,
		}
	}

	/// If we are in "reserved-only" peer mode.
	pub fn is_reserved_only(&self) -> bool {
		matches!(self, NonReservedPeerMode::Deny)
	}
}

/// The configuration of a node's secret key, describing the type of key
/// and how it is obtained. A node's identity keypair is the result of
/// the evaluation of the node key configuration.
#[derive(Clone, Debug)]
pub enum NodeKeyConfig {
	/// A Ed25519 secret key configuration.
	Ed25519(Secret<ed25519::SecretKey>),
}

impl Default for NodeKeyConfig {
	fn default() -> NodeKeyConfig {
		Self::Ed25519(Secret::New)
	}
}

/// The options for obtaining a Ed25519 secret key.
pub type Ed25519Secret = Secret<ed25519::SecretKey>;

/// The configuration options for obtaining a secret key `K`.
#[derive(Clone)]
pub enum Secret<K> {
	/// Use the given secret key `K`.
	Input(K),
	/// Read the secret key from a file. If the file does not exist,
	/// it is created with a newly generated secret key `K`. The format
	/// of the file is determined by `K`:
	///
	///   * `ed25519::SecretKey`: An unencoded 32 bytes Ed25519 secret key.
	File(PathBuf),
	/// Always generate a new secret key `K`.
	New,
}

impl<K> fmt::Debug for Secret<K> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Self::Input(_) => f.debug_tuple("Secret::Input").finish(),
			Self::File(path) => f.debug_tuple("Secret::File").field(path).finish(),
			Self::New => f.debug_tuple("Secret::New").finish(),
		}
	}
}

impl NodeKeyConfig {
	/// Evaluate a `NodeKeyConfig` to obtain an identity `Keypair`:
	///
	///  * If the secret is configured as input, the corresponding keypair is returned.
	///
	///  * If the secret is configured as a file, it is read from that file, if it exists. Otherwise
	///    a new secret is generated and stored. In either case, the keypair obtained from the
	///    secret is returned.
	///
	///  * If the secret is configured to be new, it is generated and the corresponding keypair is
	///    returned.
	pub fn into_keypair(self) -> io::Result<Keypair> {
		use NodeKeyConfig::*;
		match self {
			Ed25519(Secret::New) => Ok(Keypair::generate_ed25519()),

			Ed25519(Secret::Input(k)) => Ok(ed25519::Keypair::from(k).into()),

			Ed25519(Secret::File(f)) => get_secret(
				f,
				|mut b| match String::from_utf8(b.to_vec()).ok().and_then(|s| {
					if s.len() == 64 {
						array_bytes::hex2bytes(&s).ok()
					} else {
						None
					}
				}) {
					Some(s) => ed25519::SecretKey::try_from_bytes(s),
					_ => ed25519::SecretKey::try_from_bytes(&mut b),
				},
				ed25519::SecretKey::generate,
				|b| b.as_ref().to_vec(),
			)
			.map(ed25519::Keypair::from)
			.map(Keypair::from),
		}
	}
}

/// Load a secret key from a file, if it exists, or generate a
/// new secret key and write it to that file. In either case,
/// the secret key is returned.
fn get_secret<P, F, G, E, W, K>(file: P, parse: F, generate: G, serialize: W) -> io::Result<K>
where
	P: AsRef<Path>,
	F: for<'r> FnOnce(&'r mut [u8]) -> Result<K, E>,
	G: FnOnce() -> K,
	E: Error + Send + Sync + 'static,
	W: Fn(&K) -> Vec<u8>,
{
	std::fs::read(&file)
		.and_then(|mut sk_bytes| {
			parse(&mut sk_bytes).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
		})
		.or_else(|e| {
			if e.kind() == io::ErrorKind::NotFound {
				file.as_ref().parent().map_or(Ok(()), fs::create_dir_all)?;
				let sk = generate();
				let mut sk_vec = serialize(&sk);
				write_secret_file(file, &sk_vec)?;
				sk_vec.zeroize();
				Ok(sk)
			} else {
				Err(e)
			}
		})
}

/// Write secret bytes to a file.
fn write_secret_file<P>(path: P, sk_bytes: &[u8]) -> io::Result<()>
where
	P: AsRef<Path>,
{
	let mut file = open_secret_file(&path)?;
	file.write_all(sk_bytes)
}

/// Opens a file containing a secret key in write mode.
#[cfg(unix)]
fn open_secret_file<P>(path: P) -> io::Result<fs::File>
where
	P: AsRef<Path>,
{
	use std::os::unix::fs::OpenOptionsExt;
	fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(path)
}

/// Opens a file containing a secret key in write mode.
#[cfg(not(unix))]
fn open_secret_file<P>(path: P) -> Result<fs::File, io::Error>
where
	P: AsRef<Path>,
{
	fs::OpenOptions::new().write(true).create_new(true).open(path)
}

/// Configuration for a set of nodes.
#[derive(Clone, Debug)]
pub struct SetConfig {
	/// Maximum allowed number of incoming substreams related to this set.
	pub in_peers: u32,

	/// Number of outgoing substreams related to this set that we're trying to maintain.
	pub out_peers: u32,

	/// List of reserved node addresses.
	pub reserved_nodes: Vec<MultiaddrWithPeerId>,

	/// Whether nodes that aren't in [`SetConfig::reserved_nodes`] are accepted or automatically
	/// refused.
	pub non_reserved_mode: NonReservedPeerMode,
}

impl Default for SetConfig {
	fn default() -> Self {
		Self {
			in_peers: 25,
			out_peers: 75,
			reserved_nodes: Vec::new(),
			non_reserved_mode: NonReservedPeerMode::Accept,
		}
	}
}

/// Extension to [`SetConfig`] for sets that aren't the default set.
///
/// > **Note**: As new fields might be added in the future, please consider using the `new` method
/// >			and modifiers instead of creating this struct manually.
#[derive(Clone, Debug)]
pub struct NonDefaultSetConfig {
	/// Name of the notifications protocols of this set. A substream on this set will be
	/// considered established once this protocol is open.
	///
	/// > **Note**: This field isn't present for the default set, as this is handled internally
	/// > by the networking code.
	pub notifications_protocol: ProtocolName,

	/// If the remote reports that it doesn't support the protocol indicated in the
	/// `notifications_protocol` field, then each of these fallback names will be tried one by
	/// one.
	///
	/// If a fallback is used, it will be reported in
	/// `sc_network::protocol::event::Event::NotificationStreamOpened::negotiated_fallback`
	pub fallback_names: Vec<ProtocolName>,

	/// Handshake of the protocol
	///
	/// NOTE: Currently custom handshakes are not fully supported. See issue #5685 for more
	/// details. This field is temporarily used to allow moving the hardcoded block announcement
	/// protocol out of `protocol.rs`.
	pub handshake: Option<NotificationHandshake>,

	/// Maximum allowed size of single notifications.
	pub max_notification_size: u64,

	/// Base configuration.
	pub set_config: SetConfig,
}

impl NonDefaultSetConfig {
	/// Creates a new [`NonDefaultSetConfig`]. Zero slots and accepts only reserved nodes.
	pub fn new(notifications_protocol: ProtocolName, max_notification_size: u64) -> Self {
		Self {
			notifications_protocol,
			max_notification_size,
			fallback_names: Vec::new(),
			handshake: None,
			set_config: SetConfig {
				in_peers: 0,
				out_peers: 0,
				reserved_nodes: Vec::new(),
				non_reserved_mode: NonReservedPeerMode::Deny,
			},
		}
	}

	/// Modifies the configuration to allow non-reserved nodes.
	pub fn allow_non_reserved(&mut self, in_peers: u32, out_peers: u32) {
		self.set_config.in_peers = in_peers;
		self.set_config.out_peers = out_peers;
		self.set_config.non_reserved_mode = NonReservedPeerMode::Accept;
	}

	/// Add a node to the list of reserved nodes.
	pub fn add_reserved(&mut self, peer: MultiaddrWithPeerId) {
		self.set_config.reserved_nodes.push(peer);
	}

	/// Add a list of protocol names used for backward compatibility.
	///
	/// See the explanations in [`NonDefaultSetConfig::fallback_names`].
	pub fn add_fallback_names(&mut self, fallback_names: Vec<ProtocolName>) {
		self.fallback_names.extend(fallback_names);
	}
}

/// Network service configuration.
#[derive(Clone, Debug)]
pub struct NetworkConfiguration {
	/// Directory path to store network-specific configuration. None means nothing will be saved.
	pub net_config_path: Option<PathBuf>,

	/// Multiaddresses to listen for incoming connections.
	pub listen_addresses: Vec<Multiaddr>,

	/// Multiaddresses to advertise. Detected automatically if empty.
	pub public_addresses: Vec<Multiaddr>,

	/// List of initial node addresses
	pub boot_nodes: Vec<MultiaddrWithPeerId>,

	/// The node key configuration, which determines the node's network identity keypair.
	pub node_key: NodeKeyConfig,

	/// Configuration for the default set of nodes used for block syncing and transactions.
	pub default_peers_set: SetConfig,

	/// Number of substreams to reserve for full nodes for block syncing and transactions.
	/// Any other slot will be dedicated to light nodes.
	///
	/// This value is implicitly capped to `default_set.out_peers + default_set.in_peers`.
	pub default_peers_set_num_full: u32,

	/// Client identifier. Sent over the wire for debugging purposes.
	pub client_version: String,

	/// Name of the node. Sent over the wire for debugging purposes.
	pub node_name: String,

	/// Configuration for the transport layer.
	pub transport: TransportConfig,

	/// Maximum number of peers to ask the same blocks in parallel.
	pub max_parallel_downloads: u32,

	/// Maximum number of blocks per request.
	pub max_blocks_per_request: u32,

	/// Initial syncing mode.
	pub sync_mode: SyncMode,

	/// True if Kademlia random discovery should be enabled.
	///
	/// If true, the node will automatically randomly walk the DHT in order to find new peers.
	pub enable_dht_random_walk: bool,

	/// Should we insert non-global addresses into the DHT?
	pub allow_non_globals_in_dht: bool,

	/// Require iterative Kademlia DHT queries to use disjoint paths for increased resiliency in
	/// the presence of potentially adversarial nodes.
	pub kademlia_disjoint_query_paths: bool,

	/// Kademlia replication factor determines to how many closest peers a record is replicated to.
	///
	/// Discovery mechanism requires successful replication to all
	/// `kademlia_replication_factor` peers to consider record successfully put.
	pub kademlia_replication_factor: NonZeroUsize,

	/// Enable serving block data over IPFS bitswap.
	pub ipfs_server: bool,

	/// Size of Yamux receive window of all substreams. `None` for the default (256kiB).
	/// Any value less than 256kiB is invalid.
	///
	/// # Context
	///
	/// By design, notifications substreams on top of Yamux connections only allow up to `N` bytes
	/// to be transferred at a time, where `N` is the Yamux receive window size configurable here.
	/// This means, in practice, that every `N` bytes must be acknowledged by the receiver before
	/// the sender can send more data. The maximum bandwidth of each notifications substream is
	/// therefore `N / round_trip_time`.
	///
	/// It is recommended to leave this to `None`, and use a request-response protocol instead if
	/// a large amount of data must be transferred. The reason why the value is configurable is
	/// that some Substrate users mis-use notification protocols to send large amounts of data.
	/// As such, this option isn't designed to stay and will likely get removed in the future.
	///
	/// Note that configuring a value here isn't a modification of the Yamux protocol, but rather
	/// a modification of the way the implementation works. Different nodes with different
	/// configured values remain compatible with each other.
	pub yamux_window_size: Option<u32>,
}

impl NetworkConfiguration {
	/// Create new default configuration
	pub fn new<SN: Into<String>, SV: Into<String>>(
		node_name: SN,
		client_version: SV,
		node_key: NodeKeyConfig,
		net_config_path: Option<PathBuf>,
	) -> Self {
		let default_peers_set = SetConfig::default();
		Self {
			net_config_path,
			listen_addresses: Vec::new(),
			public_addresses: Vec::new(),
			boot_nodes: Vec::new(),
			node_key,
			default_peers_set_num_full: default_peers_set.in_peers + default_peers_set.out_peers,
			default_peers_set,
			client_version: client_version.into(),
			node_name: node_name.into(),
			transport: TransportConfig::Normal { enable_mdns: false, allow_private_ip: true },
			max_parallel_downloads: 5,
			max_blocks_per_request: 64,
			sync_mode: SyncMode::Full,
			enable_dht_random_walk: true,
			allow_non_globals_in_dht: false,
			kademlia_disjoint_query_paths: false,
			kademlia_replication_factor: NonZeroUsize::new(DEFAULT_KADEMLIA_REPLICATION_FACTOR)
				.expect("value is a constant; constant is non-zero; qed."),
			yamux_window_size: None,
			ipfs_server: false,
		}
	}

	/// Create new default configuration for localhost-only connection with random port (useful for
	/// testing)
	pub fn new_local() -> NetworkConfiguration {
		let mut config =
			NetworkConfiguration::new("test-node", "test-client", Default::default(), None);

		config.listen_addresses =
			vec![iter::once(multiaddr::Protocol::Ip4(Ipv4Addr::new(127, 0, 0, 1)))
				.chain(iter::once(multiaddr::Protocol::Tcp(0)))
				.collect()];

		config.allow_non_globals_in_dht = true;
		config
	}

	/// Create new default configuration for localhost-only connection with random port (useful for
	/// testing)
	pub fn new_memory() -> NetworkConfiguration {
		let mut config =
			NetworkConfiguration::new("test-node", "test-client", Default::default(), None);

		config.listen_addresses =
			vec![iter::once(multiaddr::Protocol::Ip4(Ipv4Addr::new(127, 0, 0, 1)))
				.chain(iter::once(multiaddr::Protocol::Tcp(0)))
				.collect()];

		config.allow_non_globals_in_dht = true;
		config
	}
}

/// Network initialization parameters.
pub struct Params<Block: BlockT> {
	/// Assigned role for our node (full, light, ...).
	pub role: Role,

	/// How to spawn background tasks.
	pub executor: Box<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>) + Send>,

	/// Network layer configuration.
	pub network_config: FullNetworkConfiguration,

	/// Peer store with known nodes, peer reputations, etc.
	pub peer_store: PeerStoreHandle,

	/// Legacy name of the protocol to use on the wire. Should be different for each chain.
	pub protocol_id: ProtocolId,

	/// Genesis hash of the chain
	pub genesis_hash: Block::Hash,

	/// Fork ID to distinguish protocols of different hard forks. Part of the standard protocol
	/// name on the wire.
	pub fork_id: Option<String>,

	/// Registry for recording prometheus metrics to.
	pub metrics_registry: Option<Registry>,

	/// Block announce protocol configuration
	pub block_announce_config: NonDefaultSetConfig,

	/// TX channel for direct communication with `SyncingEngine` and `Protocol`.
	pub tx: TracingUnboundedSender<crate::event::SyncEvent<Block>>,
}

/// Full network configuration.
pub struct FullNetworkConfiguration {
	/// Installed notification protocols.
	pub(crate) notification_protocols: Vec<NonDefaultSetConfig>,

	/// List of request-response protocols that the node supports.
	pub(crate) request_response_protocols: Vec<RequestResponseConfig>,

	/// Network configuration.
	pub network_config: NetworkConfiguration,
}

impl FullNetworkConfiguration {
	/// Create new [`FullNetworkConfiguration`].
	pub fn new(network_config: &NetworkConfiguration) -> Self {
		Self {
			notification_protocols: Vec::new(),
			request_response_protocols: Vec::new(),
			network_config: network_config.clone(),
		}
	}

	/// Add a notification protocol.
	pub fn add_notification_protocol(&mut self, config: NonDefaultSetConfig) {
		self.notification_protocols.push(config);
	}

	/// Get reference to installed notification protocols.
	pub fn notification_protocols(&self) -> &Vec<NonDefaultSetConfig> {
		&self.notification_protocols
	}

	/// Add a request-response protocol.
	pub fn add_request_response_protocol(&mut self, config: RequestResponseConfig) {
		self.request_response_protocols.push(config);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use tempfile::TempDir;

	fn tempdir_with_prefix(prefix: &str) -> TempDir {
		tempfile::Builder::new().prefix(prefix).tempdir().unwrap()
	}

	fn secret_bytes(kp: Keypair) -> Vec<u8> {
		kp.try_into_ed25519()
			.expect("ed25519 keypair")
			.secret()
			.as_ref()
			.iter()
			.cloned()
			.collect()
	}

	#[test]
	fn test_secret_file() {
		let tmp = tempdir_with_prefix("x");
		std::fs::remove_dir(tmp.path()).unwrap(); // should be recreated
		let file = tmp.path().join("x").to_path_buf();
		let kp1 = NodeKeyConfig::Ed25519(Secret::File(file.clone())).into_keypair().unwrap();
		let kp2 = NodeKeyConfig::Ed25519(Secret::File(file.clone())).into_keypair().unwrap();
		assert!(file.is_file() && secret_bytes(kp1) == secret_bytes(kp2))
	}

	#[test]
	fn test_secret_input() {
		let sk = ed25519::SecretKey::generate();
		let kp1 = NodeKeyConfig::Ed25519(Secret::Input(sk.clone())).into_keypair().unwrap();
		let kp2 = NodeKeyConfig::Ed25519(Secret::Input(sk)).into_keypair().unwrap();
		assert!(secret_bytes(kp1) == secret_bytes(kp2));
	}

	#[test]
	fn test_secret_new() {
		let kp1 = NodeKeyConfig::Ed25519(Secret::New).into_keypair().unwrap();
		let kp2 = NodeKeyConfig::Ed25519(Secret::New).into_keypair().unwrap();
		assert!(secret_bytes(kp1) != secret_bytes(kp2));
	}
}
