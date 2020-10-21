// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

pub use crate::chain::{Client, FinalityProofProvider};
pub use crate::on_demand_layer::{AlwaysBadChecker, OnDemand};
pub use crate::request_responses::{IncomingRequest, ProtocolConfig as RequestResponseConfig};
pub use libp2p::{identity, core::PublicKey, wasm_ext::ExtTransport, build_multiaddr};

// Note: this re-export shouldn't be part of the public API of the crate and will be removed in
// the future.
#[doc(hidden)]
pub use crate::protocol::ProtocolConfig;

use crate::ExHashT;

use core::{fmt, iter};
use futures::future;
use libp2p::{
	identity::{ed25519, Keypair},
	multiaddr, wasm_ext, Multiaddr, PeerId,
};
use prometheus_endpoint::Registry;
use sp_consensus::{block_validation::BlockAnnounceValidator, import_queue::ImportQueue};
use sp_runtime::{traits::Block as BlockT, ConsensusEngineId};
use std::{borrow::Cow, convert::TryFrom, future::Future, pin::Pin, str::FromStr};
use std::{
	collections::HashMap,
	error::Error,
	fs,
	io::{self, Write},
	net::Ipv4Addr,
	path::{Path, PathBuf},
	str,
	sync::Arc,
};
use zeroize::Zeroize;

/// Network initialization parameters.
pub struct Params<B: BlockT, H: ExHashT> {
	/// Assigned role for our node (full, light, ...).
	pub role: Role,

	/// How to spawn background tasks. If you pass `None`, then a threads pool will be used by
	/// default.
	pub executor: Option<Box<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>) + Send>>,

	/// Network layer configuration.
	pub network_config: NetworkConfiguration,

	/// Client that contains the blockchain.
	pub chain: Arc<dyn Client<B>>,

	/// Finality proof provider.
	///
	/// This object, if `Some`, is used when a node on the network requests a proof of finality
	/// from us.
	pub finality_proof_provider: Option<Arc<dyn FinalityProofProvider<B>>>,

	/// How to build requests for proofs of finality.
	///
	/// This object, if `Some`, is used when we need a proof of finality from another node.
	pub finality_proof_request_builder: Option<BoxFinalityProofRequestBuilder<B>>,

	/// The `OnDemand` object acts as a "receiver" for block data requests from the client.
	/// If `Some`, the network worker will process these requests and answer them.
	/// Normally used only for light clients.
	pub on_demand: Option<Arc<OnDemand<B>>>,

	/// Pool of transactions.
	///
	/// The network worker will fetch transactions from this object in order to propagate them on
	/// the network.
	pub transaction_pool: Arc<dyn TransactionPool<H, B>>,

	/// Name of the protocol to use on the wire. Should be different for each chain.
	pub protocol_id: ProtocolId,

	/// Import queue to use.
	///
	/// The import queue is the component that verifies that blocks received from other nodes are
	/// valid.
	pub import_queue: Box<dyn ImportQueue<B>>,

	/// Type to check incoming block announcements.
	pub block_announce_validator: Box<dyn BlockAnnounceValidator<B> + Send>,

	/// Registry for recording prometheus metrics to.
	pub metrics_registry: Option<Registry>,
}

/// Role of the local node.
#[derive(Debug, Clone)]
pub enum Role {
	/// Regular full node.
	Full,
	/// Regular light node.
	Light,
	/// Sentry node that guards an authority. Will be reported as "authority" on the wire protocol.
	Sentry {
		/// Address and identity of the validator nodes that we're guarding.
		///
		/// The nodes will be granted some priviledged status.
		validators: Vec<MultiaddrWithPeerId>,
	},
	/// Actual authority.
	Authority {
		/// List of public addresses and identities of our sentry nodes.
		sentry_nodes: Vec<MultiaddrWithPeerId>,
	}
}

impl Role {
	/// True for `Role::Authority`
	pub fn is_authority(&self) -> bool {
		matches!(self, Role::Authority { .. })
	}

	/// True for `Role::Authority` and `Role::Sentry` since they're both
	/// announced as having the authority role to the network.
	pub fn is_network_authority(&self) -> bool {
		matches!(self, Role::Authority { .. } | Role::Sentry { .. })
	}
}

impl fmt::Display for Role {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Role::Full => write!(f, "FULL"),
			Role::Light => write!(f, "LIGHT"),
			Role::Sentry { .. } => write!(f, "SENTRY"),
			Role::Authority { .. } => write!(f, "AUTHORITY"),
		}
	}
}

/// Finality proof request builder.
pub trait FinalityProofRequestBuilder<B: BlockT>: Send {
	/// Build data blob, associated with the request.
	fn build_request_data(&mut self, hash: &B::Hash) -> Vec<u8>;
}

/// Implementation of `FinalityProofRequestBuilder` that builds a dummy empty request.
#[derive(Debug, Default)]
pub struct DummyFinalityProofRequestBuilder;

impl<B: BlockT> FinalityProofRequestBuilder<B> for DummyFinalityProofRequestBuilder {
	fn build_request_data(&mut self, _: &B::Hash) -> Vec<u8> {
		Vec::new()
	}
}

/// Shared finality proof request builder struct used by the queue.
pub type BoxFinalityProofRequestBuilder<B> = Box<dyn FinalityProofRequestBuilder<B> + Send + Sync>;

/// Result of the transaction import.
#[derive(Clone, Copy, Debug)]
pub enum TransactionImport {
	/// Transaction is good but already known by the transaction pool.
	KnownGood,
	/// Transaction is good and not yet known.
	NewGood,
	/// Transaction is invalid.
	Bad,
	/// Transaction import was not performed.
	None,
}

/// Fuure resolving to transaction import result.
pub type TransactionImportFuture = Pin<Box<dyn Future<Output=TransactionImport> + Send>>;

/// Transaction pool interface
pub trait TransactionPool<H: ExHashT, B: BlockT>: Send + Sync {
	/// Get transactions from the pool that are ready to be propagated.
	fn transactions(&self) -> Vec<(H, B::Extrinsic)>;
	/// Get hash of transaction.
	fn hash_of(&self, transaction: &B::Extrinsic) -> H;
	/// Import a transaction into the pool.
	///
	/// This will return future.
	fn import(
		&self,
		transaction: B::Extrinsic,
	) -> TransactionImportFuture;
	/// Notify the pool about transactions broadcast.
	fn on_broadcasted(&self, propagations: HashMap<H, Vec<String>>);
	/// Get transaction by hash.
	fn transaction(&self, hash: &H) -> Option<B::Extrinsic>;
}

/// Dummy implementation of the [`TransactionPool`] trait for a transaction pool that is always
/// empty and discards all incoming transactions.
///
/// Requires the "hash" type to implement the `Default` trait.
///
/// Useful for testing purposes.
pub struct EmptyTransactionPool;

impl<H: ExHashT + Default, B: BlockT> TransactionPool<H, B> for EmptyTransactionPool {
	fn transactions(&self) -> Vec<(H, B::Extrinsic)> {
		Vec::new()
	}

	fn hash_of(&self, _transaction: &B::Extrinsic) -> H {
		Default::default()
	}

	fn import(
		&self,
		_transaction: B::Extrinsic
	) -> TransactionImportFuture {
		Box::pin(future::ready(TransactionImport::KnownGood))
	}

	fn on_broadcasted(&self, _: HashMap<H, Vec<String>>) {}

	fn transaction(&self, _h: &H) -> Option<B::Extrinsic> { None }
}

/// Name of a protocol, transmitted on the wire. Should be unique for each chain. Always UTF-8.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ProtocolId(smallvec::SmallVec<[u8; 6]>);

impl<'a> From<&'a str> for ProtocolId {
	fn from(bytes: &'a str) -> ProtocolId {
		ProtocolId(bytes.as_bytes().into())
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
/// # use sc_network::{Multiaddr, PeerId, config::parse_str_addr};
/// let (peer_id, addr) = parse_str_addr(
/// 	"/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV"
/// ).unwrap();
/// assert_eq!(peer_id, "QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".parse::<PeerId>().unwrap());
/// assert_eq!(addr, "/ip4/198.51.100.19/tcp/30333".parse::<Multiaddr>().unwrap());
/// ```
///
pub fn parse_str_addr(addr_str: &str) -> Result<(PeerId, Multiaddr), ParseErr> {
	let addr: Multiaddr = addr_str.parse()?;
	parse_addr(addr)
}

/// Splits a Multiaddress into a Multiaddress and PeerId.
pub fn parse_addr(mut addr: Multiaddr)-> Result<(PeerId, Multiaddr), ParseErr> {
	let who = match addr.pop() {
		Some(multiaddr::Protocol::P2p(key)) => PeerId::from_multihash(key)
			.map_err(|_| ParseErr::InvalidPeerId)?,
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
/// # use sc_network::{Multiaddr, PeerId, config::MultiaddrWithPeerId};
/// let addr: MultiaddrWithPeerId =
/// 	"/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".parse().unwrap();
/// assert_eq!(addr.peer_id.to_base58(), "QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV");
/// assert_eq!(addr.multiaddr.to_string(), "/ip4/198.51.100.19/tcp/30333");
/// ```
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
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
		let proto = multiaddr::Protocol::P2p(From::from(self.peer_id.clone()));
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
		Ok(MultiaddrWithPeerId {
			peer_id,
			multiaddr,
		})
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
	/// List of notifications protocols that the node supports. Must also include a
	/// `ConsensusEngineId` for backwards-compatibility.
	pub notifications_protocols: Vec<(ConsensusEngineId, Cow<'static, str>)>,
	/// List of request-response protocols that the node supports.
	pub request_response_protocols: Vec<RequestResponseConfig>,
	/// Maximum allowed number of incoming connections.
	pub in_peers: u32,
	/// Number of outgoing connections we're trying to maintain.
	pub out_peers: u32,
	/// List of reserved node addresses.
	pub reserved_nodes: Vec<MultiaddrWithPeerId>,
	/// The non-reserved peer mode.
	pub non_reserved_mode: NonReservedPeerMode,
	/// Client identifier. Sent over the wire for debugging purposes.
	pub client_version: String,
	/// Name of the node. Sent over the wire for debugging purposes.
	pub node_name: String,
	/// Configuration for the transport layer.
	pub transport: TransportConfig,
	/// Maximum number of peers to ask the same blocks in parallel.
	pub max_parallel_downloads: u32,
	/// Should we insert non-global addresses into the DHT?
	pub allow_non_globals_in_dht: bool,
}

impl NetworkConfiguration {
	/// Create new default configuration
	pub fn new<SN: Into<String>, SV: Into<String>>(
		node_name: SN,
		client_version: SV,
		node_key: NodeKeyConfig,
		net_config_path: Option<PathBuf>,
	) -> Self {
		NetworkConfiguration {
			net_config_path,
			listen_addresses: Vec::new(),
			public_addresses: Vec::new(),
			boot_nodes: Vec::new(),
			node_key,
			notifications_protocols: Vec::new(),
			request_response_protocols: Vec::new(),
			in_peers: 25,
			out_peers: 75,
			reserved_nodes: Vec::new(),
			non_reserved_mode: NonReservedPeerMode::Accept,
			client_version: client_version.into(),
			node_name: node_name.into(),
			transport: TransportConfig::Normal {
				enable_mdns: false,
				allow_private_ipv4: true,
				wasm_external_transport: None,
			},
			max_parallel_downloads: 5,
			allow_non_globals_in_dht: false,
		}
	}

	/// Create new default configuration for localhost-only connection with random port (useful for testing)
	pub fn new_local() -> NetworkConfiguration {
		let mut config = NetworkConfiguration::new(
			"test-node",
			"test-client",
			Default::default(),
			None,
		);

		config.listen_addresses = vec![
			iter::once(multiaddr::Protocol::Ip4(Ipv4Addr::new(127, 0, 0, 1)))
				.chain(iter::once(multiaddr::Protocol::Tcp(0)))
				.collect()
		];

		config.allow_non_globals_in_dht = true;
		config
	}

	/// Create new default configuration for localhost-only connection with random port (useful for testing)
	pub fn new_memory() -> NetworkConfiguration {
		let mut config = NetworkConfiguration::new(
			"test-node",
			"test-client",
			Default::default(),
			None,
		);

		config.listen_addresses = vec![
			iter::once(multiaddr::Protocol::Ip4(Ipv4Addr::new(127, 0, 0, 1)))
				.chain(iter::once(multiaddr::Protocol::Tcp(0)))
				.collect()
		];

		config.allow_non_globals_in_dht = true;
		config
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

		/// If true, allow connecting to private IPv4 addresses (as defined in
		/// [RFC1918](https://tools.ietf.org/html/rfc1918)). Irrelevant for addresses that have
		/// been passed in [`NetworkConfiguration::reserved_nodes`] or
		/// [`NetworkConfiguration::boot_nodes`].
		allow_private_ipv4: bool,

		/// Optional external implementation of a libp2p transport. Used in WASM contexts where we
		/// need some binding between the networking provided by the operating system or environment
		/// and libp2p.
		///
		/// This parameter exists whatever the target platform is, but it is expected to be set to
		/// `Some` only when compiling for WASM.
		wasm_external_transport: Option<wasm_ext::ExtTransport>,
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
			"accept" => Some(NonReservedPeerMode::Accept),
			"deny" => Some(NonReservedPeerMode::Deny),
			_ => None,
		}
	}
}

/// The configuration of a node's secret key, describing the type of key
/// and how it is obtained. A node's identity keypair is the result of
/// the evaluation of the node key configuration.
#[derive(Clone, Debug)]
pub enum NodeKeyConfig {
	/// A Ed25519 secret key configuration.
	Ed25519(Secret<ed25519::SecretKey>)
}

impl Default for NodeKeyConfig {
	fn default() -> NodeKeyConfig {
		NodeKeyConfig::Ed25519(Secret::New)
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
	New
}

impl<K> fmt::Debug for Secret<K> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Secret::Input(_) => f.debug_tuple("Secret::Input").finish(),
			Secret::File(path) => f.debug_tuple("Secret::File").field(path).finish(),
			Secret::New => f.debug_tuple("Secret::New").finish(),
		}
	}
}

impl NodeKeyConfig {
	/// Evaluate a `NodeKeyConfig` to obtain an identity `Keypair`:
	///
	///  * If the secret is configured as input, the corresponding keypair is returned.
	///
	///  * If the secret is configured as a file, it is read from that file, if it exists.
	///    Otherwise a new secret is generated and stored. In either case, the
	///    keypair obtained from the secret is returned.
	///
	///  * If the secret is configured to be new, it is generated and the corresponding
	///    keypair is returned.
	pub fn into_keypair(self) -> io::Result<Keypair> {
		use NodeKeyConfig::*;
		match self {
			Ed25519(Secret::New) =>
				Ok(Keypair::generate_ed25519()),

			Ed25519(Secret::Input(k)) =>
				Ok(Keypair::Ed25519(k.into())),

			Ed25519(Secret::File(f)) =>
				get_secret(
					f,
					|mut b| {
						match String::from_utf8(b.to_vec())
							.ok()
							.and_then(|s|{
								if s.len() == 64 {
									hex::decode(&s).ok()
								} else {
									None
								}}
							)
						{
							Some(s) => ed25519::SecretKey::from_bytes(s),
							_ => ed25519::SecretKey::from_bytes(&mut b),
						}
					},
					ed25519::SecretKey::generate,
					|b| b.as_ref().to_vec()
				)
				.map(ed25519::Keypair::from)
				.map(Keypair::Ed25519),
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
		.and_then(|mut sk_bytes|
			parse(&mut sk_bytes)
				.map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e)))
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
	P: AsRef<Path>
{
	let mut file = open_secret_file(&path)?;
	file.write_all(sk_bytes)
}

/// Opens a file containing a secret key in write mode.
#[cfg(unix)]
fn open_secret_file<P>(path: P) -> io::Result<fs::File>
where
	P: AsRef<Path>
{
	use std::os::unix::fs::OpenOptionsExt;
	fs::OpenOptions::new()
		.write(true)
		.create_new(true)
		.mode(0o600)
		.open(path)
}

/// Opens a file containing a secret key in write mode.
#[cfg(not(unix))]
fn open_secret_file<P>(path: P) -> Result<fs::File, io::Error>
where
	P: AsRef<Path>
{
	fs::OpenOptions::new()
		.write(true)
		.create_new(true)
		.open(path)
}

#[cfg(test)]
mod tests {
	use super::*;
	use tempfile::TempDir;

	fn tempdir_with_prefix(prefix: &str) -> TempDir {
		tempfile::Builder::new().prefix(prefix).tempdir().unwrap()
	}

	fn secret_bytes(kp: &Keypair) -> Vec<u8> {
		match kp {
			Keypair::Ed25519(p) => p.secret().as_ref().iter().cloned().collect(),
			Keypair::Secp256k1(p) => p.secret().to_bytes().to_vec(),
			_ => panic!("Unexpected keypair.")
		}
	}

	#[test]
	fn test_secret_file() {
		let tmp = tempdir_with_prefix("x");
		std::fs::remove_dir(tmp.path()).unwrap(); // should be recreated
		let file = tmp.path().join("x").to_path_buf();
		let kp1 = NodeKeyConfig::Ed25519(Secret::File(file.clone())).into_keypair().unwrap();
		let kp2 = NodeKeyConfig::Ed25519(Secret::File(file.clone())).into_keypair().unwrap();
		assert!(file.is_file() && secret_bytes(&kp1) == secret_bytes(&kp2))
	}

	#[test]
	fn test_secret_input() {
		let sk = ed25519::SecretKey::generate();
		let kp1 = NodeKeyConfig::Ed25519(Secret::Input(sk.clone())).into_keypair().unwrap();
		let kp2 = NodeKeyConfig::Ed25519(Secret::Input(sk)).into_keypair().unwrap();
		assert!(secret_bytes(&kp1) == secret_bytes(&kp2));
	}

	#[test]
	fn test_secret_new() {
		let kp1 = NodeKeyConfig::Ed25519(Secret::New).into_keypair().unwrap();
		let kp2 = NodeKeyConfig::Ed25519(Secret::New).into_keypair().unwrap();
		assert!(secret_bytes(&kp1) != secret_bytes(&kp2));
	}
}
