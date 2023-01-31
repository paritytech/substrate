// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

pub use sc_network_common::{
	config::ProtocolId,
	protocol::role::Role,
	request_responses::{
		IncomingRequest, OutgoingResponse, ProtocolConfig as RequestResponseConfig,
	},
	sync::warp::WarpSyncProvider,
	ExHashT,
};

pub use libp2p::{build_multiaddr, core::PublicKey, identity};

use crate::ChainSyncInterface;
use core::{fmt, iter};
use libp2p::{
	identity::{ed25519, Keypair},
	multiaddr, Multiaddr,
};
use prometheus_endpoint::Registry;
use sc_network_common::{
	config::{MultiaddrWithPeerId, NonDefaultSetConfig, SetConfig, TransportConfig},
	sync::ChainSync,
};
use sp_runtime::traits::Block as BlockT;
use std::{
	error::Error,
	fs,
	future::Future,
	io::{self, Write},
	net::Ipv4Addr,
	path::{Path, PathBuf},
	pin::Pin,
	sync::Arc,
};
use zeroize::Zeroize;

/// Network initialization parameters.
pub struct Params<B, Client>
where
	B: BlockT + 'static,
{
	/// Assigned role for our node (full, light, ...).
	pub role: Role,

	/// How to spawn background tasks.
	pub executor: Box<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>) + Send>,

	/// Network layer configuration.
	pub network_config: NetworkConfiguration,

	/// Client that contains the blockchain.
	pub chain: Arc<Client>,

	/// Legacy name of the protocol to use on the wire. Should be different for each chain.
	pub protocol_id: ProtocolId,

	/// Fork ID to distinguish protocols of different hard forks. Part of the standard protocol
	/// name on the wire.
	pub fork_id: Option<String>,

	/// Instance of chain sync implementation.
	pub chain_sync: Box<dyn ChainSync<B>>,

	/// Interface that can be used to delegate syncing-related function calls to `ChainSync`
	pub chain_sync_service: Box<dyn ChainSyncInterface<B>>,

	/// Registry for recording prometheus metrics to.
	pub metrics_registry: Option<Registry>,

	/// Block announce protocol configuration
	pub block_announce_config: NonDefaultSetConfig,

	/// Request response protocol configurations
	pub request_response_protocol_configs: Vec<RequestResponseConfig>,
}

/// Sync operation mode.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SyncMode {
	/// Full block download and verification.
	Full,
	/// Download blocks and the latest state.
	Fast {
		/// Skip state proof download and verification.
		skip_proofs: bool,
		/// Download indexed transactions for recent blocks.
		storage_chain_mode: bool,
	},
	/// Warp sync - verify authority set transitions and the latest state.
	Warp,
}

impl SyncMode {
	/// Returns if `self` is [`Self::Warp`].
	pub fn is_warp(&self) -> bool {
		matches!(self, Self::Warp)
	}

	/// Returns if `self` is [`Self::Fast`].
	pub fn is_fast(&self) -> bool {
		matches!(self, Self::Fast { .. })
	}
}

impl Default for SyncMode {
	fn default() -> Self {
		Self::Full
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
	/// List of request-response protocols that the node supports.
	pub request_response_protocols: Vec<RequestResponseConfig>,
	/// Configuration for the default set of nodes used for block syncing and transactions.
	pub default_peers_set: SetConfig,
	/// Number of substreams to reserve for full nodes for block syncing and transactions.
	/// Any other slot will be dedicated to light nodes.
	///
	/// This value is implicitly capped to `default_set.out_peers + default_set.in_peers`.
	pub default_peers_set_num_full: u32,
	/// Configuration for extra sets of nodes.
	pub extra_sets: Vec<NonDefaultSetConfig>,
	/// Client identifier. Sent over the wire for debugging purposes.
	pub client_version: String,
	/// Name of the node. Sent over the wire for debugging purposes.
	pub node_name: String,
	/// Configuration for the transport layer.
	pub transport: TransportConfig,
	/// Maximum number of peers to ask the same blocks in parallel.
	pub max_parallel_downloads: u32,
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
			request_response_protocols: Vec::new(),
			default_peers_set_num_full: default_peers_set.in_peers + default_peers_set.out_peers,
			default_peers_set,
			extra_sets: Vec::new(),
			client_version: client_version.into(),
			node_name: node_name.into(),
			transport: TransportConfig::Normal { enable_mdns: false, allow_private_ip: true },
			max_parallel_downloads: 5,
			sync_mode: SyncMode::Full,
			enable_dht_random_walk: true,
			allow_non_globals_in_dht: false,
			kademlia_disjoint_query_paths: false,
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

			Ed25519(Secret::Input(k)) => Ok(Keypair::Ed25519(k.into())),

			Ed25519(Secret::File(f)) => get_secret(
				f,
				|mut b| match String::from_utf8(b.to_vec()).ok().and_then(|s| {
					if s.len() == 64 {
						array_bytes::hex2bytes(&s).ok()
					} else {
						None
					}
				}) {
					Some(s) => ed25519::SecretKey::from_bytes(s),
					_ => ed25519::SecretKey::from_bytes(&mut b),
				},
				ed25519::SecretKey::generate,
				|b| b.as_ref().to_vec(),
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

#[cfg(test)]
mod tests {
	use super::*;
	use tempfile::TempDir;

	fn tempdir_with_prefix(prefix: &str) -> TempDir {
		tempfile::Builder::new().prefix(prefix).tempdir().unwrap()
	}

	fn secret_bytes(kp: &Keypair) -> Vec<u8> {
		let Keypair::Ed25519(p) = kp;
		p.secret().as_ref().iter().cloned().collect()
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
