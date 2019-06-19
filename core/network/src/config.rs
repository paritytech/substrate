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

//! Configuration for the networking layer of Substrate.

pub use crate::protocol::ProtocolConfig;

use crate::ProtocolId;
use crate::chain::{Client, FinalityProofProvider};
use crate::on_demand_layer::OnDemand;
use crate::service::{ExHashT, TransactionPool};
use bitflags::bitflags;
use consensus::import_queue::ImportQueue;
use parity_codec;
use runtime_primitives::traits::{Block as BlockT};
use std::sync::Arc;
use libp2p::identity::{Keypair, secp256k1, ed25519};
use libp2p::wasm_ext;
use libp2p::{Multiaddr, multiaddr::Protocol};
use std::error::Error;
use std::{io::{self, Write}, iter, fs, net::Ipv4Addr, path::{Path, PathBuf}};
use zeroize::Zeroize;

/// Service initialization parameters.
pub struct Params<B: BlockT, S, H: ExHashT> {
	/// Assigned roles for our node.
	pub roles: Roles,
	/// Network layer configuration.
	pub network_config: NetworkConfiguration,
	/// Substrate relay chain access point.
	pub chain: Arc<dyn Client<B>>,
	/// Finality proof provider.
	pub finality_proof_provider: Option<Arc<dyn FinalityProofProvider<B>>>,
	/// On-demand service reference.
	pub on_demand: Option<Arc<OnDemand<B>>>,
	/// Transaction pool.
	pub transaction_pool: Arc<dyn TransactionPool<H, B>>,
	/// Name of the protocol to use on the wire. Should be different for each chain.
	pub protocol_id: ProtocolId,
	/// Import queue to use.
	pub import_queue: Box<dyn ImportQueue<B>>,
	/// Protocol specialization.
	pub specialization: S,
}

bitflags! {
	/// Bitmask of the roles that a node fulfills.
	pub struct Roles: u8 {
		/// No network.
		const NONE = 0b00000000;
		/// Full node, does not participate in consensus.
		const FULL = 0b00000001;
		/// Light client node.
		const LIGHT = 0b00000010;
		/// Act as an authority
		const AUTHORITY = 0b00000100;
	}
}

impl Roles {
	/// Does this role represents a client that holds full chain data locally?
	pub fn is_full(&self) -> bool {
		self.intersects(Roles::FULL | Roles::AUTHORITY)
	}

	/// Does this role represents a client that does not hold full chain data locally?
	pub fn is_light(&self) -> bool {
		!self.is_full()
	}
}

impl parity_codec::Encode for Roles {
	fn encode_to<T: parity_codec::Output>(&self, dest: &mut T) {
		dest.push_byte(self.bits())
	}
}

impl parity_codec::Decode for Roles {
	fn decode<I: parity_codec::Input>(input: &mut I) -> Option<Self> {
		Self::from_bits(input.read_byte()?)
	}
}

/// Network service configuration.
#[derive(Clone)]
pub struct NetworkConfiguration {
	/// Directory path to store general network configuration. None means nothing will be saved.
	pub config_path: Option<String>,
	/// Directory path to store network-specific configuration. None means nothing will be saved.
	pub net_config_path: Option<String>,
	/// Multiaddresses to listen for incoming connections.
	pub listen_addresses: Vec<Multiaddr>,
	/// Multiaddresses to advertise. Detected automatically if empty.
	pub public_addresses: Vec<Multiaddr>,
	/// List of initial node addresses
	pub boot_nodes: Vec<String>,
	/// The node key configuration, which determines the node's network identity keypair.
	pub node_key: NodeKeyConfig,
	/// Maximum allowed number of incoming connections.
	pub in_peers: u32,
	/// Number of outgoing connections we're trying to maintain.
	pub out_peers: u32,
	/// List of reserved node addresses.
	pub reserved_nodes: Vec<String>,
	/// The non-reserved peer mode.
	pub non_reserved_mode: NonReservedPeerMode,
	/// Client identifier. Sent over the wire for debugging purposes.
	pub client_version: String,
	/// Name of the node. Sent over the wire for debugging purposes.
	pub node_name: String,
	/// If true, the network will use mDNS to discover other libp2p nodes on the local network
	/// and connect to them if they support the same chain.
	pub enable_mdns: bool,
	/// Optional external implementation of a libp2p transport. Used in WASM contexts where we need
	/// some binding between the networking provided by the operating system or environment and
	/// libp2p.
	///
	/// This parameter exists whatever the target platform is, but it is expected to be set to
	/// `Some` only when compiling for WASM.
	pub wasm_external_transport: Option<wasm_ext::ExtTransport>,
}

impl Default for NetworkConfiguration {
	fn default() -> Self {
		NetworkConfiguration {
			config_path: None,
			net_config_path: None,
			listen_addresses: Vec::new(),
			public_addresses: Vec::new(),
			boot_nodes: Vec::new(),
			node_key: NodeKeyConfig::Ed25519(Secret::New),
			in_peers: 25,
			out_peers: 75,
			reserved_nodes: Vec::new(),
			non_reserved_mode: NonReservedPeerMode::Accept,
			client_version: "unknown".into(),
			node_name: "unknown".into(),
			enable_mdns: false,
			wasm_external_transport: None,
		}
	}
}

impl NetworkConfiguration {
	/// Create a new instance of default settings.
	pub fn new() -> Self {
		Self::default()
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
#[derive(Clone)]
pub enum NodeKeyConfig {
	/// A Secp256k1 secret key configuration.
	Secp256k1(Secret<secp256k1::SecretKey>),
	/// A Ed25519 secret key configuration.
	Ed25519(Secret<ed25519::SecretKey>)
}

/// The options for obtaining a Secp256k1 secret key.
pub type Secp256k1Secret = Secret<secp256k1::SecretKey>;

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
	///   * `secp256k1::SecretKey`: An unencoded 32 bytes Secp256k1 secret key.
	///   * `ed25519::SecretKey`: An unencoded 32 bytes Ed25519 secret key.
	File(PathBuf),
	/// Always generate a new secret key `K`.
	New
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
			Secp256k1(Secret::New) =>
				Ok(Keypair::generate_secp256k1()),

			Secp256k1(Secret::Input(k)) =>
				Ok(Keypair::Secp256k1(k.into())),

			Secp256k1(Secret::File(f)) =>
				get_secret(f,
					|mut b| secp256k1::SecretKey::from_bytes(&mut b),
					secp256k1::SecretKey::generate,
					|b| b.to_bytes().to_vec())
				.map(secp256k1::Keypair::from)
				.map(Keypair::Secp256k1),

			Ed25519(Secret::New) =>
				Ok(Keypair::generate_ed25519()),

			Ed25519(Secret::Input(k)) =>
				Ok(Keypair::Ed25519(k.into())),

			Ed25519(Secret::File(f)) =>
				get_secret(f,
					|mut b| ed25519::SecretKey::from_bytes(&mut b),
					ed25519::SecretKey::generate,
					|b| b.as_ref().to_vec())
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
	use tempdir::TempDir;

	fn secret_bytes(kp: &Keypair) -> Vec<u8> {
		match kp {
			Keypair::Ed25519(p) => p.secret().as_ref().iter().cloned().collect(),
			Keypair::Secp256k1(p) => p.secret().to_bytes().to_vec(),
			_ => panic!("Unexpected keypair.")
		}
	}

	#[test]
	fn test_secret_file() {
		let tmp = TempDir::new("x").unwrap();
		std::fs::remove_dir(tmp.path()).unwrap(); // should be recreated
		let file = tmp.path().join("x").to_path_buf();
		let kp1 = NodeKeyConfig::Ed25519(Secret::File(file.clone())).into_keypair().unwrap();
		let kp2 = NodeKeyConfig::Ed25519(Secret::File(file.clone())).into_keypair().unwrap();
		assert!(file.is_file() && secret_bytes(&kp1) == secret_bytes(&kp2))
	}

	#[test]
	fn test_secret_input() {
		let sk = secp256k1::SecretKey::generate();
		let kp1 = NodeKeyConfig::Secp256k1(Secret::Input(sk.clone())).into_keypair().unwrap();
		let kp2 = NodeKeyConfig::Secp256k1(Secret::Input(sk)).into_keypair().unwrap();
		assert!(secret_bytes(&kp1) == secret_bytes(&kp2));
	}

	#[test]
	fn test_secret_new() {
		let kp1 = NodeKeyConfig::Ed25519(Secret::New).into_keypair().unwrap();
		let kp2 = NodeKeyConfig::Ed25519(Secret::New).into_keypair().unwrap();
		assert!(secret_bytes(&kp1) != secret_bytes(&kp2));
	}
}
