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

// External dependencies
pub use libp2p::{build_multiaddr, core::PublicKey, identity, multiaddr, Multiaddr};

// Substrate dependencies
use prometheus_endpoint::Registry;
pub use sc_network_common::{
	config::{
		MultiaddrWithPeerId, NodeKeyConfig, NonReservedPeerMode, NotificationHandshake, ProtocolId,
		SyncMode, TransportConfig,
	},
	protocol::{role::Role, ProtocolName},
	request_responses::{
		IncomingRequest, OutgoingResponse, ProtocolConfig as RequestResponseConfig,
	},
	sync::warp::WarpSyncProvider,
	ExHashT,
};

// `std` dependencies
use std::{future::Future, iter, net::Ipv4Addr, path::PathBuf, pin::Pin, sync::Arc};

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

/// Network initialization parameters.
pub struct Params<Client> {
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

	/// Registry for recording prometheus metrics to.
	pub metrics_registry: Option<Registry>,

	/// Block announce protocol configuration
	pub block_announce_config: NonDefaultSetConfig,

	/// Request response protocol configurations
	pub request_response_protocol_configs: Vec<RequestResponseConfig>,
}
