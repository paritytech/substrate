// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

use crate::{arg_enums::SyncMode, params::node_key_params::NodeKeyParams};
use sc_network::{
	config::{
		NetworkConfiguration, NodeKeyConfig, NonReservedPeerMode, SetConfig, TransportConfig,
	},
	multiaddr::Protocol,
};
use sc_service::{
	config::{Multiaddr, MultiaddrWithPeerId},
	ChainSpec, ChainType,
};
use std::{borrow::Cow, path::PathBuf};
use structopt::StructOpt;

/// Parameters used to create the network configuration.
#[derive(Debug, StructOpt, Clone)]
pub struct NetworkParams {
	/// Specify a list of bootnodes.
	#[structopt(long = "bootnodes", value_name = "ADDR")]
	pub bootnodes: Vec<MultiaddrWithPeerId>,

	/// Specify a list of reserved node addresses.
	#[structopt(long = "reserved-nodes", value_name = "ADDR")]
	pub reserved_nodes: Vec<MultiaddrWithPeerId>,

	/// Whether to only synchronize the chain with reserved nodes.
	///
	/// Also disables automatic peer discovery.
	///
	/// TCP connections might still be established with non-reserved nodes.
	/// In particular, if you are a validator your node might still connect to other
	/// validator nodes and collator nodes regardless of whether they are defined as
	/// reserved nodes.
	#[structopt(long = "reserved-only")]
	pub reserved_only: bool,

	/// The public address that other nodes will use to connect to it.
	/// This can be used if there's a proxy in front of this node.
	#[structopt(long, value_name = "PUBLIC_ADDR")]
	pub public_addr: Vec<Multiaddr>,

	/// Listen on this multiaddress.
	///
	/// By default:
	/// If `--validator` is passed: `/ip4/0.0.0.0/tcp/<port>` and `/ip6/[::]/tcp/<port>`.
	/// Otherwise: `/ip4/0.0.0.0/tcp/<port>/ws` and `/ip6/[::]/tcp/<port>/ws`.
	#[structopt(long = "listen-addr", value_name = "LISTEN_ADDR")]
	pub listen_addr: Vec<Multiaddr>,

	/// Specify p2p protocol TCP port.
	#[structopt(long = "port", value_name = "PORT", conflicts_with_all = &[ "listen-addr" ])]
	pub port: Option<u16>,

	/// Always forbid connecting to private IPv4 addresses (as specified in
	/// [RFC1918](https://tools.ietf.org/html/rfc1918)), unless the address was passed with
	/// `--reserved-nodes` or `--bootnodes`. Enabled by default for chains marked as "live" in
	/// their chain specifications.
	#[structopt(long = "no-private-ipv4", conflicts_with_all = &["allow-private-ipv4"])]
	pub no_private_ipv4: bool,

	/// Always accept connecting to private IPv4 addresses (as specified in
	/// [RFC1918](https://tools.ietf.org/html/rfc1918)). Enabled by default for chains marked as
	/// "local" in their chain specifications, or when `--dev` is passed.
	#[structopt(long = "allow-private-ipv4", conflicts_with_all = &["no-private-ipv4"])]
	pub allow_private_ipv4: bool,

	/// Specify the number of outgoing connections we're trying to maintain.
	#[structopt(long = "out-peers", value_name = "COUNT", default_value = "25")]
	pub out_peers: u32,

	/// Specify the maximum number of incoming connections we're accepting.
	#[structopt(long = "in-peers", value_name = "COUNT", default_value = "25")]
	pub in_peers: u32,

	/// Disable mDNS discovery.
	///
	/// By default, the network will use mDNS to discover other nodes on the
	/// local network. This disables it. Automatically implied when using --dev.
	#[structopt(long = "no-mdns")]
	pub no_mdns: bool,

	/// Maximum number of peers from which to ask for the same blocks in parallel.
	///
	/// This allows downloading announced blocks from multiple peers. Decrease to save
	/// traffic and risk increased latency.
	#[structopt(long = "max-parallel-downloads", value_name = "COUNT", default_value = "5")]
	pub max_parallel_downloads: u32,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub node_key_params: NodeKeyParams,

	/// Enable peer discovery on local networks.
	///
	/// By default this option is `true` for `--dev` or when the chain type is `Local`/`Development`
	/// and false otherwise.
	#[structopt(long)]
	pub discover_local: bool,

	/// Require iterative Kademlia DHT queries to use disjoint paths for increased resiliency in the
	/// presence of potentially adversarial nodes.
	///
	/// See the S/Kademlia paper for more information on the high level design as well as its
	/// security improvements.
	#[structopt(long)]
	pub kademlia_disjoint_query_paths: bool,

	/// Join the IPFS network and serve transactions over bitswap protocol.
	#[structopt(long)]
	pub ipfs_server: bool,

	/// Blockchain syncing mode.
	///
	/// - `Full`: Download and validate full blockchain history.
	///
	/// - `Fast`: Download blocks and the latest state only.
	///
	/// - `FastUnsafe`: Same as `Fast`, but skip downloading state proofs.
	#[structopt(long, value_name = "SYNC_MODE", default_value = "Full")]
	pub sync: SyncMode,
}

impl NetworkParams {
	/// Fill the given `NetworkConfiguration` by looking at the cli parameters.
	pub fn network_config(
		&self,
		chain_spec: &Box<dyn ChainSpec>,
		is_dev: bool,
		is_validator: bool,
		net_config_path: Option<PathBuf>,
		client_id: &str,
		node_name: &str,
		node_key: NodeKeyConfig,
		default_listen_port: u16,
	) -> NetworkConfiguration {
		let port = self.port.unwrap_or(default_listen_port);

		let listen_addresses = if self.listen_addr.is_empty() {
			if is_validator {
				vec![
					Multiaddr::empty()
						.with(Protocol::Ip6([0, 0, 0, 0, 0, 0, 0, 0].into()))
						.with(Protocol::Tcp(port)),
					Multiaddr::empty()
						.with(Protocol::Ip4([0, 0, 0, 0].into()))
						.with(Protocol::Tcp(port)),
				]
			} else {
				vec![
					Multiaddr::empty()
						.with(Protocol::Ip6([0, 0, 0, 0, 0, 0, 0, 0].into()))
						.with(Protocol::Tcp(port))
						.with(Protocol::Ws(Cow::Borrowed("/"))),
					Multiaddr::empty()
						.with(Protocol::Ip4([0, 0, 0, 0].into()))
						.with(Protocol::Tcp(port))
						.with(Protocol::Ws(Cow::Borrowed("/"))),
				]
			}
		} else {
			self.listen_addr.clone()
		};

		let public_addresses = self.public_addr.clone();

		let mut boot_nodes = chain_spec.boot_nodes().to_vec();
		boot_nodes.extend(self.bootnodes.clone());

		let chain_type = chain_spec.chain_type();
		// Activate if the user explicitly requested local discovery, `--dev` is given or the
		// chain type is `Local`/`Development`
		let allow_non_globals_in_dht =
			self.discover_local ||
				is_dev || matches!(chain_type, ChainType::Local | ChainType::Development);

		let allow_private_ipv4 = match (self.allow_private_ipv4, self.no_private_ipv4) {
			(true, true) => unreachable!("`*_private_ipv4` flags are mutually exclusive; qed"),
			(true, false) => true,
			(false, true) => false,
			(false, false) =>
				is_dev || matches!(chain_type, ChainType::Local | ChainType::Development),
		};

		NetworkConfiguration {
			boot_nodes,
			net_config_path,
			default_peers_set: SetConfig {
				in_peers: self.in_peers,
				out_peers: self.out_peers,
				reserved_nodes: self.reserved_nodes.clone(),
				non_reserved_mode: if self.reserved_only {
					NonReservedPeerMode::Deny
				} else {
					NonReservedPeerMode::Accept
				},
			},
			listen_addresses,
			public_addresses,
			extra_sets: Vec::new(),
			request_response_protocols: Vec::new(),
			node_key,
			node_name: node_name.to_string(),
			client_version: client_id.to_string(),
			transport: TransportConfig::Normal {
				enable_mdns: !is_dev && !self.no_mdns,
				allow_private_ipv4,
				wasm_external_transport: None,
			},
			max_parallel_downloads: self.max_parallel_downloads,
			enable_dht_random_walk: !self.reserved_only,
			allow_non_globals_in_dht,
			kademlia_disjoint_query_paths: self.kademlia_disjoint_query_paths,
			yamux_window_size: None,
			ipfs_server: self.ipfs_server,
			sync_mode: self.sync.into(),
		}
	}
}
