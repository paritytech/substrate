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

use crate::{arg_enums::SyncMode, params::node_key_params::NodeKeyParams};
use clap::Args;
use sc_network::{
	config::{NetworkConfiguration, NodeKeyConfig},
	multiaddr::Protocol,
};
use sc_network_common::config::{NonReservedPeerMode, SetConfig, TransportConfig};
use sc_service::{
	config::{Multiaddr, MultiaddrWithPeerId},
	ChainSpec, ChainType,
};
use std::{borrow::Cow, path::PathBuf};

/// Parameters used to create the network configuration.
#[derive(Debug, Clone, Args)]
pub struct NetworkParams {
	/// Specify a list of bootnodes.
	#[arg(long, value_name = "ADDR", num_args = 1..)]
	pub bootnodes: Vec<MultiaddrWithPeerId>,

	/// Specify a list of reserved node addresses.
	#[arg(long, value_name = "ADDR", num_args = 1..)]
	pub reserved_nodes: Vec<MultiaddrWithPeerId>,

	/// Whether to only synchronize the chain with reserved nodes.
	///
	/// Also disables automatic peer discovery.
	///
	/// TCP connections might still be established with non-reserved nodes.
	/// In particular, if you are a validator your node might still connect to other
	/// validator nodes and collator nodes regardless of whether they are defined as
	/// reserved nodes.
	#[arg(long)]
	pub reserved_only: bool,

	/// The public address that other nodes will use to connect to it.
	/// This can be used if there's a proxy in front of this node.
	#[arg(long, value_name = "PUBLIC_ADDR", num_args = 1..)]
	pub public_addr: Vec<Multiaddr>,

	/// Listen on this multiaddress.
	///
	/// By default:
	/// If `--validator` is passed: `/ip4/0.0.0.0/tcp/<port>` and `/ip6/[::]/tcp/<port>`.
	/// Otherwise: `/ip4/0.0.0.0/tcp/<port>/ws` and `/ip6/[::]/tcp/<port>/ws`.
	#[arg(long, value_name = "LISTEN_ADDR", num_args = 1..)]
	pub listen_addr: Vec<Multiaddr>,

	/// Specify p2p protocol TCP port.
	#[arg(long, value_name = "PORT", conflicts_with_all = &[ "listen_addr" ])]
	pub port: Option<u16>,

	/// Always forbid connecting to private IPv4/IPv6 addresses (as specified in
	/// [RFC1918](https://tools.ietf.org/html/rfc1918)), unless the address was passed with
	/// `--reserved-nodes` or `--bootnodes`. Enabled by default for chains marked as "live" in
	/// their chain specifications.
	#[arg(long, alias = "no-private-ipv4", conflicts_with_all = &["allow_private_ip"])]
	pub no_private_ip: bool,

	/// Always accept connecting to private IPv4/IPv6 addresses (as specified in
	/// [RFC1918](https://tools.ietf.org/html/rfc1918)). Enabled by default for chains marked as
	/// "local" in their chain specifications, or when `--dev` is passed.
	#[arg(long, alias = "allow-private-ipv4", conflicts_with_all = &["no_private_ip"])]
	pub allow_private_ip: bool,

	/// Specify the number of outgoing connections we're trying to maintain.
	#[arg(long, value_name = "COUNT", default_value_t = 15)]
	pub out_peers: u32,

	/// Maximum number of inbound full nodes peers.
	#[arg(long, value_name = "COUNT", default_value_t = 25)]
	pub in_peers: u32,

	/// Maximum number of inbound light nodes peers.
	#[arg(long, value_name = "COUNT", default_value_t = 100)]
	pub in_peers_light: u32,

	/// Disable mDNS discovery.
	///
	/// By default, the network will use mDNS to discover other nodes on the
	/// local network. This disables it. Automatically implied when using --dev.
	#[arg(long)]
	pub no_mdns: bool,

	/// Maximum number of peers from which to ask for the same blocks in parallel.
	///
	/// This allows downloading announced blocks from multiple peers. Decrease to save
	/// traffic and risk increased latency.
	#[arg(long, value_name = "COUNT", default_value_t = 5)]
	pub max_parallel_downloads: u32,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub node_key_params: NodeKeyParams,

	/// Enable peer discovery on local networks.
	///
	/// By default this option is `true` for `--dev` or when the chain type is
	/// `Local`/`Development` and false otherwise.
	#[arg(long)]
	pub discover_local: bool,

	/// Require iterative Kademlia DHT queries to use disjoint paths for increased resiliency in
	/// the presence of potentially adversarial nodes.
	///
	/// See the S/Kademlia paper for more information on the high level design as well as its
	/// security improvements.
	#[arg(long)]
	pub kademlia_disjoint_query_paths: bool,

	/// Join the IPFS network and serve transactions over bitswap protocol.
	#[arg(long)]
	pub ipfs_server: bool,

	/// Blockchain syncing mode.
	///
	/// - `full`: Download and validate full blockchain history.
	/// - `fast`: Download blocks and the latest state only.
	/// - `fast-unsafe`: Same as `fast`, but skip downloading state proofs.
	/// - `warp`: Download the latest state and proof.
	#[arg(
		long,
		value_enum,
		value_name = "SYNC_MODE",
		default_value_t = SyncMode::Full,
		ignore_case = true,
		verbatim_doc_comment
	)]
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
			if is_validator || is_dev {
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

		let allow_private_ip = match (self.allow_private_ip, self.no_private_ip) {
			(true, true) => unreachable!("`*_private_ip` flags are mutually exclusive; qed"),
			(true, false) => true,
			(false, true) => false,
			(false, false) =>
				is_dev || matches!(chain_type, ChainType::Local | ChainType::Development),
		};

		NetworkConfiguration {
			boot_nodes,
			net_config_path,
			default_peers_set: SetConfig {
				in_peers: self.in_peers + self.in_peers_light,
				out_peers: self.out_peers,
				reserved_nodes: self.reserved_nodes.clone(),
				non_reserved_mode: if self.reserved_only {
					NonReservedPeerMode::Deny
				} else {
					NonReservedPeerMode::Accept
				},
			},
			default_peers_set_num_full: self.in_peers + self.out_peers,
			listen_addresses,
			public_addresses,
			extra_sets: Vec::new(),
			request_response_protocols: Vec::new(),
			node_key,
			node_name: node_name.to_string(),
			client_version: client_id.to_string(),
			transport: TransportConfig::Normal {
				enable_mdns: !is_dev && !self.no_mdns,
				allow_private_ip,
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

#[cfg(test)]
mod tests {
	use super::*;
	use clap::Parser;

	#[derive(Parser)]
	struct Cli {
		#[clap(flatten)]
		network_params: NetworkParams,
	}

	#[test]
	fn reserved_nodes_multiple_values_and_occurrences() {
		let params = Cli::try_parse_from([
			"",
			"--reserved-nodes",
			"/ip4/0.0.0.0/tcp/501/p2p/12D3KooWEBo1HUPQJwiBmM5kSeg4XgiVxEArArQdDarYEsGxMfbS",
			"/ip4/0.0.0.0/tcp/502/p2p/12D3KooWEBo1HUPQJwiBmM5kSeg4XgiVxEArArQdDarYEsGxMfbS",
			"--reserved-nodes",
			"/ip4/0.0.0.0/tcp/503/p2p/12D3KooWEBo1HUPQJwiBmM5kSeg4XgiVxEArArQdDarYEsGxMfbS",
		])
		.expect("Parses network params");

		let expected = vec![
			MultiaddrWithPeerId::try_from(
				"/ip4/0.0.0.0/tcp/501/p2p/12D3KooWEBo1HUPQJwiBmM5kSeg4XgiVxEArArQdDarYEsGxMfbS"
					.to_string(),
			)
			.unwrap(),
			MultiaddrWithPeerId::try_from(
				"/ip4/0.0.0.0/tcp/502/p2p/12D3KooWEBo1HUPQJwiBmM5kSeg4XgiVxEArArQdDarYEsGxMfbS"
					.to_string(),
			)
			.unwrap(),
			MultiaddrWithPeerId::try_from(
				"/ip4/0.0.0.0/tcp/503/p2p/12D3KooWEBo1HUPQJwiBmM5kSeg4XgiVxEArArQdDarYEsGxMfbS"
					.to_string(),
			)
			.unwrap(),
		];

		assert_eq!(expected, params.network_params.reserved_nodes);
	}

	#[test]
	fn sync_ingores_case() {
		let params = Cli::try_parse_from(["", "--sync", "wArP"]).expect("Parses network params");

		assert_eq!(SyncMode::Warp, params.network_params.sync);
	}
}
