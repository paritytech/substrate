// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

use crate::error;
use crate::params::NodeKeyParams;
use crate::params::SharedParams;
use crate::CliConfiguration;
use log::info;
use sc_network::config::build_multiaddr;
use sc_service::{config::{MultiaddrWithPeerId, NetworkConfiguration}, ChainSpec};
use structopt::StructOpt;
use std::io::Write;

/// The `build-spec` command used to build a specification.
#[derive(Debug, StructOpt)]
pub struct BuildSpecCmd {
	/// Force raw genesis storage output.
	#[structopt(long = "raw")]
	pub raw: bool,

	/// Disable adding the default bootnode to the specification.
	///
	/// By default the `/ip4/127.0.0.1/tcp/30333/p2p/NODE_PEER_ID` bootnode is added to the
	/// specification when no bootnode exists.
	#[structopt(long = "disable-default-bootnode")]
	pub disable_default_bootnode: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub node_key_params: NodeKeyParams,
}

impl BuildSpecCmd {
	/// Run the build-spec command
	pub fn run(
		&self,
		mut spec: Box<dyn ChainSpec>,
		network_config: NetworkConfiguration,
	) -> error::Result<()> {
		info!("Building chain spec");
		let raw_output = self.raw;

		if spec.boot_nodes().is_empty() && !self.disable_default_bootnode {
			let keys = network_config.node_key.into_keypair()?;
			let peer_id = keys.public().into_peer_id();
			let addr = MultiaddrWithPeerId {
				multiaddr: build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(30333u16)],
				peer_id,
			};
			spec.add_boot_node(addr)
		}

		let json = sc_service::chain_ops::build_spec(&*spec, raw_output)?;
		if std::io::stdout().write_all(json.as_bytes()).is_err() {
			let _ = std::io::stderr().write_all(b"Error writing to stdout\n");
		}
		Ok(())
	}
}

impl CliConfiguration for BuildSpecCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn node_key_params(&self) -> Option<&NodeKeyParams> {
		Some(&self.node_key_params)
	}
}
