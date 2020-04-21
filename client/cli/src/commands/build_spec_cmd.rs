// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use crate::error;
use crate::params::NodeKeyParams;
use crate::params::SharedParams;
use crate::CliConfiguration;
use log::info;
use sc_network::config::build_multiaddr;
use sc_service::{config::MultiaddrWithPeerId, Configuration};
use structopt::StructOpt;

/// The `build-spec` command used to build a specification.
#[derive(Debug, StructOpt, Clone)]
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
	pub fn run(&self, config: Configuration) -> error::Result<()> {
		info!("Building chain spec");
		let mut spec = config.chain_spec;
		let raw_output = self.raw;

		if spec.boot_nodes().is_empty() && !self.disable_default_bootnode {
			let keys = config.network.node_key.into_keypair()?;
			let peer_id = keys.public().into_peer_id();
			let addr = MultiaddrWithPeerId {
				multiaddr: build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(30333u16)],
				peer_id,
			};
			spec.add_boot_node(addr)
		}

		let json = sc_service::chain_ops::build_spec(&*spec, raw_output)?;

		print!("{}", json);

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
