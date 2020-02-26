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

use structopt::StructOpt;
use log::info;
use sc_network::config::build_multiaddr;
use sc_service::{Configuration, ChainSpecExtension, RuntimeGenesis, ChainSpec};

use crate::error;
use crate::VersionInfo;
use crate::params::SharedParams;
use crate::params::NodeKeyParams;

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
	pub fn run<G, E>(
		self,
		config: Configuration<G, E>,
	) -> error::Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		info!("Building chain spec");
		let mut spec = config.expect_chain_spec().clone();
		let raw_output = self.raw;

		if spec.boot_nodes().is_empty() && !self.disable_default_bootnode {
			let keys = config.network.node_key.into_keypair()?;
			let peer_id = keys.public().into_peer_id();
			let addr = build_multiaddr![
				Ip4([127, 0, 0, 1]),
				Tcp(30333u16),
				P2p(peer_id)
			];
			spec.add_boot_node(addr)
		}

		let json = sc_service::chain_ops::build_spec(spec, raw_output)?;

		print!("{}", json);

		Ok(())
	}

	/// Update and prepare a `Configuration` with command line parameters
	pub fn update_config<G, E, F>(
		&self,
		mut config: &mut Configuration<G, E>,
		spec_factory: F,
		version: &VersionInfo,
	) -> error::Result<()> where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		F: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
	{
		self.shared_params.update_config(&mut config, spec_factory, version)?;

		let net_config_path = config
			.in_chain_config_dir(crate::commands::DEFAULT_NETWORK_CONFIG_PATH)
			.expect("We provided a base_path");

		self.node_key_params.update_config(&mut config, Some(&net_config_path))?;

		Ok(())
	}
}

