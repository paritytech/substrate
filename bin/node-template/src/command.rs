// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use sp_consensus_aura::sr25519::{AuthorityPair as AuraPair};
use sc_cli::{VersionInfo, error};
use crate::service;
use crate::chain_spec;
use crate::cli::Cli;

/// Parse and run command line arguments
pub fn run(version: VersionInfo) -> error::Result<()>
{
	let opt = sc_cli::from_args::<Cli>(&version);

	let mut config = sc_service::Configuration::default();
	config.impl_name = "node-template";

	match opt.subcommand {
		Some(subcommand) => sc_cli::run_subcommand(
			config,
			subcommand,
			chain_spec::load_spec,
			|config: _| Ok(new_full_start!(config).0),
			&version,
		),
		None => sc_cli::run(
			config,
			opt.run,
			service::new_light,
			service::new_full,
			chain_spec::load_spec,
			&version,
		)
	}
}
