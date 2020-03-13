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

use sc_cli::{SubstrateCLI, IntoConfiguration};
use sp_consensus_aura::sr25519::{AuthorityPair as AuraPair};
use crate::service;
use crate::chain_spec::Alternative;
use crate::cli::Cli;
use node_template_runtime::GenesisConfig;

impl SubstrateCLI<GenesisConfig, Option<()>> for Cli {
	fn spec_factory(id: &str) -> Result<Option<sc_service::ChainSpec<GenesisConfig, Option<()>>>, String> {
		Ok(match Alternative::from(id) {
			Some(spec) => Some(spec.load()?),
			None => None,
		})
	}

	fn get_impl_name() -> &'static str { "Substrate Node" }
	fn get_impl_version() -> &'static str { "1.0.todo" }
	fn get_support_url() -> &'static str { "support.anonymous.an" }
	fn get_executable_name() -> &'static str { "node-template" }
	fn get_author() -> &'static str { "Anonymous" }
	fn get_description() -> &'static str { "Template Node" }
	fn get_copyright_start_year() -> i32 { 2017 }
}

/*
	let version = sc_cli::VersionInfo {
		name: "Substrate Node",
		commit: env!("VERGEN_SHA_SHORT"),
		version: env!("CARGO_PKG_VERSION"),
		executable_name: "node-template",
		author: "Anonymous",
		description: "Template Node",
		support_url: "support.anonymous.an",
		copyright_start_year: 2017,
	};
*/

/// Parse and run command line arguments
pub fn run() -> sc_cli::Result<()> {
	let opt: Cli = Cli::from_args();

	match opt.subcommand {
		Some(subcommand) => {
			let runtime = Cli::create_runtime(&subcommand)?;
			runtime.run_subcommand(
				&subcommand,
				|config: _| Ok(new_full_start!(config).0),
			)
		},
		None => {
			let runtime = Cli::create_runtime(&opt.run)?;
			runtime.run_node(
				service::new_light,
				service::new_full,
			)
		},
	}
}
