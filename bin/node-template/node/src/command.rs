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

use crate::chain_spec::Alternative;
use crate::cli::Cli;
use crate::service;
use node_template_runtime::GenesisConfig;
use sc_cli::{spec_factory, SubstrateCLI};
use sc_service::ChainSpec;
use sp_consensus_aura::sr25519::AuthorityPair as AuraPair;

#[spec_factory(
	impl_name = "Substrate Node",
	support_url = "support.anonymous.an",
	copyright_start_year = 2017
)]
fn spec_factory(id: &str) -> Result<Option<ChainSpec<GenesisConfig>>, String> {
	Ok(match Alternative::from(id) {
		Some(spec) => Some(spec.load()?),
		None => None,
	})
}

/// Parse and run command line arguments
pub fn run() -> sc_cli::Result<()> {
	let opt = Cli::from_args();

	match opt.subcommand {
		Some(subcommand) => {
			let runtime = Cli::create_runtime(&subcommand)?;
			runtime.run_subcommand(subcommand, |config| Ok(new_full_start!(config).0))
		}
		None => {
			let runtime = Cli::create_runtime(&opt.run)?;
			runtime.run_node(service::new_light, service::new_full)
		}
	}
}
