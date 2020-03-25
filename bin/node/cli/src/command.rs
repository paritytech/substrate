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

use crate::{chain_spec, factory_impl::FactoryState, service, Cli, FactoryCmd, Subcommand};
use node_transaction_factory::RuntimeAdapter;
use sc_cli::{
	substrate_cli_configuration, substrate_cli_params, CliConfiguration, Result, SubstrateCLI,
};
use sc_service::Configuration;

#[substrate_cli_configuration(
	impl_name = "Substrate Node",
	support_url = "https://github.com/paritytech/substrate/issues/new",
	copyright_start_year = 2017,
	executable_name = "substrate"
)]
impl SubstrateCLI for Cli {
	fn load_spec(&self, id: &str) -> std::result::Result<Box<dyn sc_service::ChainSpec>, String> {
		Ok(match id {
			"dev" => Box::new(chain_spec::development_config()),
			"local" => Box::new(chain_spec::local_testnet_config()),
			"" | "fir" | "flaming-fir" => Box::new(chain_spec::flaming_fir_config()?),
			"staging" => Box::new(chain_spec::staging_testnet_config()),
			path => Box::new(chain_spec::ChainSpec::from_json_file(
				std::path::PathBuf::from(path),
			)?),
		})
	}
}

/// Parse command line arguments into service configuration.
pub fn run() -> Result<()> {
	let cli = Cli::from_args();

	match &cli.subcommand {
		None => {
			let runtime = cli.create_runtime(&cli.run)?;
			runtime.run_node(service::new_light, service::new_full)
		}
		Some(Subcommand::Inspect(cmd)) => {
			use node_executor::*;
			use node_runtime::*;

			let runtime = cli.create_runtime(cmd)?;

			runtime.sync_run(|config| cmd.run::<Block, RuntimeApi, Executor>(config))
		}
		Some(Subcommand::Benchmark(cmd)) => {
			let runtime = cli.create_runtime(cmd)?;

			runtime
				.sync_run(|config| cmd.run::<node_runtime::Block, node_executor::Executor>(config))
		}
		Some(Subcommand::Factory(cmd)) => {
			let runtime = cli.create_runtime(cmd)?;

			runtime.sync_run(|config| cmd.run(config))
		}
		Some(Subcommand::Base(subcommand)) => {
			let runtime = cli.create_runtime(subcommand)?;

			runtime.run_subcommand(subcommand, |config| Ok(new_full_start!(config).0))
		}
	}
}

#[substrate_cli_params(shared_params = shared_params, import_params = import_params)]
impl CliConfiguration for FactoryCmd {}

impl FactoryCmd {
	fn run(&self, config: Configuration) -> Result<()> {
		match config.chain_spec.id() {
			"dev" | "local" => {}
			_ => return Err("Factory is only supported for development and local testnet.".into()),
		}

		// Setup tracing.
		if let Some(tracing_targets) = self.import_params.tracing_targets.as_ref() {
			let subscriber = sc_tracing::ProfilingSubscriber::new(
				self.import_params.tracing_receiver.into(),
				tracing_targets,
			);
			if let Err(e) = tracing::subscriber::set_global_default(subscriber) {
				return Err(format!("Unable to set global default subscriber {}", e).into());
			}
		}

		let factory_state = FactoryState::new(self.blocks, self.transactions);

		let service_builder = new_full_start!(config).0;
		node_transaction_factory::factory(
			factory_state,
			service_builder.client(),
			service_builder
				.select_chain()
				.expect("The select_chain is always initialized by new_full_start!; QED"),
		)
		.map_err(|e| format!("Error in transaction factory: {}", e))?;

		Ok(())
	}
}
