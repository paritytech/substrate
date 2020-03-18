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

use sc_cli::{spec_factory, SubstrateCLI};
use sc_service::{Roles as ServiceRoles};
use node_transaction_factory::RuntimeAdapter;
use crate::{Cli, service, Subcommand, factory_impl::FactoryState, ChainSpec, chain_spec::{GenesisConfig, Extensions}};

#[spec_factory(
	impl_name = "Substrate Node",
	support_url = "https://github.com/paritytech/substrate/issues/new",
	copyright_start_year = 2017,
	executable_name = "substrate"
)]
fn spec_factory(id: &str) -> Result<Option<sc_service::ChainSpec<GenesisConfig, Extensions>>, String> {
	Ok(match ChainSpec::from(id) {
		Some(spec) => Some(spec.load()?),
		None => None,
	})
}

/// Parse command line arguments into service configuration.
pub fn run() -> sc_cli::Result<()>
{
	let opt = Cli::from_args();

	match opt.subcommand {
		None => {
			let runtime = Cli::create_runtime(&opt.run)?;
			runtime.run_node(
				service::new_light,
				service::new_full,
			)
		},
		Some(Subcommand::Inspect(cmd)) => {
			use node_runtime::*;
			use node_executor::*;

			let runtime = Cli::create_runtime(&cmd)?;

			runtime.sync_run(|config| cmd.run::<Block, RuntimeApi, Executor, _, _>(config))
		},
		/*
		Some(Subcommand::Benchmark(cmd)) => {
			cmd.init(&version)?;
			cmd.update_config(&mut config, load_spec, &version)?;

			cmd.run::<_, _, node_runtime::Block, node_executor::Executor>(config)
		},
		Some(Subcommand::Factory(cli_args)) => {
			cli_args.shared_params.init(&version)?;
			cli_args.shared_params.update_config(&mut config, load_spec, &version)?;
			cli_args.import_params.update_config(
				&mut config,
				ServiceRoles::FULL,
				cli_args.shared_params.dev,
			)?;

			config.use_in_memory_keystore()?;

			match ChainSpec::from(config.expect_chain_spec().id()) {
				Some(ref c) if c == &ChainSpec::Development || c == &ChainSpec::LocalTestnet => {},
				_ => return Err(
					"Factory is only supported for development and local testnet.".into()
				),
			}

			// Setup tracing.
			if let Some(tracing_targets) = cli_args.import_params.tracing_targets.as_ref() {
				let subscriber = sc_tracing::ProfilingSubscriber::new(
					cli_args.import_params.tracing_receiver.into(), tracing_targets
				);
				if let Err(e) = tracing::subscriber::set_global_default(subscriber) {
					return Err(
						format!("Unable to set global default subscriber {}", e).into()
					);
				}
			}

			let factory_state = FactoryState::new(
				cli_args.blocks,
				cli_args.transactions,
			);

			let service_builder = new_full_start!(config).0;
			node_transaction_factory::factory::<FactoryState<_>, _, _, _, _, _>(
				factory_state,
				service_builder.client(),
				service_builder.select_chain()
					.expect("The select_chain is always initialized by new_full_start!; QED")
			).map_err(|e| format!("Error in transaction factory: {}", e))?;

			Ok(())
		},
		*/
		Some(Subcommand::Base(subcommand)) => {
			let runtime = Cli::create_runtime(&subcommand)?;
			runtime.run_subcommand(
				subcommand,
				|config| Ok(new_full_start!(config).0),
			)
		},
		_ => todo!(),
	}
}
