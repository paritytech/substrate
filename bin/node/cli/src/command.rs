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

use sc_cli::VersionInfo;
use sc_service::{Roles as ServiceRoles};
use node_transaction_factory::RuntimeAdapter;
use crate::{Cli, service, ChainSpec, load_spec, Subcommand, factory_impl::FactoryState};

/// Parse command line arguments into service configuration.
pub fn run<I, T>(args: I, version: VersionInfo) -> sc_cli::Result<()>
where
	I: Iterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
{
	let args: Vec<_> = args.collect();
	let opt = sc_cli::from_iter::<Cli, _>(args.clone(), &version);

	let mut config = sc_service::Configuration::from_version(&version);

	match opt.subcommand {
		None => {
			opt.run.init(&version)?;
			opt.run.update_config(&mut config, load_spec, &version)?;
			opt.run.run(
				config,
				service::new_light,
				service::new_full,
				&version,
			)
		},
		Some(Subcommand::Inspect(cmd)) => {
			cmd.init(&version)?;
			cmd.update_config(&mut config, load_spec, &version)?;

			let client = sc_service::new_full_client::<
				node_runtime::Block, node_runtime::RuntimeApi, node_executor::Executor, _, _,
			>(&config)?;
			let inspect = node_inspect::Inspector::<node_runtime::Block>::new(client);

			cmd.run(inspect)
		},
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
			node_transaction_factory::factory(
				factory_state,
				service_builder.client(),
				service_builder.select_chain()
					.expect("The select_chain is always initialized by new_full_start!; QED")
			).map_err(|e| format!("Error in transaction factory: {}", e))?;

			Ok(())
		},
		Some(Subcommand::Base(subcommand)) => {
			subcommand.init(&version)?;
			subcommand.update_config(&mut config, load_spec, &version)?;
			subcommand.run(
				config,
				|config: service::NodeConfiguration| Ok(new_full_start!(config).0),
			)
		},
	}
}
