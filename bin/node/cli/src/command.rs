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

use sc_cli::{VersionInfo, error};
use sc_service::{Roles as ServiceRoles};
use node_transaction_factory::RuntimeAdapter;
use crate::{Cli, service, ChainSpec, load_spec, Subcommand, factory_impl::FactoryState};

/// Parse command line arguments into service configuration.
pub fn run<I, T>(args: I, version: VersionInfo) -> error::Result<()>
where
	I: Iterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
{
	let args: Vec<_> = args.collect();
	let opt = sc_cli::from_iter::<Cli, _>(args.clone(), &version);

	let mut config = sc_service::Configuration::new(&version);

	match opt.subcommand {
		None => sc_cli::run(
			config,
			opt.run,
			service::new_light,
			service::new_full,
			load_spec,
			&version,
		),
		Some(Subcommand::Factory(cli_args)) => {
			sc_cli::init(&cli_args.shared_params, &version)?;
			sc_cli::init_config(&mut config, &cli_args.shared_params, &version, load_spec)?;
			sc_cli::fill_import_params(
				&mut config,
				&cli_args.import_params,
				ServiceRoles::FULL,
				cli_args.shared_params.dev,
			)?;

			sc_cli::fill_config_keystore_in_memory(&mut config)?;

			match ChainSpec::from(config.expect_chain_spec().id()) {
				Some(ref c) if c == &ChainSpec::Development || c == &ChainSpec::LocalTestnet => {},
				_ => panic!("Factory is only supported for development and local testnet."),
			}

			// Setup tracing.
			if let Some(tracing_targets) = cli_args.import_params.tracing_targets.as_ref() {
				let subscriber = sc_tracing::ProfilingSubscriber::new(
					cli_args.import_params.tracing_receiver.into(), tracing_targets
				);
				if let Err(e) = tracing::subscriber::set_global_default(subscriber) {
					panic!("Unable to set global default subscriber {}", e);
				}
			}

			let factory_state = FactoryState::new(
				cli_args.mode.clone(),
				cli_args.num,
				cli_args.rounds,
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
		Some(Subcommand::Base(subcommand)) => sc_cli::run_subcommand(
			config,
			subcommand,
			load_spec,
			|config: service::NodeConfiguration| Ok(new_full_start!(config).0),
			&version,
		),
	}
}
