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

use std::path::PathBuf;
use sc_cli::{spec_factory, SubstrateCLI, Result, CliConfiguration};
use sc_service::{
	Configuration, RuntimeGenesis, ChainSpecExtension,
	config::{DatabaseConfig, ExecutionStrategies, WasmExecutionMethod},
	PruningMode, Roles, TracingReceiver,
};
use node_transaction_factory::RuntimeAdapter;
use crate::{Cli, service, Subcommand, factory_impl::FactoryState, ChainSpec, chain_spec::{GenesisConfig, Extensions}, FactoryCmd};

#[spec_factory(
	impl_name = "Substrate Node",
	support_url = "https://github.com/paritytech/substrate/issues/new",
	copyright_start_year = 2017,
	executable_name = "substrate"
)]
fn spec_factory(id: &str) -> std::result::Result<Option<sc_service::ChainSpec<GenesisConfig, Extensions>>, String> {
	Ok(match ChainSpec::from(id) {
		Some(spec) => Some(spec.load()?),
		None => None,
	})
}

/// Parse command line arguments into service configuration.
pub fn run() -> Result<()>
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
		Some(Subcommand::Benchmark(cmd)) => {
			let runtime = Cli::create_runtime(&cmd)?;

			runtime.sync_run(
				|config| cmd.run::<_, _, node_runtime::Block, node_executor::Executor>(config)
			)
		},
		Some(Subcommand::Factory(cmd)) => {
			let runtime = Cli::create_runtime(&cmd)?;

			runtime.sync_run(|config| cmd.run(config))
		},
		Some(Subcommand::Base(subcommand)) => {
			let runtime = Cli::create_runtime(&subcommand)?;
			runtime.run_subcommand(
				subcommand,
				|config| Ok(new_full_start!(config).0),
			)
		},
	}
}

impl CliConfiguration for FactoryCmd {
	fn is_dev(&self) -> bool {
		self.shared_params.dev
	}

	fn get_base_path(&self) -> Option<&PathBuf> {
		self.shared_params.base_path.as_ref()
	}

	fn get_database_config(&self, base_path: &PathBuf, cache_size: Option<usize>) -> DatabaseConfig
	{
		self.shared_params.get_database_config(base_path, cache_size)
	}

	fn get_chain_spec<C: SubstrateCLI<G, E>, G, E>(&self) -> Result<sc_service::ChainSpec<G, E>>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		self.shared_params.get_chain_spec::<C, G, E>()
	}

	fn init<C: SubstrateCLI<G, E>, G, E>(&self) -> Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		self.shared_params.init::<C, G, E>()
	}

	fn get_pruning(&self, is_dev: bool, roles: Roles) -> Result<PruningMode> {
		self.import_params.get_pruning(roles, is_dev)
	}

	fn get_tracing_receiver(&self) -> TracingReceiver {
		self.import_params.tracing_receiver.clone().into()
	}

	fn get_tracing_targets(&self) -> Option<String> {
		self.import_params.tracing_targets.clone().into()
	}

	fn get_state_cache_size(&self) -> usize {
		self.import_params.state_cache_size
	}

	fn get_wasm_method(&self) -> WasmExecutionMethod {
		self.import_params.get_wasm_method()
	}

	fn get_execution_strategies(&self, is_dev: bool) -> Result<ExecutionStrategies> {
		self.import_params.get_execution_strategies(is_dev)
	}

	fn get_database_cache_size(&self) -> Option<usize> {
		self.import_params.database_cache_size
	}
}

impl FactoryCmd {
	fn run<G, E>(&self, config: Configuration<G, E>) -> Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		match ChainSpec::from(config.chain_spec.id()) {
			Some(ref c) if c == &ChainSpec::Development || c == &ChainSpec::LocalTestnet => {},
			_ => return Err(
				"Factory is only supported for development and local testnet.".into()
			),
		}

		// Setup tracing.
		if let Some(tracing_targets) = self.import_params.tracing_targets.as_ref() {
			let subscriber = sc_tracing::ProfilingSubscriber::new(
				self.import_params.tracing_receiver.into(), tracing_targets
			);
			if let Err(e) = tracing::subscriber::set_global_default(subscriber) {
				return Err(
					format!("Unable to set global default subscriber {}", e).into()
				);
			}
		}

		let factory_state = FactoryState::new(
			self.blocks,
			self.transactions,
		);

		let service_builder = new_full_start!(config).0;
		node_transaction_factory::factory::<FactoryState<_>, _, _, _, _, _>(
			factory_state,
			service_builder.client(),
			service_builder.select_chain()
				.expect("The select_chain is always initialized by new_full_start!; QED")
		).map_err(|e| format!("Error in transaction factory: {}", e))?;

		Ok(())
	}
}
