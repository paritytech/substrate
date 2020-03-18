// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Command ran by the CLI

use std::{
	str::FromStr,
	path::PathBuf,
};

use crate::cli::{InspectCmd, InspectSubCmd};
use crate::Inspector;
use sc_service::{
	Configuration, NativeExecutionDispatch, RuntimeGenesis, ChainSpecExtension,
	config::{DatabaseConfig, ExecutionStrategies, WasmExecutionMethod}, ChainSpec, new_full_client,
	PruningMode, Roles, TracingReceiver,
};
use sc_cli::{SubstrateCLI, Result, CliConfiguration};
use sp_runtime::traits::Block;

impl InspectCmd {
	/// Run the inspect command, passing the inspector.
	pub fn run<B, RA, EX, G, E>(
		self,
		config: Configuration<G, E>,
	) -> Result<()> where
		B: Block,
		B::Hash: FromStr,
		RA: Send + Sync + 'static,
		EX: NativeExecutionDispatch + 'static,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		let client = new_full_client::<B, RA, EX, _, _>(&config)?;
		let inspect = Inspector::<B>::new(client);

		match self.command {
			InspectSubCmd::Block { input } => {
				let input = input.parse()?;
				let res = inspect.block(input)
					.map_err(|e| format!("{}", e))?;
				println!("{}", res);
				Ok(())
			},
			InspectSubCmd::Extrinsic { input } => {
				let input = input.parse()?;
				let res = inspect.extrinsic(input)
					.map_err(|e| format!("{}", e))?;
				println!("{}", res);
				Ok(())
			},
		}
	}
}

impl CliConfiguration for InspectCmd {
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

	fn get_chain_spec<C: SubstrateCLI<G, E>, G, E>(&self) -> Result<ChainSpec<G, E>>
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
