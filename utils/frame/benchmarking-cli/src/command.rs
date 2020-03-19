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

use std::path::PathBuf;
use sp_runtime::{BuildStorage, traits::{Block as BlockT, Header as HeaderT, NumberFor}};
use sc_client::StateMachine;
use sc_cli::{ExecutionStrategy, CliConfiguration, Result, substrate_cli_params, SubstrateCLI};
use sc_client_db::BenchmarkingState;
use sc_service::{
	Configuration, NativeExecutionDispatch, RuntimeGenesis, ChainSpecExtension, ChainSpec,
};
use sc_executor::NativeExecutor;
use std::fmt::Debug;
use codec::{Encode, Decode};
use frame_benchmarking::BenchmarkResults;
use crate::BenchmarkCmd;

impl BenchmarkCmd {
	/// Runs the command and benchmarks the chain.
	pub fn run<G, E, BB, ExecDispatch>(
		self,
		config: Configuration<G, E>,
	) -> Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		BB: BlockT + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
		ExecDispatch: NativeExecutionDispatch + 'static,
	{
		let spec = config.chain_spec;
		let wasm_method = self.wasm_method.into();
		let strategy = self.execution.unwrap_or(ExecutionStrategy::Native);

		let genesis_storage = spec.build_storage()?;
		let mut changes = Default::default();
		let state = BenchmarkingState::<BB>::new(genesis_storage)?;
		let executor = NativeExecutor::<ExecDispatch>::new(
			wasm_method,
			None, // heap pages
		);

		let result = StateMachine::<_, _, NumberFor<BB>, _>::new(
			&state,
			None,
			&mut changes,
			&executor,
			"Benchmark_dispatch_benchmark",
			&(&self.pallet, &self.extrinsic, self.steps.clone(), self.repeat).encode(),
			Default::default(),
		)
		.execute(strategy.into())
		.map_err(|e| format!("Error executing runtime benchmark: {:?}", e))?;
		let results = <Option<Vec<BenchmarkResults>> as Decode>::decode(&mut &result[..])
			.unwrap_or(None);

		if let Some(results) = results {
			// Print benchmark metadata
			println!(
				"Pallet: {:?}, Extrinsic: {:?}, Steps: {:?}, Repeat: {:?}",
				self.pallet,
				self.extrinsic,
				self.steps,
				self.repeat,
			);

			// Print the table header
			results[0].0.iter().for_each(|param| print!("{:?},", param.0));

			print!("extrinsic_time,storage_root_time\n");
			// Print the values
			results.iter().for_each(|result| {
				let parameters = &result.0;
				parameters.iter().for_each(|param| print!("{:?},", param.1));
				// Print extrinsic time and storage root time
				print!("{:?},{:?}\n", result.1, result.2);
			});

			eprintln!("Done.");
		} else {
			eprintln!("No Results.");
		}

		Ok(())
	}
}

#[substrate_cli_params(shared_params = shared_params)]
impl CliConfiguration for BenchmarkCmd {
	fn get_chain_spec<C: SubstrateCLI<G, E>, G, E>(&self) -> Result<ChainSpec<G, E>>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		let chain_key = match self.shared_params.chain {
			Some(ref chain) => chain.clone(),
			None => "dev".into(),
		};

		Ok(match C::spec_factory(&chain_key)? {
			Some(spec) => spec,
			None => ChainSpec::from_json_file(PathBuf::from(chain_key))?
		})
	}
}
