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

use sp_runtime::{BuildStorage, traits::{Block as BlockT, Header as HeaderT, NumberFor}};
use sc_client::StateMachine;
use sc_cli::{ExecutionStrategy, WasmExecutionMethod, VersionInfo};
use sc_client_db::BenchmarkingState;
use sc_service::{RuntimeGenesis, ChainSpecExtension, Configuration, ChainSpec};
use sc_executor::{NativeExecutor, NativeExecutionDispatch};
use std::fmt::Debug;
use codec::{Encode, Decode};
use frame_benchmarking::BenchmarkResults;

/// The `benchmark` command used to benchmark FRAME Pallets.
#[derive(Debug, structopt::StructOpt, Clone)]
pub struct BenchmarkCmd {
	/// Select a FRAME Pallet to benchmark.
	#[structopt(short, long)]
	pub pallet: String,

	/// Select an extrinsic to benchmark.
	#[structopt(short, long)]
	pub extrinsic: String,

	/// Select how many samples we should take across the variable components.
	#[structopt(short, long, default_value = "1")]
	pub steps: u32,

	/// Select how many repetitions of this benchmark should run.
	#[structopt(short, long, default_value = "1")]
	pub repeat: u32,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: sc_cli::SharedParams,

	/// The execution strategy that should be used for benchmarks
	#[structopt(
		long = "execution",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
	)]
	pub execution: Option<ExecutionStrategy>,

	/// Method for executing Wasm runtime code.
	#[structopt(
		long = "wasm-execution",
		value_name = "METHOD",
		possible_values = &WasmExecutionMethod::enabled_variants(),
		case_insensitive = true,
		default_value = "Interpreted"
	)]
	pub wasm_method: WasmExecutionMethod,
}

impl BenchmarkCmd {
	/// Initialize
	pub fn init(&self, version: &sc_cli::VersionInfo) -> sc_cli::Result<()> {
		self.shared_params.init(version)
	}

	/// Runs the command and benchmarks the chain.
	pub fn run<G, E, BB, ExecDispatch>(
		self,
		config: Configuration<G, E>,
	) -> sc_cli::Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		BB: BlockT + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
		ExecDispatch: NativeExecutionDispatch + 'static,
	{
		let spec = config.chain_spec.expect("chain_spec is always Some");
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
			&(&self.pallet, &self.extrinsic, self.steps, self.repeat).encode(),
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

	/// Update and prepare a `Configuration` with command line parameters
	pub fn update_config<G, E>(
		&self,
		mut config: &mut Configuration<G, E>,
		spec_factory: impl FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
		version: &VersionInfo,
	) -> sc_cli::Result<()> where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		self.shared_params.update_config(&mut config, spec_factory, version)?;

		// make sure to configure keystore
		config.use_in_memory_keystore()?;

		Ok(())
	}
}
