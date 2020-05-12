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

use crate::BenchmarkCmd;
use codec::{Decode, Encode};
use frame_benchmarking::{Analysis, BenchmarkBatch};
use sc_cli::{SharedParams, CliConfiguration, ExecutionStrategy, Result};
use sc_client_db::BenchmarkingState;
use sc_executor::NativeExecutor;
use sp_state_machine::StateMachine;
use sp_externalities::Extensions;
use sc_service::{Configuration, NativeExecutionDispatch};
use sp_runtime::{
	traits::{Block as BlockT, Header as HeaderT, NumberFor},
};
use sp_core::{tasks, testing::KeyStore, traits::KeystoreExt};
use std::fmt::Debug;

impl BenchmarkCmd {
	/// Runs the command and benchmarks the chain.
	pub fn run<BB, ExecDispatch>(&self, config: Configuration) -> Result<()>
	where
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
		let mut offchain_changes = Default::default();
		let cache_size = Some(self.database_cache_size as usize);
		let state = BenchmarkingState::<BB>::new(genesis_storage, cache_size)?;
		let executor = NativeExecutor::<ExecDispatch>::new(
			wasm_method,
			None, // heap pages
			2, // The runtime instances cache size.
		);

		let mut extensions = Extensions::default();
		extensions.register(KeystoreExt(KeyStore::new()));

		let result = StateMachine::<_, _, NumberFor<BB>, _>::new(
			&state,
			None,
			&mut changes,
			&mut offchain_changes,
			&executor,
			"Benchmark_dispatch_benchmark",
			&(
				&self.pallet,
				&self.extrinsic,
				self.lowest_range_values.clone(),
				self.highest_range_values.clone(),
				self.steps.clone(),
				self.repeat,
			).encode(),
			extensions,
			&sp_state_machine::backend::BackendRuntimeCode::new(&state).runtime_code()?,
			tasks::executor(),
		)
		.execute(strategy.into())
		.map_err(|e| format!("Error executing runtime benchmark: {:?}", e))?;

		let results = <std::result::Result<Vec<BenchmarkBatch>, String> as Decode>::decode(&mut &result[..])
			.map_err(|e| format!("Failed to decode benchmark results: {:?}", e))?;

		match results {
			Ok(batches) => for batch in batches.into_iter() {
				// Print benchmark metadata
				println!(
					"Pallet: {:?}, Extrinsic: {:?}, Lowest values: {:?}, Highest values: {:?}, Steps: {:?}, Repeat: {:?}",
					String::from_utf8(batch.pallet).expect("Encoded from String; qed"),
					String::from_utf8(batch.benchmark).expect("Encoded from String; qed"),
					self.lowest_range_values,
					self.highest_range_values,
					self.steps,
					self.repeat,
				);

				// Skip raw data + analysis if there are no results
				if batch.results.len() == 0 { continue }

				if self.raw_data {
					// Print the table header
					batch.results[0].0.iter().for_each(|param| print!("{:?},", param.0));

					print!("extrinsic_time,storage_root_time\n");
					// Print the values
					batch.results.iter().for_each(|result| {
						let parameters = &result.0;
						parameters.iter().for_each(|param| print!("{:?},", param.1));
						// Print extrinsic time and storage root time
						print!("{:?},{:?}\n", result.1, result.2);
					});

					println!();
				}

				// Conduct analysis.
				if !self.no_median_slopes {
					if let Some(analysis) = Analysis::median_slopes(&batch.results) {
						println!("Median Slopes Analysis\n========\n{}", analysis);
					}
				}
				if !self.no_min_squares {
					if let Some(analysis) = Analysis::min_squares_iqr(&batch.results) {
						println!("Min Squares Analysis\n========\n{}", analysis);
					}
				}
			},
			Err(error) => eprintln!("Error: {:?}", error),
		}

		Ok(())
	}
}

impl CliConfiguration for BenchmarkCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn chain_id(&self, _is_dev: bool) -> Result<String> {
		Ok(match self.shared_params.chain {
			Some(ref chain) => chain.clone(),
			None => "dev".into(),
		})
	}
}
