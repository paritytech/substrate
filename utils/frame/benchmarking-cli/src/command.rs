// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::BenchmarkCmd;
use codec::{Decode, Encode};
use frame_benchmarking::{
	Analysis, BenchmarkBatch, BenchmarkBatchSplitResults, BenchmarkList, BenchmarkParameter,
	BenchmarkResults, BenchmarkSelector,
};
use frame_support::traits::StorageInfo;
use linked_hash_map::LinkedHashMap;
use sc_cli::{CliConfiguration, ExecutionStrategy, Result, SharedParams};
use sc_client_db::BenchmarkingState;
use sc_executor::NativeExecutor;
use sc_service::{Configuration, NativeExecutionDispatch};
use sp_core::offchain::{
	testing::{TestOffchainExt, TestTransactionPoolExt},
	OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
};
use sp_externalities::Extensions;
use sp_keystore::{testing::KeyStore, KeystoreExt, SyncCryptoStorePtr};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use sp_state_machine::StateMachine;
use std::{fmt::Debug, sync::Arc, time};

// This takes multiple benchmark batches and combines all the results where the pallet, instance,
// and benchmark are the same.
fn combine_batches(
	time_batches: Vec<BenchmarkBatch>,
	db_batches: Vec<BenchmarkBatch>,
) -> Vec<BenchmarkBatchSplitResults> {
	if time_batches.is_empty() && db_batches.is_empty() {
		return Default::default()
	}

	let mut all_benchmarks =
		LinkedHashMap::<_, (Vec<BenchmarkResults>, Vec<BenchmarkResults>)>::new();

	db_batches
		.into_iter()
		.for_each(|BenchmarkBatch { pallet, instance, benchmark, results }| {
			// We use this key to uniquely identify a benchmark among batches.
			let key = (pallet, instance, benchmark);

			match all_benchmarks.get_mut(&key) {
				// We already have this benchmark, so we extend the results.
				Some(x) => x.1.extend(results),
				// New benchmark, so we add a new entry with the initial results.
				None => {
					all_benchmarks.insert(key, (Vec::new(), results));
				},
			}
		});

	time_batches
		.into_iter()
		.for_each(|BenchmarkBatch { pallet, instance, benchmark, results }| {
			// We use this key to uniquely identify a benchmark among batches.
			let key = (pallet, instance, benchmark);

			match all_benchmarks.get_mut(&key) {
				// We already have this benchmark, so we extend the results.
				Some(x) => x.0.extend(results),
				None => panic!("all benchmark keys should have been populated by db batches"),
			}
		});

	all_benchmarks
		.into_iter()
		.map(|((pallet, instance, benchmark), (time_results, db_results))| {
			BenchmarkBatchSplitResults { pallet, instance, benchmark, time_results, db_results }
		})
		.collect::<Vec<_>>()
}

impl BenchmarkCmd {
	/// Runs the command and benchmarks the chain.
	pub fn run<BB, ExecDispatch>(&self, config: Configuration) -> Result<()>
	where
		BB: BlockT + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
		ExecDispatch: NativeExecutionDispatch + 'static,
	{
		if let Some(output_path) = &self.output {
			if !output_path.is_dir() && output_path.file_name().is_none() {
				return Err("Output file or path is invalid!".into())
			}
		}

		if let Some(header_file) = &self.header {
			if !header_file.is_file() {
				return Err("Header file is invalid!".into())
			};
		}

		if let Some(handlebars_template_file) = &self.template {
			if !handlebars_template_file.is_file() {
				return Err("Handlebars template file is invalid!".into())
			};
		}

		let spec = config.chain_spec;
		let wasm_method = self.wasm_method.into();
		let strategy = self.execution.unwrap_or(ExecutionStrategy::Native);
		let pallet = self.pallet.clone().unwrap_or_else(|| String::new());
		let pallet = pallet.as_bytes();
		let extrinsic = self.extrinsic.clone().unwrap_or_else(|| String::new());
		let extrinsic = extrinsic.as_bytes();

		let genesis_storage = spec.build_storage()?;
		let mut changes = Default::default();
		let cache_size = Some(self.database_cache_size as usize);
		let state_with_tracking = BenchmarkingState::<BB>::new(
			genesis_storage.clone(),
			cache_size,
			self.record_proof,
			true,
		)?;
		let state_without_tracking =
			BenchmarkingState::<BB>::new(genesis_storage, cache_size, self.record_proof, false)?;
		let executor = NativeExecutor::<ExecDispatch>::new(
			wasm_method,
			self.heap_pages,
			2, // The runtime instances cache size.
		);

		let extensions = || -> Extensions {
			let mut extensions = Extensions::default();
			extensions.register(KeystoreExt(Arc::new(KeyStore::new()) as SyncCryptoStorePtr));
			let (offchain, _) = TestOffchainExt::new();
			let (pool, _) = TestTransactionPoolExt::new();
			extensions.register(OffchainWorkerExt::new(offchain.clone()));
			extensions.register(OffchainDbExt::new(offchain));
			extensions.register(TransactionPoolExt::new(pool));
			return extensions
		};

		// Get Benchmark List
		let state = &state_without_tracking;
		let result = StateMachine::<_, _, NumberFor<BB>, _>::new(
			state,
			None,
			&mut changes,
			&executor,
			"Benchmark_benchmark_metadata",
			&(self.extra).encode(),
			extensions(),
			&sp_state_machine::backend::BackendRuntimeCode::new(state).runtime_code()?,
			sp_core::testing::TaskExecutor::new(),
		)
		.execute(strategy.into())
		.map_err(|e| format!("Error getting benchmark list: {:?}", e))?;

		let (list, storage_info) =
			<(Vec<BenchmarkList>, Vec<StorageInfo>) as Decode>::decode(&mut &result[..])
				.map_err(|e| format!("Failed to decode benchmark metadata: {:?}", e))?;

		// Use the benchmark list and the user input to determine the set of benchmarks to run.
		let mut benchmarks_to_run = Vec::new();
		list.iter()
			.filter(|item| pallet.is_empty() || pallet == &b"*"[..] || pallet == &item.pallet[..])
			.for_each(|item| {
				for benchmark in &item.benchmarks {
					if extrinsic.is_empty() ||
						&extrinsic[..] == &b"*"[..] ||
						extrinsic == benchmark.name
					{
						benchmarks_to_run.push((
							item.pallet.clone(),
							benchmark.name.clone(),
							benchmark.components.clone(),
						))
					}
				}
			});

		if benchmarks_to_run.is_empty() {
			return Err("No benchmarks found which match your input.".into())
		}

		if self.list {
			// List benchmarks instead of running them
			list_benchmark(benchmarks_to_run);
			return Ok(())
		}

		// Run the benchmarks
		let mut batches = Vec::new();
		let mut batches_db = Vec::new();
		let mut timer = time::SystemTime::now();
		for (pallet, extrinsic, components) in benchmarks_to_run {
			let all_components = if components.is_empty() {
				vec![Default::default()]
			} else {
				let mut all_components = Vec::new();
				for (idx, (name, low, high)) in components.iter().enumerate() {
					let lowest = self.lowest_range_values.get(idx).cloned().unwrap_or(*low);
					let highest = self.highest_range_values.get(idx).cloned().unwrap_or(*high);

					let diff = highest - lowest;

					// Create up to `STEPS` steps for that component between high and low.
					let step_size = (diff / self.steps).max(1);
					let num_of_steps = diff / step_size + 1;
					for s in 0..num_of_steps {
						// This is the value we will be testing for component `name`
						let component_value = lowest + step_size * s;

						// Select the max value for all the other components.
						let c: Vec<(BenchmarkParameter, u32)> = components
							.iter()
							.enumerate()
							.map(|(idx, (n, _, h))| {
								if n == name {
									(*n, component_value)
								} else {
									(*n, *self.highest_range_values.get(idx).unwrap_or(h))
								}
							})
							.collect();
						all_components.push(c);
					}
				}
				all_components
			};
			for (s, selected_components) in all_components.iter().enumerate() {
				// First we run a verification
				if !self.no_verify {
					// Dont use these results since verification code will add overhead
					let state = &state_without_tracking;
					let _results = StateMachine::<_, _, NumberFor<BB>, _>::new(
						state,
						None,
						&mut changes,
						&executor,
						"Benchmark_dispatch_benchmark",
						&(
							&pallet.clone(),
							&extrinsic.clone(),
							&selected_components.clone(),
							true, // run verification code
							1,    // no need to do internal repeats
						)
							.encode(),
						extensions(),
						&sp_state_machine::backend::BackendRuntimeCode::new(state)
							.runtime_code()?,
						sp_core::testing::TaskExecutor::new(),
					)
					.execute(strategy.into())
					.map_err(|e| {
						format!("Error executing and verifying runtime benchmark: {:?}", e)
					})?;
				}
				// Do one loop of DB tracking.
				{
					let state = &state_with_tracking;
					let result = StateMachine::<_, _, NumberFor<BB>, _>::new(
						state, // todo remove tracking
						None,
						&mut changes,
						&executor,
						"Benchmark_dispatch_benchmark",
						&(
							&pallet.clone(),
							&extrinsic.clone(),
							&selected_components.clone(),
							false, // dont run verification code for final values
							self.repeat,
						)
							.encode(),
						extensions(),
						&sp_state_machine::backend::BackendRuntimeCode::new(state)
							.runtime_code()?,
						sp_core::testing::TaskExecutor::new(),
					)
					.execute(strategy.into())
					.map_err(|e| format!("Error executing runtime benchmark: {:?}", e))?;

					let batch =
						<std::result::Result<Vec<BenchmarkBatch>, String> as Decode>::decode(
							&mut &result[..],
						)
						.map_err(|e| format!("Failed to decode benchmark results: {:?}", e))??;

					batches_db.extend(batch);
				}
				// Finally run a bunch of loops to get extrinsic timing information.
				for r in 0..self.external_repeat {
					let state = &state_without_tracking;
					let result = StateMachine::<_, _, NumberFor<BB>, _>::new(
						state, // todo remove tracking
						None,
						&mut changes,
						&executor,
						"Benchmark_dispatch_benchmark",
						&(
							&pallet.clone(),
							&extrinsic.clone(),
							&selected_components.clone(),
							false, // dont run verification code for final values
							self.repeat,
						)
							.encode(),
						extensions(),
						&sp_state_machine::backend::BackendRuntimeCode::new(state)
							.runtime_code()?,
						sp_core::testing::TaskExecutor::new(),
					)
					.execute(strategy.into())
					.map_err(|e| format!("Error executing runtime benchmark: {:?}", e))?;

					let batch =
						<std::result::Result<Vec<BenchmarkBatch>, String> as Decode>::decode(
							&mut &result[..],
						)
						.map_err(|e| format!("Failed to decode benchmark results: {:?}", e))??;

					batches.extend(batch);

					// Show progress information
					if let Some(elapsed) = timer.elapsed().ok() {
						if elapsed >= time::Duration::from_secs(5) {
							timer = time::SystemTime::now();
							log::info!(
								"Running Benchmark:\t{}\t{}\t{}/{}\t{}/{}",
								String::from_utf8(pallet.clone())
									.expect("Encoded from String; qed"),
								String::from_utf8(extrinsic.clone())
									.expect("Encoded from String; qed"),
								s, // todo show step
								self.steps,
								r,
								self.external_repeat,
							);
						}
					}
				}
			}
		}

		// Combine all of the benchmark results, so that benchmarks of the same pallet/function
		// are together.
		let batches: Vec<BenchmarkBatchSplitResults> = combine_batches(batches, batches_db);

		if let Some(output_path) = &self.output {
			crate::writer::write_results(&batches, &storage_info, output_path, self)?;
		}

		for batch in batches.into_iter() {
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
			if batch.time_results.is_empty() {
				continue
			}

			if self.raw_data {
				// Print the table header
				batch.time_results[0]
					.components
					.iter()
					.for_each(|param| print!("{:?},", param.0));

				print!("extrinsic_time_ns,storage_root_time_ns,reads,repeat_reads,writes,repeat_writes,proof_size_bytes\n");
				// Print the values
				batch.time_results.iter().for_each(|result| {
					let parameters = &result.components;
					parameters.iter().for_each(|param| print!("{:?},", param.1));
					// Print extrinsic time and storage root time
					print!(
						"{:?},{:?},{:?},{:?},{:?},{:?},{:?}\n",
						result.extrinsic_time,
						result.storage_root_time,
						result.reads,
						result.repeat_reads,
						result.writes,
						result.repeat_writes,
						result.proof_size,
					);
				});

				println!();
			}

			// Conduct analysis.
			if !self.no_median_slopes {
				println!("Median Slopes Analysis\n========");
				if let Some(analysis) =
					Analysis::median_slopes(&batch.time_results, BenchmarkSelector::ExtrinsicTime)
				{
					println!("-- Extrinsic Time --\n{}", analysis);
				}
				if let Some(analysis) =
					Analysis::median_slopes(&batch.db_results, BenchmarkSelector::Reads)
				{
					println!("Reads = {:?}", analysis);
				}
				if let Some(analysis) =
					Analysis::median_slopes(&batch.db_results, BenchmarkSelector::Writes)
				{
					println!("Writes = {:?}", analysis);
				}
			}
			if !self.no_min_squares {
				println!("Min Squares Analysis\n========");
				if let Some(analysis) =
					Analysis::min_squares_iqr(&batch.time_results, BenchmarkSelector::ExtrinsicTime)
				{
					println!("-- Extrinsic Time --\n{}", analysis);
				}
				if let Some(analysis) =
					Analysis::min_squares_iqr(&batch.db_results, BenchmarkSelector::Reads)
				{
					println!("Reads = {:?}", analysis);
				}
				if let Some(analysis) =
					Analysis::min_squares_iqr(&batch.db_results, BenchmarkSelector::Writes)
				{
					println!("Writes = {:?}", analysis);
				}
			}
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

/// List the benchmarks available in the runtime, in a CSV friendly format.
fn list_benchmark(benchmarks_to_run: Vec<(Vec<u8>, Vec<u8>, Vec<(BenchmarkParameter, u32, u32)>)>) {
	println!("pallet, benchmark");
	for (pallet, extrinsic, _components) in benchmarks_to_run {
		println!("{}, {}", String::from_utf8_lossy(&pallet), String::from_utf8_lossy(&extrinsic));
	}
}
