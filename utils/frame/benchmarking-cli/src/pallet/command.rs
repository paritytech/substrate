// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use super::{writer, PalletCmd};
use codec::{Decode, Encode};
use frame_benchmarking::{
	Analysis, BenchmarkBatch, BenchmarkBatchSplitResults, BenchmarkList, BenchmarkParameter,
	BenchmarkResult, BenchmarkSelector,
};
use frame_support::traits::StorageInfo;
use linked_hash_map::LinkedHashMap;
use sc_cli::{
	execution_method_from_cli, CliConfiguration, ExecutionStrategy, Result, SharedParams,
};
use sc_client_db::BenchmarkingState;
use sc_executor::NativeElseWasmExecutor;
use sc_service::{Configuration, NativeExecutionDispatch};
use serde::Serialize;
use sp_core::offchain::{
	testing::{TestOffchainExt, TestTransactionPoolExt},
	OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
};
use sp_externalities::Extensions;
use sp_keystore::{testing::KeyStore, KeystoreExt, SyncCryptoStorePtr};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use sp_state_machine::StateMachine;
use std::{collections::HashMap, fmt::Debug, fs, sync::Arc, time};

/// The inclusive range of a component.
#[derive(Serialize, Debug, Clone, Eq, PartialEq)]
pub(crate) struct ComponentRange {
	/// Name of the component.
	name: String,
	/// Minimal valid value of the component.
	min: u32,
	/// Maximal valid value of the component.
	max: u32,
}

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
		LinkedHashMap::<_, (Vec<BenchmarkResult>, Vec<BenchmarkResult>)>::new();

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

/// Explains possible reasons why the metadata for the benchmarking could not be found.
const ERROR_METADATA_NOT_FOUND: &'static str = "Did not find the benchmarking metadata. \
This could mean that you either did not build the node correctly with the \
`--features runtime-benchmarks` flag, or the chain spec that you are using was \
not created by a node that was compiled with the flag";

impl PalletCmd {
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

		if let Some(json_input) = &self.json_input {
			let raw_data = match std::fs::read(json_input) {
				Ok(raw_data) => raw_data,
				Err(error) =>
					return Err(format!("Failed to read {:?}: {}", json_input, error).into()),
			};
			let batches: Vec<BenchmarkBatchSplitResults> = match serde_json::from_slice(&raw_data) {
				Ok(batches) => batches,
				Err(error) =>
					return Err(format!("Failed to deserialize {:?}: {}", json_input, error).into()),
			};
			return self.output_from_results(&batches)
		}

		let spec = config.chain_spec;
		let strategy = self.execution.unwrap_or(ExecutionStrategy::Native);
		let pallet = self.pallet.clone().unwrap_or_default();
		let pallet = pallet.as_bytes();
		let extrinsic = self.extrinsic.clone().unwrap_or_default();
		let extrinsic_split: Vec<&str> = extrinsic.split(',').collect();
		let extrinsics: Vec<_> = extrinsic_split.iter().map(|x| x.trim().as_bytes()).collect();

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
		let executor = NativeElseWasmExecutor::<ExecDispatch>::new(
			execution_method_from_cli(self.wasm_method, self.wasmtime_instantiation_strategy),
			self.heap_pages,
			2, // The runtime instances cache size.
			2, // The runtime cache size
		);

		let extensions = || -> Extensions {
			let mut extensions = Extensions::default();
			extensions.register(KeystoreExt(Arc::new(KeyStore::new()) as SyncCryptoStorePtr));
			let (offchain, _) = TestOffchainExt::new();
			let (pool, _) = TestTransactionPoolExt::new();
			extensions.register(OffchainWorkerExt::new(offchain.clone()));
			extensions.register(OffchainDbExt::new(offchain));
			extensions.register(TransactionPoolExt::new(pool));
			extensions
		};

		// Get Benchmark List
		let state = &state_without_tracking;
		let result = StateMachine::new(
			state,
			&mut changes,
			&executor,
			"Benchmark_benchmark_metadata",
			&(self.extra).encode(),
			extensions(),
			&sp_state_machine::backend::BackendRuntimeCode::new(state).runtime_code()?,
			sp_core::testing::TaskExecutor::new(),
		)
		.execute(strategy.into())
		.map_err(|e| format!("{}: {}", ERROR_METADATA_NOT_FOUND, e))?;

		let (list, storage_info) =
			<(Vec<BenchmarkList>, Vec<StorageInfo>) as Decode>::decode(&mut &result[..])
				.map_err(|e| format!("Failed to decode benchmark metadata: {:?}", e))?;

		// Use the benchmark list and the user input to determine the set of benchmarks to run.
		let mut benchmarks_to_run = Vec::new();
		list.iter()
			.filter(|item| pallet.is_empty() || pallet == &b"*"[..] || pallet == &item.pallet[..])
			.for_each(|item| {
				for benchmark in &item.benchmarks {
					let benchmark_name = &benchmark.name;
					if extrinsic.is_empty() ||
						extrinsic.as_bytes() == &b"*"[..] ||
						extrinsics.contains(&&benchmark_name[..])
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
		// Maps (pallet, extrinsic) to its component ranges.
		let mut component_ranges = HashMap::<(Vec<u8>, Vec<u8>), Vec<ComponentRange>>::new();

		for (pallet, extrinsic, components) in benchmarks_to_run {
			println!(
				"Starting benchmark: {}::{}",
				String::from_utf8(pallet.clone()).expect("Encoded from String; qed"),
				String::from_utf8(extrinsic.clone()).expect("Encoded from String; qed"),
			);
			let all_components = if components.is_empty() {
				vec![Default::default()]
			} else {
				let mut all_components = Vec::new();
				for (idx, (name, low, high)) in components.iter().enumerate() {
					let lowest = self.lowest_range_values.get(idx).cloned().unwrap_or(*low);
					let highest = self.highest_range_values.get(idx).cloned().unwrap_or(*high);

					let diff =
						highest.checked_sub(lowest).ok_or("`low` cannot be higher than `high`")?;

					// The slope logic needs at least two points
					// to compute a slope.
					if self.steps < 2 {
						return Err("`steps` must be at least 2.".into())
					}

					let step_size = (diff as f32 / (self.steps - 1) as f32).max(0.0);

					for s in 0..self.steps {
						// This is the value we will be testing for component `name`
						let component_value = ((lowest as f32 + step_size * s as f32) as u32)
							.min(highest)
							.max(lowest);

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

					component_ranges
						.entry((pallet.clone(), extrinsic.clone()))
						.or_default()
						.push(ComponentRange { name: name.to_string(), min: lowest, max: highest });
				}
				all_components
			};
			for (s, selected_components) in all_components.iter().enumerate() {
				// First we run a verification
				if !self.no_verify {
					// Dont use these results since verification code will add overhead
					let state = &state_without_tracking;
					let _results = StateMachine::new(
						state,
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
						format!("Error executing and verifying runtime benchmark: {}", e)
					})?;
				}
				// Do one loop of DB tracking.
				{
					let state = &state_with_tracking;
					let result = StateMachine::new(
						state, // todo remove tracking
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
					.map_err(|e| format!("Error executing runtime benchmark: {}", e))?;

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
					let result = StateMachine::new(
						state, // todo remove tracking
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
					.map_err(|e| format!("Error executing runtime benchmark: {}", e))?;

					let batch =
						<std::result::Result<Vec<BenchmarkBatch>, String> as Decode>::decode(
							&mut &result[..],
						)
						.map_err(|e| format!("Failed to decode benchmark results: {:?}", e))??;

					batches.extend(batch);

					// Show progress information
					if let Ok(elapsed) = timer.elapsed() {
						if elapsed >= time::Duration::from_secs(5) {
							timer = time::SystemTime::now();
							println!(
								"Running Benchmark: {}.{}({} args) {}/{} {}/{}",
								String::from_utf8(pallet.clone())
									.expect("Encoded from String; qed"),
								String::from_utf8(extrinsic.clone())
									.expect("Encoded from String; qed"),
								components.len(),
								s + 1, // s starts at 0.
								all_components.len(),
								r + 1,
								self.external_repeat,
							);
						}
					}
				}
			}
		}

		// Combine all of the benchmark results, so that benchmarks of the same pallet/function
		// are together.
		let batches = combine_batches(batches, batches_db);
		self.output(&batches, &storage_info, &component_ranges)
	}

	fn output(
		&self,
		batches: &[BenchmarkBatchSplitResults],
		storage_info: &[StorageInfo],
		component_ranges: &HashMap<(Vec<u8>, Vec<u8>), Vec<ComponentRange>>,
	) -> Result<()> {
		// Jsonify the result and write it to a file or stdout if desired.
		if !self.jsonify(&batches)? {
			// Print the summary only if `jsonify` did not write to stdout.
			self.print_summary(&batches, &storage_info)
		}

		// Create the weights.rs file.
		if let Some(output_path) = &self.output {
			writer::write_results(&batches, &storage_info, &component_ranges, output_path, self)?;
		}

		Ok(())
	}

	fn output_from_results(&self, batches: &[BenchmarkBatchSplitResults]) -> Result<()> {
		let mut component_ranges =
			HashMap::<(Vec<u8>, Vec<u8>), HashMap<String, (u32, u32)>>::new();
		for batch in batches {
			let range = component_ranges
				.entry((batch.pallet.clone(), batch.benchmark.clone()))
				.or_default();
			for result in &batch.time_results {
				for (param, value) in &result.components {
					let name = param.to_string();
					let (ref mut min, ref mut max) = range.entry(name).or_insert((*value, *value));
					if *value < *min {
						*min = *value;
					}
					if *value > *max {
						*max = *value;
					}
				}
			}
		}

		let component_ranges: HashMap<_, _> = component_ranges
			.into_iter()
			.map(|(key, ranges)| {
				let ranges = ranges
					.into_iter()
					.map(|(name, (min, max))| ComponentRange { name, min, max })
					.collect();
				(key, ranges)
			})
			.collect();

		self.output(batches, &[], &component_ranges)
	}

	/// Jsonifies the passed batches and writes them to stdout or into a file.
	/// Can be configured via `--json` and `--json-file`.
	/// Returns whether it wrote to stdout.
	fn jsonify(&self, batches: &[BenchmarkBatchSplitResults]) -> Result<bool> {
		if self.json_output || self.json_file.is_some() {
			let json = serde_json::to_string_pretty(&batches)
				.map_err(|e| format!("Serializing into JSON: {:?}", e))?;

			if let Some(path) = &self.json_file {
				fs::write(path, json)?;
			} else {
				println!("{}", json);
				return Ok(true)
			}
		}

		Ok(false)
	}

	/// Prints the results as human-readable summary without raw timing data.
	fn print_summary(&self, batches: &[BenchmarkBatchSplitResults], storage_info: &[StorageInfo]) {
		for batch in batches.iter() {
			// Print benchmark metadata
			println!(
					"Pallet: {:?}, Extrinsic: {:?}, Lowest values: {:?}, Highest values: {:?}, Steps: {:?}, Repeat: {:?}",
					String::from_utf8(batch.pallet.clone()).expect("Encoded from String; qed"),
					String::from_utf8(batch.benchmark.clone()).expect("Encoded from String; qed"),
					self.lowest_range_values,
					self.highest_range_values,
					self.steps,
					self.repeat,
				);

			// Skip raw data + analysis if there are no results
			if batch.time_results.is_empty() {
				continue
			}

			if !self.no_storage_info {
				let mut comments: Vec<String> = Default::default();
				writer::add_storage_comments(&mut comments, &batch.db_results, storage_info);
				println!("Raw Storage Info\n========");
				for comment in comments {
					println!("{}", comment);
				}
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
				println!();
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
				println!();
			}
		}
	}
}

impl CliConfiguration for PalletCmd {
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
