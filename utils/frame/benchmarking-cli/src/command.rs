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
	Analysis, BenchmarkBatch, BenchmarkList, BenchmarkResults, BenchmarkSelector,
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
fn combine_batches(batches: Vec<BenchmarkBatch>) -> Vec<BenchmarkBatch> {
	if batches.is_empty() {
		return batches
	}

	let mut all_benchmarks = LinkedHashMap::<_, Vec<BenchmarkResults>>::new();

	batches
		.into_iter()
		.for_each(|BenchmarkBatch { pallet, instance, benchmark, results }| {
			// We use this key to uniquely identify a benchmark among batches.
			let key = (pallet, instance, benchmark);

			match all_benchmarks.get_mut(&key) {
				// We already have this benchmark, so we extend the results.
				Some(x) => x.extend(results),
				// New benchmark, so we add a new entry with the initial results.
				None => {
					all_benchmarks.insert(key, results);
				},
			}
		});

	all_benchmarks
		.into_iter()
		.map(|((pallet, instance, benchmark), results)| BenchmarkBatch {
			pallet,
			instance,
			benchmark,
			results,
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
		let state = BenchmarkingState::<BB>::new(genesis_storage, cache_size, self.record_proof)?;
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
		let result = StateMachine::<_, _, NumberFor<BB>, _>::new(
			&state,
			None,
			&mut changes,
			&executor,
			"Benchmark_benchmark_metadata",
			&(self.extra).encode(),
			extensions(),
			&sp_state_machine::backend::BackendRuntimeCode::new(&state).runtime_code()?,
			sp_core::testing::TaskExecutor::new(),
		)
		.execute(strategy.into())
		.map_err(|e| format!("Error getting benchmark list: {:?}", e))?;

		let (list, storage_info) =
			<(Vec<BenchmarkList>, Vec<StorageInfo>) as Decode>::decode(&mut &result[..])
				.map_err(|e| format!("Failed to decode benchmark metadata: {:?}", e))?;

		if self.list {
			list_benchmark(pallet, extrinsic, list);
			return Ok(())
		}

		// Use the benchmark list and the user input to determine the set of benchmarks to run.
		let mut benchmarks_to_run = Vec::new();
		for item in list {
			if pallet == &item.pallet[..] || pallet == &b"*"[..] {
				if &pallet[..] == &b"*"[..] || &extrinsic[..] == &b"*"[..] {
					for benchmark in item.benchmarks {
						benchmarks_to_run.push((item.pallet.clone(), benchmark));
					}
				} else {
					benchmarks_to_run.push((pallet.to_vec(), extrinsic.to_vec()));
				}
			}
		}

		// Run the benchmarks
		let mut batches = Vec::new();
		let mut timer = time::SystemTime::now();
		for (pallet, extrinsic) in benchmarks_to_run {
			for s in 0..self.steps {
				for r in 0..self.repeat {
					// This should run only a single instance of a benchmark for `pallet` and
					// `extrinsic`. All loops happen above.
					let result = StateMachine::<_, _, NumberFor<BB>, _>::new(
						&state,
						None,
						&mut changes,
						&executor,
						"Benchmark_dispatch_benchmark",
						&(
							&pallet.clone(),
							&extrinsic.clone(),
							self.lowest_range_values.clone(),
							self.highest_range_values.clone(),
							(s, self.steps),
							(r, self.repeat),
							!self.no_verify,
							self.extra,
						)
							.encode(),
						extensions(),
						&sp_state_machine::backend::BackendRuntimeCode::new(&state)
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
								s,
								self.steps,
								r,
								self.repeat,
							);
						}
					}
				}
			}
		}

		// Combine all of the benchmark results, so that benchmarks of the same pallet/function
		// are together.
		let batches = combine_batches(batches);

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
			if batch.results.is_empty() {
				continue
			}

			if self.raw_data {
				// Print the table header
				batch.results[0].components.iter().for_each(|param| print!("{:?},", param.0));

				print!("extrinsic_time_ns,storage_root_time_ns,reads,repeat_reads,writes,repeat_writes,proof_size_bytes\n");
				// Print the values
				batch.results.iter().for_each(|result| {
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
					Analysis::median_slopes(&batch.results, BenchmarkSelector::ExtrinsicTime)
				{
					println!("-- Extrinsic Time --\n{}", analysis);
				}
				if let Some(analysis) =
					Analysis::median_slopes(&batch.results, BenchmarkSelector::Reads)
				{
					println!("Reads = {:?}", analysis);
				}
				if let Some(analysis) =
					Analysis::median_slopes(&batch.results, BenchmarkSelector::Writes)
				{
					println!("Writes = {:?}", analysis);
				}
			}
			if !self.no_min_squares {
				println!("Min Squares Analysis\n========");
				if let Some(analysis) =
					Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::ExtrinsicTime)
				{
					println!("-- Extrinsic Time --\n{}", analysis);
				}
				if let Some(analysis) =
					Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::Reads)
				{
					println!("Reads = {:?}", analysis);
				}
				if let Some(analysis) =
					Analysis::min_squares_iqr(&batch.results, BenchmarkSelector::Writes)
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
///
/// If `pallet_input` and `extrinsic_input` is empty, we list everything.
///
/// If `pallet_input` is present, we only list the benchmarks for that pallet.
///
/// If `extrinsic_input` is `*`, we will hide the individual benchmarks for each pallet, and just
/// show a single line for each available pallet.
fn list_benchmark(pallet_input: &[u8], extrinsic_input: &[u8], list: Vec<BenchmarkList>) {
	let filtered_list = list
		.into_iter()
		.filter(|item| pallet_input.is_empty() || pallet_input == &item.pallet)
		.collect::<Vec<_>>();

	if filtered_list.is_empty() {
		println!("Pallet not found.");
		return
	}

	println!("pallet, benchmark");
	for item in filtered_list {
		let pallet_string =
			String::from_utf8(item.pallet.clone()).expect("Encoded from String; qed");

		if extrinsic_input == &b"*"[..] {
			println!("{}, *", pallet_string)
		} else {
			for benchmark in item.benchmarks {
				println!(
					"{}, {}",
					pallet_string,
					String::from_utf8(benchmark).expect("Encoded from String; qed"),
				);
			}
		}
	}
}
