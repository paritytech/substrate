// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
#[macro_use] mod core;
mod import;
mod trie;
mod simple_trie;
mod generator;
mod tempdb;
mod state_sizes;

use crate::core::{run_benchmark, Mode as BenchmarkMode};
use crate::tempdb::DatabaseType;
use import::{ImportBenchmarkDescription, SizeType};
use trie::{TrieReadBenchmarkDescription, TrieWriteBenchmarkDescription, DatabaseSize};
use node_testing::bench::{Profile, KeyTypes, BlockType};
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "node-bench", about = "Node integration benchmarks")]
struct Opt {
	/// Show list of all available benchmarks.
	///
	/// Will output ("name", "path"). Benchmarks can then be filtered by path.
	#[structopt(short, long)]
	list: bool,

	/// Machine readable json output.
	///
	/// This also suppresses all regular output (except to stderr)
	#[structopt(short, long)]
	json: bool,

	/// Filter benchmarks.
	///
	/// Run with `--list` for the hint of what to filter.
	filter: Option<String>,

	/// Number of transactions for block import with `custom` size.
	#[structopt(long)]
	transactions: Option<usize>,

	/// Mode
	///
	/// "regular" for regular benchmark
	///
	/// "profile" mode adds pauses between measurable runs,
	/// so that actual interval can be selected in the profiler of choice.
	#[structopt(short, long, default_value = "regular")]
	mode: BenchmarkMode,
}

fn main() {
	let opt = Opt::from_args();

	if !opt.json {
		sc_cli::init_logger("");
	}

	let mut import_benchmarks = Vec::new();

	for profile in [Profile::Wasm, Profile::Native].iter() {
		for size in [
			SizeType::Empty,
			SizeType::Small,
			SizeType::Medium,
			SizeType::Large,
			SizeType::Full,
			SizeType::Custom,
		].iter() {
			let txs = match size {
				SizeType::Custom => opt.transactions.unwrap_or(0),
				_ => size.transactions()
			};
			for block_type in [
				BlockType::RandomTransfersKeepAlive(txs),
				BlockType::RandomTransfersReaping(txs),
				BlockType::Noop(txs),
			].iter() {
				import_benchmarks.push((profile.clone(), size.clone(), block_type.clone()));
			}
		}
	}

	let benchmarks = matrix!(
		(profile, size, block_type) in import_benchmarks.iter() =>
			ImportBenchmarkDescription {
				profile: *profile,
				key_types: KeyTypes::Sr25519,
				size: *size,
				block_type: *block_type,
			},
		(size, db_type) in
			[
				DatabaseSize::Empty, DatabaseSize::Smallest, DatabaseSize::Small,
				DatabaseSize::Medium, DatabaseSize::Large, DatabaseSize::Huge,
			]
			.iter().flat_map(|size|
			[
				DatabaseType::RocksDb, DatabaseType::ParityDb
			]
			.iter().map(move |db_type| (size, db_type)))
			=> TrieReadBenchmarkDescription { database_size: *size, database_type: *db_type },
		(size, db_type) in
			[
				DatabaseSize::Empty, DatabaseSize::Smallest, DatabaseSize::Small,
				DatabaseSize::Medium, DatabaseSize::Large, DatabaseSize::Huge,
			]
			.iter().flat_map(|size|
			[
				DatabaseType::RocksDb, DatabaseType::ParityDb
			]
			.iter().map(move |db_type| (size, db_type)))
			=> TrieWriteBenchmarkDescription { database_size: *size, database_type: *db_type },
	);

	if opt.list {
		for benchmark in benchmarks.iter() {
			log::info!("{}: {}", benchmark.name(), benchmark.path().full())
		}
		return;
	}

	let mut results = Vec::new();
	for benchmark in benchmarks {
		if opt.filter.as_ref().map(|f| benchmark.path().has(f)).unwrap_or(true) {
			log::info!("Starting {}", benchmark.name());
			let result = run_benchmark(benchmark, opt.mode);
			log::info!("{}", result);

			results.push(result);
		}
	}

	if opt.json {
		let json_result: String = serde_json::to_string(&results).expect("Failed to construct json");
		println!("{}", json_result);
	}
}
