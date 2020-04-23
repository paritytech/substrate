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

#[macro_use] mod core;
mod import;
mod trie;
mod generator;
mod tempdb;
mod state_sizes;

use crate::core::{run_benchmark, Mode as BenchmarkMode};
use import::{ImportBenchmarkDescription, SizeType};
use trie::{TrieBenchmarkDescription, DatabaseSize};
use node_testing::bench::{Profile, KeyTypes};
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

	/// Mode
	///
	/// "regular" for regular becnhmark
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

	let benchmarks = matrix!(
		profile in [Profile::Wasm, Profile::Native] =>
			ImportBenchmarkDescription {
				profile: *profile,
				key_types: KeyTypes::Sr25519,
				size: SizeType::Medium,
			},
		ImportBenchmarkDescription {
			profile: Profile::Native,
			key_types: KeyTypes::Ed25519,
			size: SizeType::Medium,
		},
		ImportBenchmarkDescription {
			profile: Profile::Wasm,
			key_types: KeyTypes::Sr25519,
			size: SizeType::Full,
		},
		ImportBenchmarkDescription {
			profile: Profile::Native,
			key_types: KeyTypes::Sr25519,
			size: SizeType::Full,
		},
		size in [SizeType::Small, SizeType::Large] =>
			ImportBenchmarkDescription {
				profile: Profile::Native,
				key_types: KeyTypes::Sr25519,
				size: *size,
			},
		size in [
			DatabaseSize::Empty, DatabaseSize::Smallest, DatabaseSize::Small,
			DatabaseSize::Medium, DatabaseSize::Large,
		] => TrieBenchmarkDescription { database_size: *size },
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