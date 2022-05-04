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

mod command;
mod storage;
mod writer;

use sc_cli::{ExecutionStrategy, WasmExecutionMethod, DEFAULT_WASM_EXECUTION_METHOD};
use std::{fmt::Debug, path::PathBuf};

pub use storage::StorageCmd;

// Add a more relaxed parsing for pallet names by allowing pallet directory names with `-` to be
// used like crate names with `_`
fn parse_pallet_name(pallet: &str) -> String {
	pallet.replace("-", "_")
}

/// The `benchmark` command used to benchmark FRAME Pallets.
#[derive(Debug, clap::Parser)]
pub struct BenchmarkCmd {
	/// Select a FRAME Pallet to benchmark, or `*` for all (in which case `extrinsic` must be `*`).
	#[clap(short, long, parse(from_str = parse_pallet_name), required_unless_present = "list")]
	pub pallet: Option<String>,

	/// Select an extrinsic inside the pallet to benchmark, or `*` for all.
	#[clap(short, long, required_unless_present = "list")]
	pub extrinsic: Option<String>,

	/// Select how many samples we should take across the variable components.
	#[clap(short, long, default_value = "1")]
	pub steps: u32,

	/// Indicates lowest values for each of the component ranges.
	#[clap(long = "low", use_value_delimiter = true)]
	pub lowest_range_values: Vec<u32>,

	/// Indicates highest values for each of the component ranges.
	#[clap(long = "high", use_value_delimiter = true)]
	pub highest_range_values: Vec<u32>,

	/// Select how many repetitions of this benchmark should run from within the wasm.
	#[clap(short, long, default_value = "1")]
	pub repeat: u32,

	/// Select how many repetitions of this benchmark should run from the client.
	///
	/// NOTE: Using this alone may give slower results, but will afford you maximum Wasm memory.
	#[clap(long, default_value = "1")]
	pub external_repeat: u32,

	/// Print the raw results in JSON format.
	#[clap(long = "json")]
	pub json_output: bool,

	/// Write the raw results in JSON format into the give file.
	#[clap(long, conflicts_with = "json-output")]
	pub json_file: Option<PathBuf>,

	/// Don't print the median-slopes linear regression analysis.
	#[clap(long)]
	pub no_median_slopes: bool,

	/// Don't print the min-squares linear regression analysis.
	#[clap(long)]
	pub no_min_squares: bool,

	/// Output the benchmarks to a Rust file at the given path.
	#[clap(long)]
	pub output: Option<PathBuf>,

	/// Add a header file to your outputted benchmarks
	#[clap(long)]
	pub header: Option<PathBuf>,

	/// Path to Handlebars template file used for outputting benchmark results. (Optional)
	#[clap(long)]
	pub template: Option<PathBuf>,

	/// Which analysis function to use when outputting benchmarks:
	/// * min-squares (default)
	/// * median-slopes
	/// * max (max of min squares and median slopes for each value)
	#[clap(long)]
	pub output_analysis: Option<String>,

	/// Set the heap pages while running benchmarks. If not set, the default value from the client
	/// is used.
	#[clap(long)]
	pub heap_pages: Option<u64>,

	/// Disable verification logic when running benchmarks.
	#[clap(long)]
	pub no_verify: bool,

	/// Display and run extra benchmarks that would otherwise not be needed for weight
	/// construction.
	#[clap(long)]
	pub extra: bool,

	/// Estimate PoV size.
	#[clap(long)]
	pub record_proof: bool,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: sc_cli::SharedParams,

	/// The execution strategy that should be used for benchmarks
	#[clap(long, value_name = "STRATEGY", arg_enum, ignore_case = true)]
	pub execution: Option<ExecutionStrategy>,

	/// Method for executing Wasm runtime code.
	#[clap(
		long = "wasm-execution",
		value_name = "METHOD",
		possible_values = WasmExecutionMethod::variants(),
		ignore_case = true,
		default_value = DEFAULT_WASM_EXECUTION_METHOD,
	)]
	pub wasm_method: WasmExecutionMethod,

	/// Limit the memory the database cache can use.
	#[clap(long = "db-cache", value_name = "MiB", default_value = "1024")]
	pub database_cache_size: u32,

	/// List the benchmarks that match your query rather than running them.
	///
	/// When nothing is provided, we list all benchmarks.
	#[clap(long)]
	pub list: bool,

	/// If enabled, the storage info is not displayed in the output next to the analysis.
	///
	/// This is independent of the storage info appearing in the *output file*. Use a Handlebar
	/// template for that purpose.
	#[clap(long)]
	pub no_storage_info: bool,
}
