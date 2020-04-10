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

mod command;

use sc_cli::{ExecutionStrategy, WasmExecutionMethod};
use std::fmt::Debug;

/// The `benchmark` command used to benchmark FRAME Pallets.
#[derive(Debug, structopt::StructOpt, Clone)]
pub struct BenchmarkCmd {
	/// Select a FRAME Pallet to benchmark, or `*` for all (in which case `extrinsic` must be `*`).
	#[structopt(short, long)]
	pub pallet: String,

	/// Select an extrinsic inside the pallet to benchmark, or `*` for all.
	#[structopt(short, long)]
	pub extrinsic: String,

	/// Select how many samples we should take across the variable components.
	#[structopt(short, long, use_delimiter = true)]
	pub steps: Vec<u32>,

	/// Indicates lowest values for each of the component ranges.
	#[structopt(long = "low", use_delimiter = true)]
	pub lowest_range_values: Vec<u32>,

	/// Indicates highest values for each of the component ranges.
	#[structopt(long = "high", use_delimiter = true)]
	pub highest_range_values: Vec<u32>,

	/// Select how many repetitions of this benchmark should run.
	#[structopt(short, long, default_value = "1")]
	pub repeat: u32,

	/// Print the raw results.
	#[structopt(long = "raw")]
	pub raw_data: bool,

	/// Don't print the median-slopes linear regression analysis.
	#[structopt(long)]
	pub no_median_slopes: bool,

	/// Don't print the min-squares linear regression analysis.
	#[structopt(long)]
	pub no_min_squares: bool,

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

	/// Limit the memory the database cache can use.
	#[structopt(long = "db-cache", value_name = "MiB", default_value = "128")]
	pub database_cache_size: u32,
}
