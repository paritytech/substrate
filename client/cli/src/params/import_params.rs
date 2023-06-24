// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use crate::{
	arg_enums::{
		ExecutionStrategy, WasmExecutionMethod, WasmtimeInstantiationStrategy,
		DEFAULT_WASMTIME_INSTANTIATION_STRATEGY, DEFAULT_WASM_EXECUTION_METHOD,
	},
	params::{DatabaseParams, PruningParams},
};
use clap::Args;
use std::path::PathBuf;

/// Parameters for block import.
#[derive(Debug, Clone, Args)]
pub struct ImportParams {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub pruning_params: PruningParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub database_params: DatabaseParams,

	/// Method for executing Wasm runtime code.
	#[arg(
		long = "wasm-execution",
		value_name = "METHOD",
		value_enum,
		ignore_case = true,
		default_value_t = DEFAULT_WASM_EXECUTION_METHOD,
	)]
	pub wasm_method: WasmExecutionMethod,

	/// The WASM instantiation method to use.
	/// Only has an effect when `wasm-execution` is set to `compiled`.
	/// The copy-on-write strategies are only supported on Linux.
	/// If the copy-on-write variant of a strategy is unsupported
	/// the executor will fall back to the non-CoW equivalent.
	/// The fastest (and the default) strategy available is `pooling-copy-on-write`.
	/// The `legacy-instance-reuse` strategy is deprecated and will
	/// be removed in the future. It should only be used in case of
	/// issues with the default instantiation strategy.
	#[arg(
		long,
		value_name = "STRATEGY",
		default_value_t = DEFAULT_WASMTIME_INSTANTIATION_STRATEGY,
		value_enum,
	)]
	pub wasmtime_instantiation_strategy: WasmtimeInstantiationStrategy,

	/// Specify the path where local WASM runtimes are stored.
	/// These runtimes will override on-chain runtimes when the version matches.
	#[arg(long, value_name = "PATH")]
	pub wasm_runtime_overrides: Option<PathBuf>,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub execution_strategies: ExecutionStrategiesParams,

	/// Specify the state cache size.
	/// Providing `0` will disable the cache.
	#[arg(long, value_name = "Bytes", default_value_t = 67108864)]
	pub trie_cache_size: usize,

	/// DEPRECATED
	/// Switch to `--trie-cache-size`.
	#[arg(long)]
	state_cache_size: Option<usize>,
}

impl ImportParams {
	/// Specify the trie cache maximum size.
	pub fn trie_cache_maximum_size(&self) -> Option<usize> {
		if self.state_cache_size.is_some() {
			eprintln!("`--state-cache-size` was deprecated. Please switch to `--trie-cache-size`.");
		}

		if self.trie_cache_size == 0 {
			None
		} else {
			Some(self.trie_cache_size)
		}
	}

	/// Get the WASM execution method from the parameters
	pub fn wasm_method(&self) -> sc_service::config::WasmExecutionMethod {
		self.execution_strategies.check_usage_and_print_deprecation_warning();

		crate::execution_method_from_cli(self.wasm_method, self.wasmtime_instantiation_strategy)
	}

	/// Enable overriding on-chain WASM with locally-stored WASM
	/// by specifying the path where local WASM is stored.
	pub fn wasm_runtime_overrides(&self) -> Option<PathBuf> {
		self.wasm_runtime_overrides.clone()
	}
}

/// Execution strategies parameters.
#[derive(Debug, Clone, Args)]
pub struct ExecutionStrategiesParams {
	/// The means of execution used when calling into the runtime for importing blocks as
	/// part of an initial sync.
	#[arg(long, value_name = "STRATEGY", value_enum, ignore_case = true)]
	pub execution_syncing: Option<ExecutionStrategy>,

	/// The means of execution used when calling into the runtime for general block import
	/// (including locally authored blocks).
	#[arg(long, value_name = "STRATEGY", value_enum, ignore_case = true)]
	pub execution_import_block: Option<ExecutionStrategy>,

	/// The means of execution used when calling into the runtime while constructing blocks.
	#[arg(long, value_name = "STRATEGY", value_enum, ignore_case = true)]
	pub execution_block_construction: Option<ExecutionStrategy>,

	/// The means of execution used when calling into the runtime while using an off-chain worker.
	#[arg(long, value_name = "STRATEGY", value_enum, ignore_case = true)]
	pub execution_offchain_worker: Option<ExecutionStrategy>,

	/// The means of execution used when calling into the runtime while not syncing, importing or
	/// constructing blocks.
	#[arg(long, value_name = "STRATEGY", value_enum, ignore_case = true)]
	pub execution_other: Option<ExecutionStrategy>,

	/// The execution strategy that should be used by all execution contexts.
	#[arg(
		long,
		value_name = "STRATEGY",
		value_enum,
		ignore_case = true,
		conflicts_with_all = &[
			"execution_other",
			"execution_offchain_worker",
			"execution_block_construction",
			"execution_import_block",
			"execution_syncing",
		]
	)]
	pub execution: Option<ExecutionStrategy>,
}

impl ExecutionStrategiesParams {
	/// Check if one of the parameters is still passed and print a warning if so.
	fn check_usage_and_print_deprecation_warning(&self) {
		for (param, name) in [
			(&self.execution_syncing, "execution-syncing"),
			(&self.execution_import_block, "execution-import-block"),
			(&self.execution_block_construction, "execution-block-construction"),
			(&self.execution_offchain_worker, "execution-offchain-worker"),
			(&self.execution_other, "execution-other"),
			(&self.execution, "execution"),
		] {
			if param.is_some() {
				eprintln!(
					"CLI parameter `--{name}` has no effect anymore and will be removed in the future!"
				);
			}
		}
	}
}
