// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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
		ExecutionStrategy, WasmExecutionMethod, DEFAULT_EXECUTION_BLOCK_CONSTRUCTION,
		DEFAULT_EXECUTION_IMPORT_BLOCK, DEFAULT_EXECUTION_IMPORT_BLOCK_VALIDATOR,
		DEFAULT_EXECUTION_OFFCHAIN_WORKER, DEFAULT_EXECUTION_OTHER, DEFAULT_EXECUTION_SYNCING,
		DEFAULT_WASM_EXECUTION_METHOD,
	},
	params::{DatabaseParams, PruningParams},
};
use clap::Args;
use sc_client_api::execution_extensions::ExecutionStrategies;
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

	/// Force start with unsafe pruning settings.
	///
	/// When running as a validator it is highly recommended to disable state
	/// pruning (i.e. 'archive') which is the default. The node will refuse to
	/// start as a validator if pruning is enabled unless this option is set.
	#[clap(long)]
	pub unsafe_pruning: bool,

	/// Method for executing Wasm runtime code.
	#[clap(
		long = "wasm-execution",
		value_name = "METHOD",
		possible_values = WasmExecutionMethod::variants(),
		ignore_case = true,
		default_value = DEFAULT_WASM_EXECUTION_METHOD,
	)]
	pub wasm_method: WasmExecutionMethod,

	/// Specify the path where local WASM runtimes are stored.
	///
	/// These runtimes will override on-chain runtimes when the version matches.
	#[clap(long, value_name = "PATH", parse(from_os_str))]
	pub wasm_runtime_overrides: Option<PathBuf>,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub execution_strategies: ExecutionStrategiesParams,

	/// Specify the state cache size.
	#[clap(long, value_name = "Bytes", default_value = "67108864")]
	pub state_cache_size: usize,
}

impl ImportParams {
	/// Specify the state cache size.
	pub fn state_cache_size(&self) -> usize {
		self.state_cache_size
	}

	/// Get the WASM execution method from the parameters
	pub fn wasm_method(&self) -> sc_service::config::WasmExecutionMethod {
		self.wasm_method.into()
	}

	/// Enable overriding on-chain WASM with locally-stored WASM
	/// by specifying the path where local WASM is stored.
	pub fn wasm_runtime_overrides(&self) -> Option<PathBuf> {
		self.wasm_runtime_overrides.clone()
	}

	/// Get execution strategies for the parameters
	pub fn execution_strategies(&self, is_dev: bool, is_validator: bool) -> ExecutionStrategies {
		let exec = &self.execution_strategies;
		let exec_all_or = |strat: Option<ExecutionStrategy>, default: ExecutionStrategy| {
			let default = if is_dev { ExecutionStrategy::Native } else { default };

			exec.execution.unwrap_or_else(|| strat.unwrap_or(default)).into()
		};

		let default_execution_import_block = if is_validator {
			DEFAULT_EXECUTION_IMPORT_BLOCK_VALIDATOR
		} else {
			DEFAULT_EXECUTION_IMPORT_BLOCK
		};

		ExecutionStrategies {
			syncing: exec_all_or(exec.execution_syncing, DEFAULT_EXECUTION_SYNCING),
			importing: exec_all_or(exec.execution_import_block, default_execution_import_block),
			block_construction: exec_all_or(
				exec.execution_block_construction,
				DEFAULT_EXECUTION_BLOCK_CONSTRUCTION,
			),
			offchain_worker: exec_all_or(
				exec.execution_offchain_worker,
				DEFAULT_EXECUTION_OFFCHAIN_WORKER,
			),
			other: exec_all_or(exec.execution_other, DEFAULT_EXECUTION_OTHER),
		}
	}
}

/// Execution strategies parameters.
#[derive(Debug, Clone, Args)]
pub struct ExecutionStrategiesParams {
	/// The means of execution used when calling into the runtime for importing blocks as
	/// part of an initial sync.
	#[clap(long, value_name = "STRATEGY", arg_enum, ignore_case = true)]
	pub execution_syncing: Option<ExecutionStrategy>,

	/// The means of execution used when calling into the runtime for general block import
	/// (including locally authored blocks).
	#[clap(long, value_name = "STRATEGY", arg_enum, ignore_case = true)]
	pub execution_import_block: Option<ExecutionStrategy>,

	/// The means of execution used when calling into the runtime while constructing blocks.
	#[clap(long, value_name = "STRATEGY", arg_enum, ignore_case = true)]
	pub execution_block_construction: Option<ExecutionStrategy>,

	/// The means of execution used when calling into the runtime while using an off-chain worker.
	#[clap(long, value_name = "STRATEGY", arg_enum, ignore_case = true)]
	pub execution_offchain_worker: Option<ExecutionStrategy>,

	/// The means of execution used when calling into the runtime while not syncing, importing or
	/// constructing blocks.
	#[clap(long, value_name = "STRATEGY", arg_enum, ignore_case = true)]
	pub execution_other: Option<ExecutionStrategy>,

	/// The execution strategy that should be used by all execution contexts.
	#[clap(
		long,
		value_name = "STRATEGY",
		arg_enum,
		ignore_case = true,
		conflicts_with_all = &[
			"execution-other",
			"execution-offchain-worker",
			"execution-block-construction",
			"execution-import-block",
			"execution-syncing",
		]
	)]
	pub execution: Option<ExecutionStrategy>,
}
