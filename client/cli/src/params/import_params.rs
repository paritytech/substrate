// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

use crate::arg_enums::{
	ExecutionStrategy, TracingReceiver, WasmExecutionMethod, DEFAULT_EXECUTION_BLOCK_CONSTRUCTION,
	DEFAULT_EXECUTION_IMPORT_BLOCK, DEFAULT_EXECUTION_IMPORT_BLOCK_VALIDATOR,
	DEFAULT_EXECUTION_OFFCHAIN_WORKER, DEFAULT_EXECUTION_OTHER, DEFAULT_EXECUTION_SYNCING,
};
use crate::params::DatabaseParams;
use crate::params::PruningParams;
use sc_client_api::execution_extensions::ExecutionStrategies;
use structopt::StructOpt;

/// Parameters for block import.
#[derive(Debug, StructOpt)]
pub struct ImportParams {
	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pruning_params: PruningParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub database_params: DatabaseParams,

	/// Force start with unsafe pruning settings.
	///
	/// When running as a validator it is highly recommended to disable state
	/// pruning (i.e. 'archive') which is the default. The node will refuse to
	/// start as a validator if pruning is enabled unless this option is set.
	#[structopt(long = "unsafe-pruning")]
	pub unsafe_pruning: bool,

	/// Method for executing Wasm runtime code.
	#[structopt(
		long = "wasm-execution",
		value_name = "METHOD",
		possible_values = &WasmExecutionMethod::enabled_variants(),
		case_insensitive = true,
		default_value = "Interpreted"
	)]
	pub wasm_method: WasmExecutionMethod,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub execution_strategies: ExecutionStrategiesParams,

	/// Specify the state cache size.
	#[structopt(
		long = "state-cache-size",
		value_name = "Bytes",
		default_value = "67108864"
	)]
	pub state_cache_size: usize,

	/// Comma separated list of targets for tracing.
	#[structopt(long = "tracing-targets", value_name = "TARGETS")]
	pub tracing_targets: Option<String>,

	/// Receiver to process tracing messages.
	#[structopt(
		long = "tracing-receiver",
		value_name = "RECEIVER",
		possible_values = &TracingReceiver::variants(),
		case_insensitive = true,
		default_value = "Log"
	)]
	pub tracing_receiver: TracingReceiver,
}

impl ImportParams {
	/// Receiver to process tracing messages.
	pub fn tracing_receiver(&self) -> sc_service::TracingReceiver {
		self.tracing_receiver.clone().into()
	}

	/// Comma separated list of targets for tracing.
	pub fn tracing_targets(&self) -> Option<String> {
		self.tracing_targets.clone()
	}

	/// Specify the state cache size.
	pub fn state_cache_size(&self) -> usize {
		self.state_cache_size
	}

	/// Get the WASM execution method from the parameters
	pub fn wasm_method(&self) -> sc_service::config::WasmExecutionMethod {
		self.wasm_method.into()
	}

	/// Get execution strategies for the parameters
	pub fn execution_strategies(&self, is_dev: bool, is_validator: bool) -> ExecutionStrategies {
		let exec = &self.execution_strategies;
		let exec_all_or = |strat: Option<ExecutionStrategy>, default: ExecutionStrategy| {
			let default = if is_dev {
				ExecutionStrategy::Native
			} else {
				default
			};

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
			block_construction:
				exec_all_or(exec.execution_block_construction, DEFAULT_EXECUTION_BLOCK_CONSTRUCTION),
			offchain_worker:
				exec_all_or(exec.execution_offchain_worker, DEFAULT_EXECUTION_OFFCHAIN_WORKER),
			other: exec_all_or(exec.execution_other, DEFAULT_EXECUTION_OTHER),
		}
	}
}

/// Execution strategies parameters.
#[derive(Debug, StructOpt)]
pub struct ExecutionStrategiesParams {
	/// The means of execution used when calling into the runtime for importing blocks as
	/// part of an initial sync.
	#[structopt(
		long = "execution-syncing",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
	)]
	pub execution_syncing: Option<ExecutionStrategy>,

	/// The means of execution used when calling into the runtime for general block import
	/// (including locally authored blocks).
	#[structopt(
		long = "execution-import-block",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
	)]
	pub execution_import_block: Option<ExecutionStrategy>,

	/// The means of execution used when calling into the runtime while constructing blocks.
	#[structopt(
		long = "execution-block-construction",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
	)]
	pub execution_block_construction: Option<ExecutionStrategy>,

	/// The means of execution used when calling into the runtime while using an off-chain worker.
	#[structopt(
		long = "execution-offchain-worker",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
	)]
	pub execution_offchain_worker: Option<ExecutionStrategy>,

	/// The means of execution used when calling into the runtime while not syncing, importing or constructing blocks.
	#[structopt(
		long = "execution-other",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
	)]
	pub execution_other: Option<ExecutionStrategy>,

	/// The execution strategy that should be used by all execution contexts.
	#[structopt(
		long = "execution",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
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
