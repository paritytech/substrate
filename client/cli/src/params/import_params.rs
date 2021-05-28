// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

use crate::arg_enums::WasmExecutionMethod;
use crate::params::DatabaseParams;
use crate::params::PruningParams;
use structopt::StructOpt;
use std::path::PathBuf;

#[cfg(feature = "wasmtime")]
const WASM_METHOD_DEFAULT: &str = "Compiled";

#[cfg(not(feature = "wasmtime"))]
const WASM_METHOD_DEFAULT: &str = "interpreted-i-know-what-i-do";

/// Parameters for block import.
#[derive(Debug, StructOpt, Clone)]
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
		possible_values = &WasmExecutionMethod::variants(),
		case_insensitive = true,
		default_value = WASM_METHOD_DEFAULT
	)]
	pub wasm_method: WasmExecutionMethod,

	/// Specify the path where local WASM runtimes are stored.
	///
	/// These runtimes will override on-chain runtimes when the version matches.
	#[structopt(long, value_name = "PATH", parse(from_os_str))]
	pub wasm_runtime_overrides: Option<PathBuf>,

	/// Specify the state cache size.
	#[structopt(
		long = "state-cache-size",
		value_name = "Bytes",
		default_value = "67108864"
	)]
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
}
