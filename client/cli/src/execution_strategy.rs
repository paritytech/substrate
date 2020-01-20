// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

#![allow(missing_docs)]

use structopt::clap::arg_enum;

arg_enum! {
	/// How to execute blocks
	#[derive(Debug, Clone, Copy, PartialEq, Eq)]
	pub enum ExecutionStrategy {
		// Execute with native build (if available, WebAssembly otherwise).
		Native,
		// Only execute with the WebAssembly build.
		Wasm,
		// Execute with both native (where available) and WebAssembly builds.
		Both,
		// Execute with the native build if possible; if it fails, then execute with WebAssembly.
		NativeElseWasm,
	}
}

impl ExecutionStrategy {
	/// Returns the variant as `'&static str`.
	pub fn as_str(&self) -> &'static str {
		match self {
			Self::Native => "Native",
			Self::Wasm => "Wasm",
			Self::Both => "Both",
			Self::NativeElseWasm => "NativeElseWasm",
		}
	}
}

/// Default value for the `--execution-syncing` parameter.
pub const DEFAULT_EXECUTION_SYNCING: ExecutionStrategy = ExecutionStrategy::NativeElseWasm;
/// Default value for the `--execution-import-block` parameter.
pub const DEFAULT_EXECUTION_IMPORT_BLOCK: ExecutionStrategy = ExecutionStrategy::NativeElseWasm;
/// Default value for the `--execution-block-construction` parameter.
pub const DEFAULT_EXECUTION_BLOCK_CONSTRUCTION: ExecutionStrategy = ExecutionStrategy::Wasm;
/// Default value for the `--execution-offchain-worker` parameter.
pub const DEFAULT_EXECUTION_OFFCHAIN_WORKER: ExecutionStrategy = ExecutionStrategy::Native;
/// Default value for the `--execution-other` parameter.
pub const DEFAULT_EXECUTION_OTHER: ExecutionStrategy = ExecutionStrategy::Native;
