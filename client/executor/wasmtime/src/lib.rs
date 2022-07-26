// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Defines a `WasmRuntime` that uses the Wasmtime JIT to execute.
//!
//! You can choose a profiling strategy at runtime with
//! environment variable `WASMTIME_PROFILING_STRATEGY`:
//!
//! | `WASMTIME_PROFILING_STRATEGY` | Effect |
//! |-------------|-------------------------|
//! | undefined   | No profiling            |
//! | `"jitdump"` | jitdump profiling       |
//! | other value | No profiling (warning)  |

mod host;
mod imports;
mod instance_wrapper;
mod runtime;
mod util;

#[cfg(test)]
mod tests;

pub use runtime::{
	create_runtime, create_runtime_from_artifact, prepare_runtime_artifact, Config,
	DeterministicStackLimit, InstantiationStrategy, Semantics,
};
