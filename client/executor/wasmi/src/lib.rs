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

//! This crate provides an implementation of `WasmModule` that is baked by wasmi.

use sc_executor_common::{
	error::WasmError,
	runtime_blob::RuntimeBlob,
	wasm_runtime::{HeapAllocStrategy, WasmModule}
};
use sp_wasm_interface::Function;
use std::boxed::Box;

#[cfg(not(feature = "enabled"))]
pub fn create_runtime(
	_blob: RuntimeBlob,
	_heap_alloc_strategy: HeapAllocStrategy,
	_host_functions: Vec<&'static dyn Function>,
	_allow_missing_func_imports: bool,
) -> Result<Box<dyn WasmModule>, WasmError> {
    Err(WasmError::Other("Execution of wasm runtime with an interpreter disabled. Please recompile the node with enabled 'interpreted-wasm' feature if necessary.".into()))
}

#[cfg(feature = "enabled")]
mod wasmi;

#[cfg(feature = "enabled")]
pub use wasmi::create_runtime;
