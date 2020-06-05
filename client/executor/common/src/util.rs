// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! A set of utilities for resetting a wasm instance to its initial state.

use crate::error::{self, Error};
use std::mem;
use parity_wasm::elements::{deserialize_buffer, DataSegment, Instruction, Module as RawModule};

/// A bunch of information collected from a WebAssembly module.
pub struct WasmModuleInfo {
	raw_module: RawModule,
}

impl WasmModuleInfo {
	/// Create `WasmModuleInfo` from the given wasm code.
	///
	/// Returns `None` if the wasm code cannot be deserialized.
	pub fn new(wasm_code: &[u8]) -> Option<Self> {
		let raw_module: RawModule = deserialize_buffer(wasm_code).ok()?;
		Some(Self { raw_module })
	}

	/// Extract the data segments from the given wasm code.
	///
	/// Returns `Err` if the given wasm code cannot be deserialized.
	fn data_segments(&self) -> Vec<DataSegment> {
		self.raw_module
			.data_section()
			.map(|ds| ds.entries())
			.unwrap_or(&[])
			.to_vec()
	}

	/// The number of globals defined in locally in this module.
	pub fn declared_globals_count(&self) -> u32 {
		self.raw_module
			.global_section()
			.map(|gs| gs.entries().len() as u32)
			.unwrap_or(0)
	}

	/// The number of imports of globals.
	pub fn imported_globals_count(&self) -> u32 {
		self.raw_module
			.import_section()
			.map(|is| is.globals() as u32)
			.unwrap_or(0)
	}
}

/// This is a snapshot of data segments specialzied for a particular instantiation.
///
/// Note that this assumes that no mutable globals are used.
#[derive(Clone)]
pub struct DataSegmentsSnapshot {
	/// The list of data segments represented by (offset, contents).
	data_segments: Vec<(u32, Vec<u8>)>,
}

impl DataSegmentsSnapshot {
	/// Create a snapshot from the data segments from the module.
	pub fn take(module: &WasmModuleInfo) -> error::Result<Self> {
		let data_segments = module
			.data_segments()
			.into_iter()
			.map(|mut segment| {
				// Just replace contents of the segment since the segments will be discarded later
				// anyway.
				let contents = mem::replace(segment.value_mut(), vec![]);

				let init_expr = match segment.offset() {
					Some(offset) => offset.code(),
					// Return if the segment is passive
					None => return Err(Error::from("Shared memory is not supported".to_string())),
				};

				// [op, End]
				if init_expr.len() != 2 {
					return Err(Error::from(
						"initializer expression can have only up to 2 expressions in wasm 1.0"
							.to_string(),
					));
				}
				let offset = match &init_expr[0] {
					Instruction::I32Const(v) => *v as u32,
					Instruction::GetGlobal(_) => {
						// In a valid wasm file, initializer expressions can only refer imported
						// globals.
						//
						// At the moment of writing the Substrate Runtime Interface does not provide
						// any globals. There is nothing that prevents us from supporting this
						// if/when we gain those.
						return Err(Error::from(
							"Imported globals are not supported yet".to_string(),
						));
					}
					insn => {
						return Err(Error::from(format!(
							"{:?} is not supported as initializer expression in wasm 1.0",
							insn
						)))
					}
				};

				Ok((offset, contents))
			})
			.collect::<error::Result<Vec<_>>>()?;

		Ok(Self { data_segments })
	}

	/// Apply the given snapshot to a linear memory.
	///
	/// Linear memory interface is represented by a closure `memory_set`.
	pub fn apply<E>(
		&self,
		mut memory_set: impl FnMut(u32, &[u8]) -> Result<(), E>,
	) -> Result<(), E> {
		for (offset, contents) in &self.data_segments {
			memory_set(*offset, contents)?;
		}
		Ok(())
	}
}
