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

//! A set of utilities for resetting a wasm instance to its initial state.

use std::mem;
use parity_wasm::elements::{deserialize_buffer, DataSegment, Instruction, Module as RawModule};
use sp_wasm_interface::Value;

// TODO: Rename this module

pub struct DeserializedModule {
	raw_module: RawModule,
}

impl DeserializedModule {
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
	pub fn take(module: &DeserializedModule) -> Option<Self> {
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
					None => return None,
				};

				// [op, End]
				if init_expr.len() != 2 {
					return None;
				}
				let offset = match init_expr[0] {
					Instruction::I32Const(v) => v as u32,
					Instruction::GetGlobal(idx) => return None, // TODO: Not supported for now.
					_ => return None,
				};

				Some((offset, contents))
			})
			.collect::<Option<Vec<_>>>()?;

		Some(Self { data_segments })
	}

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
