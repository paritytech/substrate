// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use parity_wasm::elements::{DataSegment, Module as RawModule, deserialize_buffer, serialize};

use crate::error::WasmError;

/// A bunch of information collected from a WebAssembly module.
#[derive(Clone)]
pub struct RuntimeBlob {
	raw_module: RawModule,
}

impl RuntimeBlob {
	/// Create `RuntimeBlob` from the given wasm code.
	///
	/// Returns `Err` if the wasm code cannot be deserialized.
	pub fn new(wasm_code: &[u8]) -> Result<Self, WasmError> {
		let raw_module: RawModule = deserialize_buffer(wasm_code)
			.map_err(|e| WasmError::Other(format!("cannot deserialize module: {:?}", e)))?;
		Ok(Self { raw_module })
	}

	/// Extract the data segments from the given wasm code.
	pub(super) fn data_segments(&self) -> Vec<DataSegment> {
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

	/// Perform an instrumentation that makes sure that the mutable globals are exported.
	pub fn expose_mutable_globals(&mut self) {
		pwasm_utils::export_mutable_globals(&mut self.raw_module, "exported_internal_global");
	}

	/// Returns an iterator of all globals which were exported by [`expose_mutable_globals`].
	pub(super) fn exported_internal_global_names<'module>(
		&'module self,
	) -> impl Iterator<Item = &'module str> {
		let exports = self
			.raw_module
			.export_section()
			.map(|es| es.entries())
			.unwrap_or(&[]);
		exports.iter().filter_map(|export| match export.internal() {
			parity_wasm::elements::Internal::Global(_)
				if export.field().starts_with("exported_internal_global") =>
			{
				Some(export.field())
			}
			_ => None,
		})
	}

	/// Consumes this runtime blob and serializes it.
	pub fn serialize(self) -> Vec<u8> {
		serialize(self.raw_module)
			.expect("serializing into a vec should succeed; qed")
	}
}
