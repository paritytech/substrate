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

use pwasm_utils::{
	parity_wasm::elements::{
		DataSegment, Module, deserialize_buffer, serialize, Internal,
	},
	export_mutable_globals,
};
use crate::error::WasmError;

/// A bunch of information collected from a WebAssembly module.
#[derive(Clone)]
pub struct RuntimeBlob {
	raw_module: Module,
}

impl RuntimeBlob {
	/// Create `RuntimeBlob` from the given wasm code. Will attempt to decompress the code before
	/// deserializing it.
	///
	/// See [`sp_maybe_compressed_blob`] for details about decompression.
	pub fn uncompress_if_needed(wasm_code: &[u8]) -> Result<Self, WasmError> {
		use sp_maybe_compressed_blob::CODE_BLOB_BOMB_LIMIT;
		let wasm_code = sp_maybe_compressed_blob::decompress(wasm_code, CODE_BLOB_BOMB_LIMIT)
			.map_err(|e| WasmError::Other(format!("Decompression error: {:?}", e)))?;
		Self::new(&wasm_code)
	}

	/// Create `RuntimeBlob` from the given wasm code.
	///
	/// Returns `Err` if the wasm code cannot be deserialized.
	pub fn new(wasm_code: &[u8]) -> Result<Self, WasmError> {
		let raw_module: Module = deserialize_buffer(wasm_code)
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
		export_mutable_globals(&mut self.raw_module, "exported_internal_global");
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
			Internal::Global(_)
				if export.field().starts_with("exported_internal_global") =>
			{
				Some(export.field())
			}
			_ => None,
		})
	}

	/// Scans the wasm blob for the first section with the name that matches the given. Returns the
	/// contents of the custom section if found or `None` otherwise.
	pub fn custom_section_contents(&self, section_name: &str) -> Option<&[u8]> {
		self.raw_module
			.custom_sections()
			.find(|cs| cs.name() == section_name)
			.map(|cs| cs.payload())
		}

	/// Consumes this runtime blob and serializes it.
	pub fn serialize(self) -> Vec<u8> {
		serialize(self.raw_module)
			.expect("serializing into a vec should succeed; qed")
	}

	/// Destructure this structure into the underlying parity-wasm Module.
	pub fn into_inner(self) -> Module {
		self.raw_module
	}
}
