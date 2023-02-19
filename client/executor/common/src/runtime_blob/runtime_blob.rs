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

use crate::error::WasmError;
use wasm_instrument::{
	export_mutable_globals,
	parity_wasm::elements::{
		deserialize_buffer, serialize, DataSegment, ExportEntry, External, Internal, MemorySection,
		MemoryType, Module, Section,
	},
};

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
		self.raw_module.data_section().map(|ds| ds.entries()).unwrap_or(&[]).to_vec()
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
		self.raw_module.import_section().map(|is| is.globals() as u32).unwrap_or(0)
	}

	/// Perform an instrumentation that makes sure that the mutable globals are exported.
	pub fn expose_mutable_globals(&mut self) {
		export_mutable_globals(&mut self.raw_module, "exported_internal_global");
	}

	/// Run a pass that instrument this module so as to introduce a deterministic stack height
	/// limit.
	///
	/// It will introduce a global mutable counter. The instrumentation will increase the counter
	/// according to the "cost" of the callee. If the cost exceeds the `stack_depth_limit` constant,
	/// the instrumentation will trap. The counter will be decreased as soon as the the callee
	/// returns.
	///
	/// The stack cost of a function is computed based on how much locals there are and the maximum
	/// depth of the wasm operand stack.
	pub fn inject_stack_depth_metering(self, stack_depth_limit: u32) -> Result<Self, WasmError> {
		let injected_module =
			wasm_instrument::inject_stack_limiter(self.raw_module, stack_depth_limit).map_err(
				|e| WasmError::Other(format!("cannot inject the stack limiter: {:?}", e)),
			)?;

		Ok(Self { raw_module: injected_module })
	}

	/// Perform an instrumentation that makes sure that a specific function `entry_point` is
	/// exported
	pub fn entry_point_exists(&self, entry_point: &str) -> bool {
		self.raw_module
			.export_section()
			.map(|e| {
				e.entries().iter().any(|e| {
					matches!(e.internal(), Internal::Function(_)) && e.field() == entry_point
				})
			})
			.unwrap_or_default()
	}

	/// Converts a WASM memory import into a memory section and exports it.
	///
	/// Does nothing if there's no memory import.
	///
	/// May return an error in case the WASM module is invalid.
	pub fn convert_memory_import_into_export(&mut self) -> Result<(), WasmError> {
		let import_section = match self.raw_module.import_section_mut() {
			Some(import_section) => import_section,
			None => return Ok(()),
		};

		let import_entries = import_section.entries_mut();
		for index in 0..import_entries.len() {
			let entry = &import_entries[index];
			let memory_ty = match entry.external() {
				External::Memory(memory_ty) => *memory_ty,
				_ => continue,
			};

			let memory_name = entry.field().to_owned();
			import_entries.remove(index);

			self.raw_module
				.insert_section(Section::Memory(MemorySection::with_entries(vec![memory_ty])))
				.map_err(|error| {
					WasmError::Other(format!(
					"can't convert a memory import into an export: failed to insert a new memory section: {}",
					error
				))
				})?;

			if self.raw_module.export_section_mut().is_none() {
				// A module without an export section is somewhat unrealistic, but let's do this
				// just in case to cover all of our bases.
				self.raw_module
					.insert_section(Section::Export(Default::default()))
					.expect("an export section can be always inserted if it doesn't exist; qed");
			}
			self.raw_module
				.export_section_mut()
				.expect("export section already existed or we just added it above, so it always exists; qed")
				.entries_mut()
				.push(ExportEntry::new(memory_name, Internal::Memory(0)));

			break
		}

		Ok(())
	}

	/// Increases the number of memory pages requested by the WASM blob by
	/// the given amount of `extra_heap_pages`.
	///
	/// Will return an error in case there is no memory section present,
	/// or if the memory section is empty.
	///
	/// Only modifies the initial size of the memory; the maximum is unmodified
	/// unless it's smaller than the initial size, in which case it will be increased
	/// so that it's at least as big as the initial size.
	pub fn add_extra_heap_pages_to_memory_section(
		&mut self,
		extra_heap_pages: u32,
	) -> Result<(), WasmError> {
		let memory_section = self
			.raw_module
			.memory_section_mut()
			.ok_or_else(|| WasmError::Other("no memory section found".into()))?;

		if memory_section.entries().is_empty() {
			return Err(WasmError::Other("memory section is empty".into()))
		}
		for memory_ty in memory_section.entries_mut() {
			let min = memory_ty.limits().initial().saturating_add(extra_heap_pages);
			let max = memory_ty.limits().maximum().map(|max| std::cmp::max(min, max));
			*memory_ty = MemoryType::new(min, max);
		}
		Ok(())
	}

	/// Returns an iterator of all globals which were exported by [`expose_mutable_globals`].
	pub(super) fn exported_internal_global_names(&self) -> impl Iterator<Item = &str> {
		let exports = self.raw_module.export_section().map(|es| es.entries()).unwrap_or(&[]);
		exports.iter().filter_map(|export| match export.internal() {
			Internal::Global(_) if export.field().starts_with("exported_internal_global") =>
				Some(export.field()),
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
		serialize(self.raw_module).expect("serializing into a vec should succeed; qed")
	}

	/// Destructure this structure into the underlying parity-wasm Module.
	pub fn into_inner(self) -> Module {
		self.raw_module
	}
}
