// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Implements a cache for pre-created Wasm runtime module instances.

use crate::error::{Error, Result};
use crate::wasm_executor::WasmExecutor;
use log::trace;
use parity_codec::Decode;
use parity_wasm::elements::{deserialize_buffer, DataSegment, Instruction, Module as RawModule};
use primitives::storage::well_known_keys;
use primitives::Blake2Hasher;
use runtime_version::RuntimeVersion;
use state_machine::Externalities;
use std::collections::HashMap;
use std::mem;
use wasmi::{Module as WasmModule, ModuleRef as WasmModuleInstanceRef, RuntimeValue};

/// A runtime along with its version and initial state snapshot.
#[derive(Clone)]
enum RuntimePreproc {
	InvalidCode,
	ValidCode {
		/// A wasm module instance.
		instance: WasmModuleInstanceRef,
		/// Runtime version according to `Core_version`.
		///
		/// Can be `None` if the runtime doesn't expose this function.
		version: Option<RuntimeVersion>,
		/// The snapshot of the instance's state taken just after the instantiation.
		state_snapshot: StateSnapshot,
	},
}

/// A state snapshot of an instance taken just after instantiation.
///
/// It is used for restoring the state of the module after execution.
#[derive(Clone)]
struct StateSnapshot {
	/// The offset and the contents of the memory segments that should be copied at
	/// to restore the snapshot.
	data_segments: Vec<(u32, Vec<u8>)>,
	/// The list of all global variables of the module in their sequential order.
	global_mut_values: Vec<RuntimeValue>,
	heap_pages: u32,
}

impl StateSnapshot {
	fn take(
		module_instance: &WasmModuleInstanceRef,
		data_segments: Vec<DataSegment>,
		heap_pages: u32,
	) -> Option<Self> {
		let mut prepared_segments = Vec::with_capacity(data_segments.len());
		for mut segment in data_segments {
			// Just replace contents of the segment since the segments will be discarded later
			// anyway.
			let contents = mem::replace(segment.value_mut(), vec![]);

			let init_expr = segment.offset().code();
			// [op, End]
			if init_expr.len() != 2 {
				return None;
			}
			let offset = match init_expr[0] {
				Instruction::I32Const(v) => v as u32,
				Instruction::GetGlobal(idx) => {
					let global_val = module_instance.globals().get(idx as usize)?.get();
					match global_val {
						RuntimeValue::I32(v) => v as u32,
						_ => return None,
					}
				}
				_ => return None,
			};
			prepared_segments.push((offset, contents))
		}

		// Collect all values of mutable globals.
		let global_mut_values = module_instance
			.globals()
			.iter()
			.filter(|g| g.is_mutable())
			.map(|g| g.get())
			.collect();

		Some(Self {
			data_segments: prepared_segments,
			global_mut_values,
			heap_pages,
		})
	}

	/// Reset the runtime instance to the initial version by restoring
	/// the preserved memory and globals.
	fn apply(&self, instance: &WasmModuleInstanceRef) {
		let mem = instance
			.export_by_name("memory")
			.expect("export identifier 'memory' is hardcoded and will always exist; qed");
		match mem {
			wasmi::ExternVal::Memory(memory_ref) => {
				let amount = self.heap_pages as usize * wasmi::LINEAR_MEMORY_PAGE_SIZE.0;
				// TODO:
				memory_ref.clear(0, 0, amount).expect("");

				for (offset, contents) in &self.data_segments {
					// TODO: expect
					memory_ref.set(*offset, contents).expect("");
				}
			}
			_ => unreachable!("memory export always exists wasm module; qed"),
		}

		// Restore the values of mutable globals.
		for (global_ref, global_val) in instance
			.globals()
			.iter()
			.filter(|g| g.is_mutable())
			.zip(self.global_mut_values.iter())
		{
			// TODO: Can we guarantee that the instance is the same?
			global_ref.set(*global_val).expect(
				"the instance should be the same as used for preserving;
				we iterate the same way it as we do it for preserving values;
				the types should be the same;
				all the values are mutable;
				qed
				",
			);
		}
	}
}

/// Default num of pages for the heap
const DEFAULT_HEAP_PAGES: u64 = 1024;

/// When an instance is requested for the first time it is added to this
/// cache. Furthermore its initial memory is preserved here. Follow-up
/// requests to fetch a runtime return this one instance with the memory
/// reset to the initial memory. So, one runtime instance is reused for
/// every fetch request.
pub struct RuntimesCache {
	// TODO: Consider LRU.
	/// A cache of runtime instances along with metadata, ready to be reused.
	///
	/// Instances are keyed by the hash of their code.
	instances: HashMap<[u8; 32], RuntimePreproc>,
}

impl RuntimesCache {
	/// Creates a new instance of a runtimes cache.
	pub fn new() -> RuntimesCache {
		RuntimesCache {
			instances: HashMap::new(),
		}
	}

	/// Fetches an instance of the runtime.
	///
	/// On first use we create a new runtime instance, save it to the cache
	/// and persist its initial memory.
	///
	/// Each subsequent request will return this instance, with its memory restored
	/// to the persisted initial memory. Thus, we reuse one single runtime instance
	/// for every `fetch_runtime` invocation.
	///
	/// # Parameters
	///
	/// `wasm_executor`- Rust wasm executor. Executes the provided code in a
	/// sandboxed Wasm runtime.
	///
	/// `ext` - Externalities to use for the runtime. This is used for setting
	/// up an initial runtime instance. The parameter is only needed for calling
	/// into the Wasm module to find out the `Core_version`.
	///
	/// `initial_heap_pages` - Number of 64KB pages to allocate for Wasm execution.
	/// Defaults to `DEFAULT_HEAP_PAGES` if `None` is provided.
	///
	/// # Return value
	///
	/// If no error occurred a tuple `(wasmi::ModuleRef, Option<RuntimeVersion>)` is
	/// returned. `RuntimeVersion` is contained if the call to `Core_version` returned
	/// a version.
	///
	/// In case of failure one of two errors can be returned:
	///
	/// `Err::InvalidCode` is returned for runtime code issues.
	///
	/// `Error::InvalidMemoryReference` is returned if no memory export with the
	/// identifier `memory` can be found in the runtime.
	pub fn fetch_runtime<E: Externalities<Blake2Hasher>>(
		&mut self,
		wasm_executor: &WasmExecutor,
		ext: &mut E,
		initial_heap_pages: Option<u64>,
	) -> Result<(WasmModuleInstanceRef, Option<RuntimeVersion>)> {
		let code_hash = match ext.original_storage_hash(well_known_keys::CODE) {
			Some(code_hash) => code_hash,
			None => return Err(Error::InvalidCode),
		};

		let runtime_preproc = self.instances.entry(code_hash.into()).or_insert_with(|| {
			trace!(target: "runtimes_cache", "no instance found in cache, creating now.");
			Self::create_wasm_instance(wasm_executor, ext, initial_heap_pages)
		});

		match *runtime_preproc {
			RuntimePreproc::InvalidCode => Err(Error::InvalidCode),
			RuntimePreproc::ValidCode {
				ref instance,
				ref version,
				ref state_snapshot,
				..
			} => {
				state_snapshot.apply(&instance);
				Ok((instance.clone(), version.clone()))
			}
		}
	}

	fn create_wasm_instance<E: Externalities<Blake2Hasher>>(
		wasm_executor: &WasmExecutor,
		ext: &mut E,
		initial_heap_pages: Option<u64>,
	) -> RuntimePreproc {
		let code = match ext.original_storage(well_known_keys::CODE) {
			Some(code) => code,
			None => return RuntimePreproc::InvalidCode,
		};

		// Extract the data segments from the wasm code.
		let data_segments = match extract_data_segments(&code) {
			Some(data_segments) => data_segments,
			None => return RuntimePreproc::InvalidCode,
		};

		let heap_pages = ext
			.storage(well_known_keys::HEAP_PAGES)
			.and_then(|pages| u64::decode(&mut &pages[..]))
			.or(initial_heap_pages)
			.unwrap_or(DEFAULT_HEAP_PAGES);

		match WasmModule::from_buffer(code)
			.map_err(|_| Error::InvalidCode)
			.and_then(|module| WasmExecutor::instantiate_module(ext, heap_pages as usize, &module))
		{
			Ok(instance) => {
				// Take state snapshot before executing anything.
				let state_snapshot =
					match StateSnapshot::take(&instance, data_segments, heap_pages as u32) {
						Some(snapshot) => snapshot,
						None => return RuntimePreproc::InvalidCode,
					};

				let version = wasm_executor
					.call_in_wasm_module(ext, &instance, "Core_version", &[])
					.ok()
					.and_then(|v| RuntimeVersion::decode(&mut v.as_slice()));
				RuntimePreproc::ValidCode {
					instance,
					version,
					state_snapshot,
				}
			}
			Err(e) => {
				trace!(target: "runtimes_cache", "Invalid code presented to executor ({:?})", e);
				RuntimePreproc::InvalidCode
			}
		}
	}
}

/// Extract the data segments in the given wasm code.
///
/// Returns `Err` if the given wasm code cannot be deserialized.
fn extract_data_segments(wasm_code: &[u8]) -> Option<Vec<DataSegment>> {
	let raw_module: RawModule = deserialize_buffer(wasm_code).ok()?;
	let segments = raw_module
		.data_section()
		.map(|ds| ds.entries())
		.unwrap_or(&[])
		.to_vec();
	Some(segments)
}
