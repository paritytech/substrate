// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Defines data and logic needed for interaction with an WebAssembly instance of a substrate
//! runtime module.

use crate::runtime::{Store, StoreData};
use sc_executor_common::{
	error::{Error, Result},
	wasm_runtime::InvokeMethod,
};
use sp_wasm_interface::{HostFunctions, Pointer, Value, WordSize};
use wasmtime::{
	AsContext, AsContextMut, Extern, Func, Global, Instance, Memory, Module, Table, Val,
};

/// Invoked entrypoint format.
pub enum EntryPointType {
	/// Direct call.
	///
	/// Call is made by providing only payload reference and length.
	Direct { entrypoint: wasmtime::TypedFunc<(u32, u32), u64> },
	/// Indirect call.
	///
	/// Call is made by providing payload reference and length, and extra argument
	/// for advanced routing.
	Wrapped {
		/// The extra argument passed to the runtime. It is typically a wasm function pointer.
		func: u32,
		dispatcher: wasmtime::TypedFunc<(u32, u32, u32), u64>,
	},
}

/// Wasm blob entry point.
pub struct EntryPoint {
	call_type: EntryPointType,
}

impl EntryPoint {
	/// Call this entry point.
	pub fn call(
		&self,
		ctx: impl AsContextMut,
		data_ptr: Pointer<u8>,
		data_len: WordSize,
	) -> Result<u64> {
		let data_ptr = u32::from(data_ptr);
		let data_len = u32::from(data_len);

		fn handle_trap(err: wasmtime::Trap) -> Error {
			Error::from(format!("Wasm execution trapped: {}", err))
		}

		match self.call_type {
			EntryPointType::Direct { ref entrypoint } =>
				entrypoint.call(ctx, (data_ptr, data_len)).map_err(handle_trap),
			EntryPointType::Wrapped { func, ref dispatcher } =>
				dispatcher.call(ctx, (func, data_ptr, data_len)).map_err(handle_trap),
		}
	}

	pub fn direct(
		func: wasmtime::Func,
		ctx: impl AsContext,
	) -> std::result::Result<Self, &'static str> {
		let entrypoint = func
			.typed::<(u32, u32), u64, _>(ctx)
			.map_err(|_| "Invalid signature for direct entry point")?
			.clone();
		Ok(Self { call_type: EntryPointType::Direct { entrypoint } })
	}

	pub fn wrapped(
		dispatcher: wasmtime::Func,
		func: u32,
		ctx: impl AsContext,
	) -> std::result::Result<Self, &'static str> {
		let dispatcher = dispatcher
			.typed::<(u32, u32, u32), u64, _>(ctx)
			.map_err(|_| "Invalid signature for wrapped entry point")?
			.clone();
		Ok(Self { call_type: EntryPointType::Wrapped { func, dispatcher } })
	}
}

/// Wrap the given WebAssembly Instance of a wasm module with Substrate-runtime.
///
/// This struct is a handy wrapper around a wasmtime `Instance` that provides substrate specific
/// routines.
pub struct InstanceWrapper {
	instance: Instance,
	memory: Memory,
	store: Store,
}

fn extern_memory(extern_: &Extern) -> Option<&Memory> {
	match extern_ {
		Extern::Memory(mem) => Some(mem),
		_ => None,
	}
}

fn extern_global(extern_: &Extern) -> Option<&Global> {
	match extern_ {
		Extern::Global(glob) => Some(glob),
		_ => None,
	}
}

fn extern_table(extern_: &Extern) -> Option<&Table> {
	match extern_ {
		Extern::Table(table) => Some(table),
		_ => None,
	}
}

fn extern_func(extern_: &Extern) -> Option<&Func> {
	match extern_ {
		Extern::Func(func) => Some(func),
		_ => None,
	}
}

impl InstanceWrapper {
	/// Create a new instance wrapper from the given wasm module.
	pub fn new<H>(
		module: &Module,
		heap_pages: u64,
		allow_missing_func_imports: bool,
		max_memory_size: Option<usize>,
	) -> Result<Self>
	where
		H: HostFunctions,
	{
		let limits = if let Some(max_memory_size) = max_memory_size {
			wasmtime::StoreLimitsBuilder::new().memory_size(max_memory_size).build()
		} else {
			Default::default()
		};

		let mut store = Store::new(
			module.engine(),
			StoreData { limits, host_state: None, memory: None, table: None },
		);
		if max_memory_size.is_some() {
			store.limiter(|s| &mut s.limits);
		}

		// Scan all imports, find the matching host functions, and create stubs that adapt arguments
		// and results.
		let imports = crate::imports::resolve_imports::<H>(
			&mut store,
			module,
			heap_pages,
			allow_missing_func_imports,
		)?;

		let instance = Instance::new(&mut store, module, &imports.externs)
			.map_err(|e| Error::from(format!("cannot instantiate: {}", e)))?;

		let memory = match imports.memory_import_index {
			Some(memory_idx) => extern_memory(&imports.externs[memory_idx])
				.expect("only memory can be at the `memory_idx`; qed")
				.clone(),
			None => {
				let memory = get_linear_memory(&instance, &mut store)?;
				if !memory.grow(&mut store, heap_pages).is_ok() {
					return Err("failed top increase the linear memory size".into())
				}
				memory
			},
		};

		let table = get_table(&instance, &mut store);

		store.data_mut().memory = Some(memory);
		store.data_mut().table = table;

		Ok(Self { instance, memory, store })
	}

	/// Resolves a substrate entrypoint by the given name.
	///
	/// An entrypoint must have a signature `(i32, i32) -> i64`, otherwise this function will return
	/// an error.
	pub fn resolve_entrypoint(&mut self, method: InvokeMethod) -> Result<EntryPoint> {
		Ok(match method {
			InvokeMethod::Export(method) => {
				// Resolve the requested method and verify that it has a proper signature.
				let export =
					self.instance.get_export(&mut self.store, method).ok_or_else(|| {
						Error::from(format!("Exported method {} is not found", method))
					})?;
				let func = extern_func(&export)
					.ok_or_else(|| Error::from(format!("Export {} is not a function", method)))?
					.clone();
				EntryPoint::direct(func, &self.store).map_err(|_| {
					Error::from(format!("Exported function '{}' has invalid signature.", method))
				})?
			},
			InvokeMethod::Table(func_ref) => {
				let table = self
					.instance
					.get_table(&mut self.store, "__indirect_function_table")
					.ok_or(Error::NoTable)?;
				let val = table
					.get(&mut self.store, func_ref)
					.ok_or(Error::NoTableEntryWithIndex(func_ref))?;
				let func = val
					.funcref()
					.ok_or(Error::TableElementIsNotAFunction(func_ref))?
					.ok_or(Error::FunctionRefIsNull(func_ref))?
					.clone();

				EntryPoint::direct(func, &self.store).map_err(|_| {
					Error::from(format!(
						"Function @{} in exported table has invalid signature for direct call.",
						func_ref,
					))
				})?
			},
			InvokeMethod::TableWithWrapper { dispatcher_ref, func } => {
				let table = self
					.instance
					.get_table(&mut self.store, "__indirect_function_table")
					.ok_or(Error::NoTable)?;
				let val = table
					.get(&mut self.store, dispatcher_ref)
					.ok_or(Error::NoTableEntryWithIndex(dispatcher_ref))?;
				let dispatcher = val
					.funcref()
					.ok_or(Error::TableElementIsNotAFunction(dispatcher_ref))?
					.ok_or(Error::FunctionRefIsNull(dispatcher_ref))?
					.clone();

				EntryPoint::wrapped(dispatcher, func, &self.store).map_err(|_| {
					Error::from(format!(
						"Function @{} in exported table has invalid signature for wrapped call.",
						dispatcher_ref,
					))
				})?
			},
		})
	}

	/// Reads `__heap_base: i32` global variable and returns it.
	///
	/// If it doesn't exist, not a global or of not i32 type returns an error.
	pub fn extract_heap_base(&mut self) -> Result<u32> {
		let heap_base_export = self
			.instance
			.get_export(&mut self.store, "__heap_base")
			.ok_or_else(|| Error::from("__heap_base is not found"))?;

		let heap_base_global = extern_global(&heap_base_export)
			.ok_or_else(|| Error::from("__heap_base is not a global"))?;

		let heap_base = heap_base_global
			.get(&mut self.store)
			.i32()
			.ok_or_else(|| Error::from("__heap_base is not a i32"))?;

		Ok(heap_base as u32)
	}

	/// Get the value from a global with the given `name`.
	pub fn get_global_val(&mut self, name: &str) -> Result<Option<Value>> {
		let global = match self.instance.get_export(&mut self.store, name) {
			Some(global) => global,
			None => return Ok(None),
		};

		let global = extern_global(&global).ok_or_else(|| format!("`{}` is not a global", name))?;

		match global.get(&mut self.store) {
			Val::I32(val) => Ok(Some(Value::I32(val))),
			Val::I64(val) => Ok(Some(Value::I64(val))),
			Val::F32(val) => Ok(Some(Value::F32(val))),
			Val::F64(val) => Ok(Some(Value::F64(val))),
			_ => Err("Unknown value type".into()),
		}
	}

	/// Get a global with the given `name`.
	pub fn get_global(&mut self, name: &str) -> Option<wasmtime::Global> {
		self.instance.get_global(&mut self.store, name)
	}
}

/// Extract linear memory instance from the given instance.
fn get_linear_memory(instance: &Instance, ctx: impl AsContextMut) -> Result<Memory> {
	let memory_export = instance
		.get_export(ctx, "memory")
		.ok_or_else(|| Error::from("memory is not exported under `memory` name"))?;

	let memory = extern_memory(&memory_export)
		.ok_or_else(|| Error::from("the `memory` export should have memory type"))?
		.clone();

	Ok(memory)
}

/// Extract the table from the given instance if any.
fn get_table(instance: &Instance, ctx: &mut Store) -> Option<Table> {
	instance
		.get_export(ctx, "__indirect_function_table")
		.as_ref()
		.and_then(extern_table)
		.cloned()
}

/// Functions related to memory.
impl InstanceWrapper {
	/// Returns the pointer to the first byte of the linear memory for this instance.
	pub fn base_ptr(&self) -> *const u8 {
		self.memory.data_ptr(&self.store)
	}

	/// If possible removes physical backing from the allocated linear memory which
	/// leads to returning the memory back to the system; this also zeroes the memory
	/// as a side-effect.
	pub fn decommit(&mut self) {
		if self.memory.data_size(&self.store) == 0 {
			return
		}

		cfg_if::cfg_if! {
			if #[cfg(target_os = "linux")] {
				use std::sync::Once;

				unsafe {
					let ptr = self.memory.data_ptr(&self.store);
					let len = self.memory.data_size(&self.store);

					// Linux handles MADV_DONTNEED reliably. The result is that the given area
					// is unmapped and will be zeroed on the next pagefault.
					if libc::madvise(ptr as _, len, libc::MADV_DONTNEED) != 0 {
						static LOGGED: Once = Once::new();
						LOGGED.call_once(|| {
							log::warn!(
								"madvise(MADV_DONTNEED) failed: {}",
								std::io::Error::last_os_error(),
							);
						});
					} else {
						return;
					}
				}
			}
		}

		// If we're on an unsupported OS or the memory couldn't have been
		// decommited for some reason then just manually zero it out.
		self.memory.data_mut(self.store.as_context_mut()).fill(0);
	}

	pub(crate) fn store(&self) -> &Store {
		&self.store
	}

	pub(crate) fn store_mut(&mut self) -> &mut Store {
		&mut self.store
	}
}
