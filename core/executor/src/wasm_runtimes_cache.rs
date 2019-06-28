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
use primitives::Blake2Hasher;
use primitives::storage::well_known_keys;
use runtime_version::RuntimeVersion;
use state_machine::Externalities;
use std::{ops::Deref, result};
use wasmi::{Module as WasmModule, ModuleRef as WasmModuleInstanceRef};

// Contains a preprocessed runtime instance, if it is compatible
// enough to be run natively.
#[derive(Clone)]
enum RuntimePreproc {
	InvalidCode,
	ValidCode(WasmModuleInstanceRef, Option<RuntimeVersion>),
}

#[derive(Debug)]
enum Action {
	ReuseInstance,
	InvalidCode,
	CreateNewInstance,
}

/// Default num of pages for the heap
const DEFAULT_HEAP_PAGES: u64 = 1024;

/// When an instance is requested for the first time it is added to this
/// cache. Furthermore its initial memory is preserved here. Follow-up
/// requests to fetch a runtime return this one instance with the memory
/// reset to the initial memory. So, one runtime instance is reused for
/// every fetch request.
pub struct RuntimesCache {
	runtime_instance: Option<RuntimePreproc>,
	initial_memory: Option<Vec<u8>>,
}

impl RuntimesCache {
	/// Creates a new instance of a runtimes cache.
	pub fn new() -> RuntimesCache {
		RuntimesCache {
			runtime_instance: None,
			initial_memory: None,
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
	/// `maybe_requested_version` - If `Some(RuntimeVersion)` is provided the
	/// cached instance will be checked for compatibility. In case of incompatibility
	/// the instance will be reset and a new one will be created synchronously.
	///
	/// # Return value
	///
	/// If no error occurred a tuple `(wasmi::ModuleRef, Option<RuntimeVersion>)` is
	/// returned. `RuntimeVersion` is contained if the call to `Core_version` returned
	/// a version.
	///
	/// In case of failure one of two errors can be returned:
	///
	/// `Err::InvalidCode(code)` is returned for runtime code issues.
	///
	/// `Error::InvalidMemoryReference` is returned if no memory export with the
	/// identifier `memory` can be found in the runtime.
	pub fn fetch_runtime<E: Externalities<Blake2Hasher>>(
		&mut self,
		wasm_executor: &WasmExecutor,
		ext: &mut E,
		initial_heap_pages: Option<u64>,
		maybe_requested_version: Option<&RuntimeVersion>,
	) -> Result<(WasmModuleInstanceRef, Option<RuntimeVersion>)> {
		if let None = self.runtime_instance {
			trace!(target: "runtimes_cache",
				   "no instance found in cache, creating now.");
			self.create_instance(wasm_executor, ext, initial_heap_pages)?;

			match self.runtime_instance.clone() {
				Some(RuntimePreproc::ValidCode(r, v)) => return Ok((r, v)),
				_ => unreachable!("runtime must exist here, errors would have been returned earlier; qed"),
			};
		}

		let action = match maybe_requested_version {
			None => Action::ReuseInstance,
			Some(ref requested_version) => {
				match self.runtime_instance {
					Some(RuntimePreproc::InvalidCode) => Action::InvalidCode,
					Some(RuntimePreproc::ValidCode(_, None)) => {
						// In case of a certain version being requested, but
						// the runtime in the cache not having one, we create
						// a new instance.
						Action::CreateNewInstance
					},
					Some(RuntimePreproc::ValidCode(_, Some(ref runtime_version))) => {
						if runtime_version.can_call_with(&requested_version) {
							Action::ReuseInstance
						} else {
							trace!(target: "runtimes_cache",
								   "resetting cache because new version received");
							Action::CreateNewInstance
						}
					},
					None => unreachable!("instance is created at beginning of function if non-existent; qed"),
				}
			}
		};

		let runtime_preproc = match action {
			Action::ReuseInstance => {
				self.reset_instance();
				self.runtime_instance.clone()
					.expect("this path will only be invoked if instance exists; qed")
			}
			Action::CreateNewInstance => {
				self.create_instance(wasm_executor, ext, initial_heap_pages)?;
				self.runtime_instance.clone()
					.expect("was created right beforehand; qed")
			}
			Action::InvalidCode => {
				RuntimePreproc::InvalidCode
			}
		};

		match runtime_preproc {
			RuntimePreproc::InvalidCode => {
				let code = ext.original_storage(well_known_keys::CODE).unwrap_or(vec![]);
				Err(Error::InvalidCode(code))
			},
			RuntimePreproc::ValidCode(r, v) => {
				Ok((r, v))
			}
		}
	}

	fn create_instance<E: Externalities<Blake2Hasher>>(
		&mut self,
		wasm_executor: &WasmExecutor,
		ext: &mut E,
		initial_heap_pages: Option<u64>,
	) -> result::Result<(), Error> {
		let maybe_instance =
			self.create_wasm_instance(wasm_executor, ext, initial_heap_pages);
		match maybe_instance {
			RuntimePreproc::ValidCode(ref module, _) => {
				self.preserve_initial_memory(module)?;
				self.runtime_instance = Some(maybe_instance);
				Ok(())
			},
			RuntimePreproc::InvalidCode => Err(Error::InvalidCode(vec![])),
		}
	}

	fn preserve_initial_memory(&mut self, module: &WasmModuleInstanceRef) -> result::Result<(), Error> {
		let module_instance = module.deref();
		let mem = module_instance.export_by_name("memory")
			.ok_or_else(|| {
				trace!(target: "runtimes_cache", "No export 'memory' found in runtime!");
				Error::InvalidMemoryReference
			})?;
		match mem {
			wasmi::ExternVal::Memory(memory_ref) => {
				// The returned used size is a heuristic which returns one more
				// than the highest memory address that had been written to.
				let used_size = memory_ref.used_size().0;

				let data = memory_ref.get(0, used_size)
					.expect("extracting data will always succeed since requested range is always valid; qed");

				self.initial_memory = Some(data);
				Ok(())
			}
			_ => {
				trace!(target: "runtimes_cache", "No export 'memory' found in runtime!");
				Err(Error::InvalidMemoryReference)
			}
		}
	}

	/// Resets the runtime instance to the initial version by restoring
	/// the preserved memory.
	fn reset_instance(&self) -> RuntimePreproc {
		match &self.runtime_instance {
			Some(runtime) => {
				if let RuntimePreproc::ValidCode(module_ref, _) = runtime {
					if let Some(vec) = &self.initial_memory {
						let instance: &wasmi::ModuleInstance = module_ref.deref();
						let mem = instance.export_by_name("memory")
							.expect("export identifier 'memory' is hardcoded and will always exist; qed");
						match mem {
							wasmi::ExternVal::Memory(memory_ref) => {
								let mem = memory_ref;
								mem.set(0, vec)
									.expect("only putting data back in which was already in; qed");
							},
							_ => unreachable!("memory export always exists wasm module; qed"),
						}
					}
				}
				runtime.clone()
			}
			None => unreachable!("runtime instance is always existent at this point; qed"),
		}
	}

	fn create_wasm_instance<E: Externalities<Blake2Hasher>>(
		&self,
		wasm_executor: &WasmExecutor,
		ext: &mut E,
		initial_heap_pages: Option<u64>,
	) -> RuntimePreproc {
		let code = match ext.original_storage(well_known_keys::CODE) {
			Some(code) => code,
			None => return RuntimePreproc::InvalidCode,
		};

		let heap_pages = ext.storage(well_known_keys::HEAP_PAGES)
			.and_then(|pages| u64::decode(&mut &pages[..]))
			.or(initial_heap_pages)
			.unwrap_or(DEFAULT_HEAP_PAGES);

		match WasmModule::from_buffer(code)
			.map_err(|_| Error::InvalidCode(vec![]))
			.and_then(|module| wasm_executor.prepare_module(ext, heap_pages as usize, &module))
		{
			Ok(module) => {
				let version = wasm_executor.call_in_wasm_module(ext, &module, "Core_version", &[])
					.ok()
					.and_then(|v| {
						RuntimeVersion::decode(&mut v.as_slice())
					});
				RuntimePreproc::ValidCode(module, version)
			}
			Err(e) => {
				trace!(target: "runtimes_cache", "Invalid code presented to executor ({:?})", e);
				RuntimePreproc::InvalidCode
			}
		}
	}
}
