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
use wasmi::{Module as WasmModule, ModuleRef as WasmModuleInstanceRef};

#[derive(Clone)]
enum RuntimePreproc {
	InvalidCode,
	ValidCode(WasmModuleInstanceRef, Option<RuntimeVersion>),
}

#[derive(Debug)]
enum Action {
	Clone,
	Invalid,
	Reset,
}

/// Default num of pages for the heap
const DEFAULT_HEAP_PAGES: u64 = 1024;

/// Cache a runtime instances. When an instance is requested,
/// the template instance is cloned synchronously.
pub struct RuntimesCache {
	template_instance: Option<RuntimePreproc>,
}

impl RuntimesCache {
	/// Creates a new instance of a runtimes cache.
	pub fn new() -> RuntimesCache {
		RuntimesCache {
			template_instance: None,
		}
	}

	/// Fetch a runtime instance from a template instance. If there is no template
	/// instance yet, initialization happens automatically.
	///
	/// # Parameters
	///
	/// `wasm_executor`- Rust wasm executor. Executes the provided code in a
	/// sandboxed Wasm runtime.
	///
	/// `ext` - Externalities to use for the runtime. This is used for setting
	/// up an initial "template instance", which will be cloned when this method
	/// is called. The parameter is only needed to call into he Wasm module to
	/// find out the `Core_version`.
	///
	/// `default_heap_pages` - Default number of 64KB pages to allocate for
	/// Wasm execution. Defaults to `DEFAULT_HEAP_PAGES` if `None` is provided.
	///
	/// `maybe_requested_version` - If `Some(RuntimeVersion)` is provided the
	/// template instance will be checked for compatibility. In case of
	/// incompatibility the template instance will be reset.
	///
	/// # Return value
	///
	/// If no error occurred a `RuntimePreproc::ValidCode` is returned, containing
	/// a wasmi `ModuleRef` with an optional `RuntimeVersion` (if the call
	/// `Core_version` returned a version).
	///
	/// In case an error occurred `RuntimePreproc::InvalidCode` is returned with an
	/// appropriate description.
	pub fn fetch_runtime<E: Externalities<Blake2Hasher>>(
		&mut self,
		wasm_executor: &WasmExecutor,
		ext: &mut E,
		default_heap_pages: Option<u64>,
		maybe_requested_version: Option<&RuntimeVersion>,
	) -> Result<(WasmModuleInstanceRef, Option<RuntimeVersion>)> {
		if let None = self.template_instance {
			trace!(target: "runtimes_cache",
				   "no template instance found, creating now.");
			let template =
				self.create_wasm_instance(wasm_executor, ext, default_heap_pages);
			self.template_instance = Some(template);
		}

		let action = match maybe_requested_version {
			None => Action::Clone,
			Some(ref version) => {
				match self.template_instance {
					None => Action::Clone,
					Some(RuntimePreproc::InvalidCode) => Action::Invalid,
					Some(RuntimePreproc::ValidCode(_, None)) => Action::Reset,
					Some(RuntimePreproc::ValidCode(_, Some(ref template_version))) => {
						if template_version.can_call_with(&version) {
							Action::Clone
						} else {
							trace!(target: "runtimes_cache",
								   "resetting cache because new version received");
							Action::Reset
						}
					},
				}
			},
		};

		let runtime_preproc = match action {
			Action::Clone => {
				self.template_instance
					.clone()
					.expect("if non-existent, template was created at beginning of function; qed")
			},
			Action::Reset => {
				let new_template = self.create_wasm_instance(wasm_executor, ext, default_heap_pages);
				self.template_instance = Some(new_template);
				self.template_instance
					.clone()
					.expect("template was created right before; qed")
			},
			Action::Invalid => {
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

	fn create_wasm_instance<E: Externalities<Blake2Hasher>>(
		&self,
		wasm_executor: &WasmExecutor,
		ext: &mut E,
		default_heap_pages: Option<u64>,
	) -> RuntimePreproc {
		let code = match ext.original_storage(well_known_keys::CODE) {
			Some(code) => code,
			None => return RuntimePreproc::InvalidCode,
		};

		let heap_pages = ext.storage(well_known_keys::HEAP_PAGES)
			.and_then(|pages| u64::decode(&mut &pages[..]))
			.or(default_heap_pages)
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
