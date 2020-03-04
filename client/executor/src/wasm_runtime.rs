// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Traits and accessor functions for calling into the Substrate Wasm runtime.
//!
//! The primary means of accessing the runtimes is through a cache which saves the reusable
//! components of the runtime that are expensive to initialize.

use crate::error::{Error, WasmError};
use log::{trace, warn};
use codec::Decode;
use sp_core::traits::{Externalities, RuntimeCode};
use sp_version::RuntimeVersion;
use std::{collections::hash_map::{Entry, HashMap}, panic::AssertUnwindSafe};
use sc_executor_common::wasm_runtime::WasmRuntime;

use sp_wasm_interface::Function;

/// Specification of different methods of executing the runtime Wasm code.
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum WasmExecutionMethod {
	/// Uses the Wasmi interpreter.
	Interpreted,
	/// Uses the Wasmtime compiled runtime.
	#[cfg(feature = "wasmtime")]
	Compiled,
}

/// A Wasm runtime object along with its cached runtime version.
struct VersionedRuntime {
	runtime: Box<dyn WasmRuntime>,
	/// The number of WebAssembly heap pages this instance was created with.
	heap_pages: u64,
	/// Runtime version according to `Core_version`.
	version: RuntimeVersion,
}

/// Cache for the runtimes.
///
/// When an instance is requested for the first time it is added to this cache. Metadata is kept
/// with the instance so that it can be efficiently reinitialized.
///
/// When using the Wasmi interpreter execution method, the metadata includes the initial memory and
/// values of mutable globals. Follow-up requests to fetch a runtime return this one instance with
/// the memory reset to the initial memory. So, one runtime instance is reused for every fetch
/// request.
///
/// For now the cache grows indefinitely, but that should be fine for now since runtimes can only be
/// upgraded rarely and there are no other ways to make the node to execute some other runtime.
pub struct RuntimesCache {
	/// A cache of runtime instances along with metadata, ready to be reused.
	///
	/// Instances are keyed by the Wasm execution method and the hash of their code.
	instances: HashMap<(WasmExecutionMethod, Vec<u8>), Result<VersionedRuntime, WasmError>>,
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
	/// `ext` - Externalities to use for the getting the runtime's version call.
	///
	/// `runtime_code` - The runtime wasm code used setup the runtime.
	///
	/// `default_heap_pages` - Number of 64KB pages to allocate for Wasm execution.
	///
	/// `host_functions` - The host functions that should be registered for the Wasm runtime.
	///
	/// # Return value
	///
	/// If no error occurred a tuple `(&mut WasmRuntime, RuntimeVerion)` is
	/// returned.
	///
	/// In case of failure one of two errors can be returned:
	///
	/// `Err::InvalidCode` is returned for runtime code issues.
	///
	/// `Error::InvalidMemoryReference` is returned if no memory export with the
	/// identifier `memory` can be found in the runtime.
	pub fn fetch_runtime<E: Externalities>(
		&mut self,
		ext: &mut E,
		runtime_code: &RuntimeCode,
		wasm_method: WasmExecutionMethod,
		default_heap_pages: u64,
		host_functions: &[&'static dyn Function],
	) -> Result<(&mut (dyn WasmRuntime + 'static), &RuntimeVersion), Error> {
		let heap_pages = runtime_code.heap_pages.unwrap_or(default_heap_pages);

		let result = match self.instances.entry((wasm_method, runtime_code.hash.clone())) {
			Entry::Occupied(o) => {
				let result = o.into_mut();
				if let Ok(ref mut cached_runtime) = result {
					let heap_pages_changed = cached_runtime.heap_pages != heap_pages;
					let host_functions_changed = cached_runtime.runtime.host_functions()
						!= host_functions;
					if heap_pages_changed || host_functions_changed {
						let changed = if heap_pages_changed {
							"heap_pages"
						} else {
							"host functions"
						};

						trace!(
							target: "runtimes_cache",
							"{} were changed. Reinstantiating the instance",
							changed,
						);
						*result = create_versioned_wasm_runtime(
							ext,
							wasm_method,
							runtime_code,
							heap_pages,
							host_functions.into(),
						);
						if let Err(ref err) = result {
							warn!(target: "runtimes_cache", "cannot create a runtime: {:?}", err);
						}
					}
				}
				result
			},
			Entry::Vacant(v) => {
				trace!(target: "runtimes_cache", "no instance found in cache, creating now.");
				let result = create_versioned_wasm_runtime(
					ext,
					wasm_method,
					runtime_code,
					heap_pages,
					host_functions.into(),
				);
				if let Err(ref err) = result {
					warn!(target: "runtimes_cache", "cannot create a runtime: {:?}", err);
				}
				v.insert(result)
			}
		};

		result.as_mut()
			.map(|entry| (entry.runtime.as_mut(), &entry.version))
			.map_err(|ref e| Error::InvalidCode(format!("{:?}", e)))
	}

	/// Invalidate the runtime for the given `wasm_method` and `code_hash`.
	///
	/// Invalidation of a runtime is useful when there was a `panic!` in native while executing it.
	/// The `panic!` maybe have brought the runtime into a poisoned state and so, it is better to
	/// invalidate this runtime instance.
	pub fn invalidate_runtime(
		&mut self,
		wasm_method: WasmExecutionMethod,
		code_hash: Vec<u8>,
	) {
		// Just remove the instance, it will be re-created the next time it is requested.
		self.instances.remove(&(wasm_method, code_hash));
	}
}

/// Create a wasm runtime with the given `code`.
pub fn create_wasm_runtime_with_code(
	wasm_method: WasmExecutionMethod,
	heap_pages: u64,
	code: &[u8],
	host_functions: Vec<&'static dyn Function>,
	allow_missing_func_imports: bool,
) -> Result<Box<dyn WasmRuntime>, WasmError> {
	match wasm_method {
		WasmExecutionMethod::Interpreted =>
			sc_executor_wasmi::create_instance(code, heap_pages, host_functions, allow_missing_func_imports)
				.map(|runtime| -> Box<dyn WasmRuntime> { Box::new(runtime) }),
		#[cfg(feature = "wasmtime")]
		WasmExecutionMethod::Compiled =>
			sc_executor_wasmtime::create_instance(code, heap_pages, host_functions, allow_missing_func_imports)
				.map(|runtime| -> Box<dyn WasmRuntime> { Box::new(runtime) }),
	}
}

fn create_versioned_wasm_runtime<E: Externalities>(
	ext: &mut E,
	wasm_method: WasmExecutionMethod,
	runtime_code: &RuntimeCode,
	heap_pages: u64,
	host_functions: Vec<&'static dyn Function>,
) -> Result<VersionedRuntime, WasmError> {
	let mut runtime = create_wasm_runtime_with_code(
		wasm_method,
		heap_pages,
		&runtime_code.code,
		host_functions,
		false,
	)?;

	// Call to determine runtime version.
	let version_result = {
		// `ext` is already implicitly handled as unwind safe, as we store it in a global variable.
		let mut ext = AssertUnwindSafe(ext);

		// The following unwind safety assertion is OK because if the method call panics, the
		// runtime will be dropped.
		let mut runtime = AssertUnwindSafe(runtime.as_mut());
		crate::native_executor::with_externalities_safe(
			&mut **ext,
			move || runtime.call("Core_version", &[])
		).map_err(|_| WasmError::Instantiation("panic in call to get runtime version".into()))?
	};
	let encoded_version = version_result
		.map_err(|e| WasmError::Instantiation(format!("failed to call \"Core_version\": {}", e)))?;
	let version = RuntimeVersion::decode(&mut encoded_version.as_slice())
		.map_err(|_| WasmError::Instantiation("failed to decode \"Core_version\" result".into()))?;

	Ok(VersionedRuntime {
		runtime,
		version,
		heap_pages,
	})
}

#[cfg(test)]
mod tests {
	use sp_wasm_interface::HostFunctions;

	#[test]
	fn host_functions_are_equal() {
		let host_functions = sp_io::SubstrateHostFunctions::host_functions();

		let equal = &host_functions[..] == &host_functions[..];
		assert!(equal, "Host functions are not equal");
	}
}
