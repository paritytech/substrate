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

use std::sync::Arc;
use std::borrow::Cow;
use crate::error::{Error, WasmError};
use parking_lot::{Mutex, RwLock, RwLockUpgradableReadGuard};
use codec::Decode;
use sp_core::{storage::well_known_keys, traits::Externalities};
use sp_version::RuntimeVersion;
use std::panic::AssertUnwindSafe;
use sc_executor_common::wasm_runtime::{WasmRuntime, WasmInstance};

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

/// Eecuted code source.
pub enum CodeSource<'a> {
	/// Take code from storage,
	Externalities,
	/// Use provided code,
	Custom(&'a [u8]),
}

/// A Wasm runtime object along with its cached runtime version.
struct VersionedRuntime {
	/// Code hash.
	code_hash: Vec<u8>,
	/// Wasm runtime type.
	wasm_method: WasmExecutionMethod,
	/// Shared runtime.
	runtime: Box<dyn WasmRuntime>,
	/// The number of WebAssembly heap pages this instance was created with.
	heap_pages: u64,
	/// Runtime version according to `Core_version` if any.
	version: Option<RuntimeVersion>,
	/// Cached instance pool.
	instances: RwLock<Vec<Mutex<Box<dyn WasmInstance>>>>,
}

const MAX_RUNTIMES: usize = 2;
const MAX_INSTANCES: usize = 8;

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
pub struct RuntimeCache {
	/// A cache of runtimes along with metadata.
	///
	/// Runtimes sorted by recent usage. The most recently used is at the front.
	runtimes: RwLock<[Option<Arc<VersionedRuntime>>; MAX_RUNTIMES]>,
}

impl RuntimeCache {
	/// Creates a new instance of a runtimes cache.
	pub fn new() -> RuntimeCache {
		RuntimeCache {
			runtimes: Default::default(),
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
	/// `ext` - Externalities to use for the runtime. This is used for setting
	/// up an initial runtime instance.
	///
	/// `default_heap_pages` - Number of 64KB pages to allocate for Wasm execution.
	///
	/// `host_functions` - The host functions that should be registered for the Wasm runtime.
	///
	/// # Return value
	///
	/// If no error occurred a tuple `(&mut WasmRuntime, H256)` is
	/// returned. `H256` is the hash of the runtime code.
	///
	/// In case of failure one of two errors can be returned:
	///
	/// `Err::InvalidCode` is returned for runtime code issues.
	///
	/// `Error::InvalidMemoryReference` is returned if no memory export with the
	/// identifier `memory` can be found in the runtime.
	pub fn with_instance<'c, R, F>(
		&self,
		code: CodeSource<'c>,
		ext: &mut dyn Externalities,
		wasm_method: WasmExecutionMethod,
		default_heap_pages: u64,
		host_functions: &[&'static dyn Function],
		allow_missing_func_imports: bool,
		f: F,
	) -> Result<R, Error>
		where F: FnOnce(&dyn WasmInstance, Option<&RuntimeVersion>, &mut dyn Externalities) -> R,
	{
		let (code_hash, heap_pages) = match &code {
			CodeSource::Externalities => {
				(
					ext
						.original_storage_hash(well_known_keys::CODE)
						.ok_or(Error::InvalidCode("`CODE` not found in storage.".into()))?,
					ext
						.storage(well_known_keys::HEAP_PAGES)
						.and_then(|pages| u64::decode(&mut &pages[..]).ok())
						.unwrap_or(default_heap_pages)
				)
			},
			CodeSource::Custom(code) => {
				(sp_core::blake2_256(code).to_vec(), default_heap_pages)
			}
		};

		let runtimes = self.runtimes.upgradable_read(); // this must be released prior to calling f
		let pos = runtimes.iter().position(|r| r.as_ref().map_or(
			false,
			|r| r.wasm_method == wasm_method && r.code_hash == code_hash && r.heap_pages == heap_pages
		));

		let runtime = match pos {
			Some(n) => runtimes[n].clone().expect("`position` only returns `Some` for entries that are `Some`"),
			None =>  {
				let code = match code {
					CodeSource::Externalities => {
						Cow::Owned(ext.original_storage(well_known_keys::CODE).ok_or(WasmError::CodeNotFound)?)
					}
					CodeSource::Custom(code) => {
						Cow::Borrowed(code)
					}
				};

				let result = create_versioned_wasm_runtime(
					&code,
					code_hash,
					ext,
					wasm_method,
					heap_pages,
					host_functions.into(),
					allow_missing_func_imports,
				);
				if let Err(ref err) = result {
					log::warn!(target: "wasm-cache", "Cannot create a runtime: {:?}", err);
				}
				Arc::new(result?)
			}
		};

		// Rearrange runtimes by last recently used.
		match pos {
			Some(0) => { drop(runtimes) },
			Some(n) => {
				let mut runtimes = RwLockUpgradableReadGuard::upgrade(runtimes);
				for i in (1 .. n + 1).rev() {
					runtimes.swap(i, i - 1);
				}
			}
			None => {
				let mut runtimes = RwLockUpgradableReadGuard::upgrade(runtimes);
				runtimes[MAX_RUNTIMES-1] = Some(runtime.clone());
				for i in (1 .. MAX_RUNTIMES).rev() {
					runtimes.swap(i, i - 1);
				}
			}
		}

		let result = {
			let instance_pool = runtime.instances.upgradable_read();
			// Find a free instance
			let instance = instance_pool.iter().filter_map(|i| i.try_lock()).next();
			if let Some(instance) = instance {
				f(&**instance, runtime.version.as_ref(), ext)
			} else {
				// Allocate a new instance
				drop(instance);
				let instance = runtime.runtime.new_instance()?;

				let result = f(&*instance, runtime.version.as_ref(), ext);
				let mut instance_pool = RwLockUpgradableReadGuard::upgrade(instance_pool);
				if instance_pool.len() < MAX_INSTANCES {
					instance_pool.push(Mutex::new(instance));
					log::debug!(target: "wasm-cache", "Allocated WASM instance {}/{}", instance_pool.len(), MAX_INSTANCES);
				} else {
					log::warn!(target: "wasm-cache", "Ran out of free WASM instances");
				}
				result
			}
		};

		Ok(result)
	}
	/*
	/// Invalidate the runtime for the given `wasm_method` and `code_hash`.
	///
	/// Invalidation of a runtime is useful when there was a `panic!` in native while executing it.
	/// The `panic!` maybe have brought the runtime into a poisoned state and so, it is better to
	/// invalidate this runtime instance.
	fn invalidate_runtime(
		&mut self,
		wasm_method: WasmExecutionMethod,
		code_hash: Vec<u8>,
	) {
		// Just remove the instance, it will be re-created the next time it is requested.
		self.instances.remove(&(wasm_method, code_hash));
	}
	*/
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
			sc_executor_wasmi::create_runtime(code, heap_pages, host_functions, allow_missing_func_imports)
				.map(|runtime| -> Box<dyn WasmRuntime> { Box::new(runtime) }),
		#[cfg(feature = "wasmtime")]
		WasmExecutionMethod::Compiled =>
			sc_executor_wasmtime::create_runtime(code, heap_pages, host_functions, allow_missing_func_imports)
				.map(|runtime| -> Box<dyn WasmRuntime> { Box::new(runtime) }),
	}
}

fn create_versioned_wasm_runtime(
	code: &[u8],
	code_hash: Vec<u8>,
	ext: &mut dyn Externalities,
	wasm_method: WasmExecutionMethod,
	heap_pages: u64,
	host_functions: Vec<&'static dyn Function>,
	allow_missing_func_imports: bool,
) -> Result<VersionedRuntime, WasmError> {
	let time = std::time::Instant::now();
	let mut runtime = create_wasm_runtime_with_code(
		wasm_method,
		heap_pages,
		&code,
		host_functions,
		allow_missing_func_imports
	)?;

	// Call to determine runtime version.
	let version_result = {
		// `ext` is already implicitly handled as unwind safe, as we store it in a global variable.
		let mut ext = AssertUnwindSafe(ext);

		// The following unwind safety assertion is OK because if the method call panics, the
		// runtime will be dropped.
		let runtime = AssertUnwindSafe(runtime.as_mut());
		crate::native_executor::with_externalities_safe(
			&mut **ext,
			move || runtime.new_instance()?.call("Core_version", &[])
		).map_err(|_| WasmError::Instantiation("panic in call to get runtime version".into()))?
	};
	let version = match version_result {
		Ok(version) => Some(RuntimeVersion::decode(&mut version.as_slice())
			.map_err(|_| WasmError::Instantiation("failed to decode \"Core_version\" result".into()))?),
		Err(_) => None,
	};
	log::debug!(
		target: "wasm-cache",
		"Prepared new runtime version {:?} in {} ms.",
		version,
		time.elapsed().as_millis()
	);

	Ok(VersionedRuntime {
		code_hash,
		runtime,
		version,
		heap_pages,
		wasm_method,
		instances: RwLock::new(Vec::with_capacity(MAX_INSTANCES)),
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
