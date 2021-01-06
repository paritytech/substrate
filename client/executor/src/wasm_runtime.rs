// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Traits and accessor functions for calling into the Substrate Wasm runtime.
//!
//! The primary means of accessing the runtimes is through a cache which saves the reusable
//! components of the runtime that are expensive to initialize.

use std::sync::Arc;
use crate::error::{Error, WasmError};
use parking_lot::Mutex;
use codec::Decode;
use sp_core::traits::{Externalities, RuntimeCode, FetchRuntimeCode};
use sp_version::RuntimeVersion;
use std::panic::AssertUnwindSafe;
use sc_executor_common::wasm_runtime::{WasmModule, WasmInstance};

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

impl Default for WasmExecutionMethod {
	fn default() -> WasmExecutionMethod {
		WasmExecutionMethod::Interpreted
	}
}

/// A Wasm runtime object along with its cached runtime version.
struct VersionedRuntime {
	/// Runtime code hash.
	code_hash: Vec<u8>,
	/// Wasm runtime type.
	wasm_method: WasmExecutionMethod,
	/// Shared runtime that can spawn instances.
	module: Arc<dyn WasmModule>,
	/// The number of WebAssembly heap pages this instance was created with.
	heap_pages: u64,
	/// Runtime version according to `Core_version` if any.
	version: Option<RuntimeVersion>,
	/// Cached instance pool.
	instances: Vec<Mutex<Option<Box<dyn WasmInstance>>>>,
}

impl VersionedRuntime {
	/// Run the given closure `f` with an instance of this runtime.
	fn with_instance<'c, R, F>(
		&self,
		ext: &mut dyn Externalities,
		f: F,
	) -> Result<R, Error>
		where F: FnOnce(
			&Arc<dyn WasmModule>,
			&dyn WasmInstance,
			Option<&RuntimeVersion>,
			&mut dyn Externalities)
		-> Result<R, Error>,
	{
		// Find a free instance
		let instance = self.instances
			.iter()
			.enumerate()
			.find_map(|(index, i)| i.try_lock().map(|i| (index, i)));

		match instance {
			Some((index, mut locked)) => {
				let (instance, new_inst) = locked.take()
					.map(|r| Ok((r, false)))
					.unwrap_or_else(|| self.module.new_instance().map(|i| (i, true)))?;

				let result = f(&self.module, &*instance, self.version.as_ref(), ext);
				if let Err(e) = &result {
					if new_inst {
						log::warn!(
							target: "wasm-runtime",
							"Fresh runtime instance failed with {:?}",
							e,
						)
					} else {
						log::warn!(
							target: "wasm-runtime",
							"Evicting failed runtime instance: {:?}",
							e,
						);
					}
				} else {
					*locked = Some(instance);

					if new_inst {
						log::debug!(
							target: "wasm-runtime",
							"Allocated WASM instance {}/{}",
							index + 1,
							self.instances.len(),
						);
					}
				}

				result
			},
			None => {
				log::warn!(target: "wasm-runtime", "Ran out of free WASM instances");

				// Allocate a new instance
				let instance = self.module.new_instance()?;

				f(&self.module, &*instance, self.version.as_ref(), ext)
			}
		}
	}
}

const MAX_RUNTIMES: usize = 2;

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
/// The size of cache is equal to `MAX_RUNTIMES`.
pub struct RuntimeCache {
	/// A cache of runtimes along with metadata.
	///
	/// Runtimes sorted by recent usage. The most recently used is at the front.
	runtimes: Mutex<[Option<Arc<VersionedRuntime>>; MAX_RUNTIMES]>,
	/// The size of the instances cache for each runtime.
	max_runtime_instances: usize,
}

impl RuntimeCache {
	/// Creates a new instance of a runtimes cache.
	pub fn new(max_runtime_instances: usize) -> RuntimeCache {
		RuntimeCache {
			runtimes: Default::default(),
			max_runtime_instances,
		}
	}

	/// Prepares a WASM module instance and executes given function for it.
	///
	/// This uses internal cache to find avaiable instance or create a new one.
	/// # Parameters
	///
	/// `code` - Provides external code or tells the executor to fetch it from storage.
	///
	/// `runtime_code` - The runtime wasm code used setup the runtime.
	///
	/// `default_heap_pages` - Number of 64KB pages to allocate for Wasm execution.
	///
	/// `wasm_method` - Type of WASM backend to use.
	///
	/// `host_functions` - The host functions that should be registered for the Wasm runtime.
	///
	/// `allow_missing_func_imports` - Ignore missing function imports.
	///
	/// `max_runtime_instances` - The size of the instances cache.
	///
	/// `f` - Function to execute.
	///
	/// # Returns result of `f` wrapped in an additonal result.
	/// In case of failure one of two errors can be returned:
	///
	/// `Err::InvalidCode` is returned for runtime code issues.
	///
	/// `Error::InvalidMemoryReference` is returned if no memory export with the
	/// identifier `memory` can be found in the runtime.
	pub fn with_instance<'c, R, F>(
		&self,
		runtime_code: &'c RuntimeCode<'c>,
		ext: &mut dyn Externalities,
		wasm_method: WasmExecutionMethod,
		default_heap_pages: u64,
		host_functions: &[&'static dyn Function],
		allow_missing_func_imports: bool,
		f: F,
	) -> Result<Result<R, Error>, Error>
		where F: FnOnce(
			&Arc<dyn WasmModule>,
			&dyn WasmInstance,
			Option<&RuntimeVersion>,
			&mut dyn Externalities)
		-> Result<R, Error>,
	{
		let code_hash = &runtime_code.hash;
		let heap_pages = runtime_code.heap_pages.unwrap_or(default_heap_pages);

		let mut runtimes = self.runtimes.lock(); // this must be released prior to calling f
		let pos = runtimes.iter().position(|r| r.as_ref().map_or(
			false,
			|r| r.wasm_method == wasm_method &&
				r.code_hash == *code_hash &&
				r.heap_pages == heap_pages
		));

		let runtime = match pos {
			Some(n) => runtimes[n]
				.clone()
				.expect("`position` only returns `Some` for entries that are `Some`"),
			None =>  {
				let code = runtime_code.fetch_runtime_code().ok_or(WasmError::CodeNotFound)?;

				let result = create_versioned_wasm_runtime(
					&code,
					code_hash.clone(),
					ext,
					wasm_method,
					heap_pages,
					host_functions.into(),
					allow_missing_func_imports,
					self.max_runtime_instances,
				);
				if let Err(ref err) = result {
					log::warn!(target: "wasm-runtime", "Cannot create a runtime: {:?}", err);
				}
				Arc::new(result?)
			}
		};

		// Rearrange runtimes by last recently used.
		match pos {
			Some(0) => {},
			Some(n) => {
				for i in (1 .. n + 1).rev() {
					runtimes.swap(i, i - 1);
				}
			}
			None => {
				runtimes[MAX_RUNTIMES-1] = Some(runtime.clone());
				for i in (1 .. MAX_RUNTIMES).rev() {
					runtimes.swap(i, i - 1);
				}
			}
		}
		drop(runtimes);

		Ok(runtime.with_instance(ext, f))
	}
}

/// Create a wasm runtime with the given `code`.
pub fn create_wasm_runtime_with_code(
	wasm_method: WasmExecutionMethod,
	heap_pages: u64,
	code: &[u8],
	host_functions: Vec<&'static dyn Function>,
	allow_missing_func_imports: bool,
) -> Result<Arc<dyn WasmModule>, WasmError> {
	match wasm_method {
		WasmExecutionMethod::Interpreted =>
			sc_executor_wasmi::create_runtime(
				code,
				heap_pages,
				host_functions,
				allow_missing_func_imports
			).map(|runtime| -> Arc<dyn WasmModule> { Arc::new(runtime) }),
		#[cfg(feature = "wasmtime")]
		WasmExecutionMethod::Compiled =>
			sc_executor_wasmtime::create_runtime(
				code,
				heap_pages,
				host_functions,
				allow_missing_func_imports
			).map(|runtime| -> Arc<dyn WasmModule> { Arc::new(runtime) }),
	}
}

fn decode_version(version: &[u8]) -> Result<RuntimeVersion, WasmError> {
	let v: RuntimeVersion = sp_api::OldRuntimeVersion::decode(&mut &version[..])
		.map_err(|_|
				 WasmError::Instantiation(
					 "failed to decode \"Core_version\" result using old runtime version".into(),
				 )
		)?.into();

	let core_api_id = sp_core::hashing::blake2_64(b"Core");
	if v.has_api_with(&core_api_id, |v| v >= 3) {
		sp_api::RuntimeVersion::decode(&mut &version[..])
			.map_err(|_|
				WasmError::Instantiation("failed to decode \"Core_version\" result".into())
			)
	} else {
		Ok(v)
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
	max_instances: usize,
) -> Result<VersionedRuntime, WasmError> {
	#[cfg(not(target_os = "unknown"))]
	let time = std::time::Instant::now();
	let runtime = create_wasm_runtime_with_code(
		wasm_method,
		heap_pages,
		&code,
		host_functions,
		allow_missing_func_imports,
	)?;

	// Call to determine runtime version.
	let version_result = {
		// `ext` is already implicitly handled as unwind safe, as we store it in a global variable.
		let mut ext = AssertUnwindSafe(ext);

		// The following unwind safety assertion is OK because if the method call panics, the
		// runtime will be dropped.
		let runtime = AssertUnwindSafe(runtime.as_ref());
		crate::native_executor::with_externalities_safe(
			&mut **ext,
			move || runtime.new_instance()?.call("Core_version".into(), &[])
		).map_err(|_| WasmError::Instantiation("panic in call to get runtime version".into()))?
	};
	let version = match version_result {
		Ok(version) => Some(decode_version(&version)?),
		Err(_) => None,
	};
	#[cfg(not(target_os = "unknown"))]
	log::debug!(
		target: "wasm-runtime",
		"Prepared new runtime version {:?} in {} ms.",
		version,
		time.elapsed().as_millis(),
	);

	let mut instances = Vec::with_capacity(max_instances);
	instances.resize_with(max_instances, || Mutex::new(None));

	Ok(VersionedRuntime {
		code_hash,
		module: runtime,
		version,
		heap_pages,
		wasm_method,
		instances,
	})
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_wasm_interface::HostFunctions;
	use sp_api::{Core, RuntimeApiInfo};
	use substrate_test_runtime::Block;
	use codec::Encode;

	#[test]
	fn host_functions_are_equal() {
		let host_functions = sp_io::SubstrateHostFunctions::host_functions();

		let equal = &host_functions[..] == &host_functions[..];
		assert!(equal, "Host functions are not equal");
	}

	#[test]
	fn old_runtime_version_decodes() {
		let old_runtime_version = sp_api::OldRuntimeVersion {
			spec_name: "test".into(),
			impl_name: "test".into(),
			authoring_version: 1,
			spec_version: 1,
			impl_version: 1,
			apis: sp_api::create_apis_vec!([(Core::<Block, Error = ()>::ID, 1)]),
		};

		let version = decode_version(&old_runtime_version.encode()).unwrap();
		assert_eq!(1, version.transaction_version);
	}

	#[test]
	fn old_runtime_version_decodes_fails_with_version_3() {
		let old_runtime_version = sp_api::OldRuntimeVersion {
			spec_name: "test".into(),
			impl_name: "test".into(),
			authoring_version: 1,
			spec_version: 1,
			impl_version: 1,
			apis: sp_api::create_apis_vec!([(Core::<Block, Error = ()>::ID, 3)]),
		};

		decode_version(&old_runtime_version.encode()).unwrap_err();
	}

	#[test]
	fn new_runtime_version_decodes() {
		let old_runtime_version = sp_api::RuntimeVersion {
			spec_name: "test".into(),
			impl_name: "test".into(),
			authoring_version: 1,
			spec_version: 1,
			impl_version: 1,
			apis: sp_api::create_apis_vec!([(Core::<Block, Error = ()>::ID, 3)]),
			transaction_version: 3,
		};

		let version = decode_version(&old_runtime_version.encode()).unwrap();
		assert_eq!(3, version.transaction_version);
	}
}
