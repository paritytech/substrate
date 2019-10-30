// Copyright 2019 Parity Technologies (UK) Ltd.
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
use crate::wasmi_execution;
use log::{trace, warn};
use codec::Decode;
use primitives::{storage::well_known_keys, traits::Externalities};
use runtime_version::RuntimeVersion;
use std::{collections::hash_map::{Entry, HashMap}};

/// The Substrate Wasm runtime.
pub trait WasmRuntime {
	/// Attempt to update the number of heap pages available during execution.
	///
	/// Returns false if the update cannot be applied. The function is guaranteed to return true if
	/// the heap pages would not change from its current value.
	fn update_heap_pages(&mut self, heap_pages: u64) -> bool;

	/// Call a method in the Substrate runtime by name. Returns the encoded result on success.
	fn call(&mut self, ext: &mut dyn Externalities, method: &str, data: &[u8])
		-> Result<Vec<u8>, Error>;

	/// Returns the version of this runtime.
	///
	/// Returns `None` if the runtime doesn't provide the information or there was an error
	/// while fetching it.
	fn version(&self) -> Option<RuntimeVersion>;
}

/// Specification of different methods of executing the runtime Wasm code.
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum WasmExecutionMethod {
	/// Uses the Wasmi interpreter.
	Interpreted,
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
	instances: HashMap<(WasmExecutionMethod, [u8; 32]), Result<Box<dyn WasmRuntime>, WasmError>>,
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
	/// `ext` - Externalities to use for the runtime. This is used for setting
	/// up an initial runtime instance. The parameter is only needed for calling
	/// into the Wasm module to find out the `Core_version`.
	///
	/// `default_heap_pages` - Number of 64KB pages to allocate for Wasm execution.
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
	pub fn fetch_runtime<E: Externalities>(
		&mut self,
		ext: &mut E,
		wasm_method: WasmExecutionMethod,
		default_heap_pages: u64,
	) -> Result<&mut (dyn WasmRuntime + 'static), Error> {
		let code_hash = ext
			.original_storage_hash(well_known_keys::CODE)
			.ok_or(Error::InvalidCode("`CODE` not found in storage.".into()))?;

		let heap_pages = ext
			.storage(well_known_keys::HEAP_PAGES)
			.and_then(|pages| u64::decode(&mut &pages[..]).ok())
			.unwrap_or(default_heap_pages);

		let result = match self.instances.entry((wasm_method, code_hash.into())) {
			Entry::Occupied(o) => {
				let result = o.into_mut();
				if let Ok(ref mut cached_runtime) = result {
					if !cached_runtime.update_heap_pages(heap_pages) {
						trace!(
							target: "runtimes_cache",
							"heap_pages were changed. Reinstantiating the instance"
						);
						*result = create_wasm_runtime(ext, wasm_method, heap_pages);
						if let Err(ref err) = result {
							warn!(target: "runtimes_cache", "cannot create a runtime: {:?}", err);
						}
					}
				}
				result
			},
			Entry::Vacant(v) => {
				trace!(target: "runtimes_cache", "no instance found in cache, creating now.");
				let result = create_wasm_runtime(ext, wasm_method, heap_pages);
				if let Err(ref err) = result {
					warn!(target: "runtimes_cache", "cannot create a runtime: {:?}", err);
				}
				v.insert(result)
			}
		};

		result.as_mut()
			.map(|runtime| runtime.as_mut())
			.map_err(|ref e| Error::InvalidCode(format!("{:?}", e)))
	}
}

/// Create a wasm runtime with the given `code`.
pub fn create_wasm_runtime_with_code<E: Externalities>(
	ext: &mut E,
	wasm_method: WasmExecutionMethod,
	heap_pages: u64,
	code: &[u8],
) -> Result<Box<dyn WasmRuntime>, WasmError> {
	match wasm_method {
		WasmExecutionMethod::Interpreted =>
			wasmi_execution::create_instance(ext, code, heap_pages)
				.map(|runtime| -> Box<dyn WasmRuntime> { Box::new(runtime) }),
	}
}

fn create_wasm_runtime<E: Externalities>(
	ext: &mut E,
	wasm_method: WasmExecutionMethod,
	heap_pages: u64,
) -> Result<Box<dyn WasmRuntime>, WasmError> {
	let code = ext
		.original_storage(well_known_keys::CODE)
		.ok_or(WasmError::CodeNotFound)?;
	create_wasm_runtime_with_code(ext, wasm_method, heap_pages, &code)
}
