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

use std::{borrow::BorrowMut, result, cell::{RefMut, RefCell}};
use crate::error::{Error, Result};
use state_machine::{CodeExecutor, Externalities};
use crate::wasm_executor::WasmExecutor;
use wasmi::{Module as WasmModule, ModuleRef as WasmModuleInstanceRef};
use runtime_version::{NativeVersion, RuntimeVersion};
use std::{collections::HashMap, panic::UnwindSafe};
use parity_codec::{Decode, Encode};
use crate::RuntimeInfo;
use primitives::{Blake2Hasher, NativeOrEncoded};
use primitives::storage::well_known_keys;
use log::trace;

/// Default num of pages for the heap
const DEFAULT_HEAP_PAGES: u64 = 1024;

// For the internal Runtime Cache:
// Is it compatible enough to run this natively or do we need to fall back on the WasmModule

enum RuntimePreproc {
	InvalidCode,
	ValidCode(WasmModuleInstanceRef, Option<RuntimeVersion>),
}

type CacheType = HashMap<[u8; 32], RuntimePreproc>;

thread_local! {
	static RUNTIMES_CACHE: RefCell<CacheType> = RefCell::new(HashMap::new());
}

/// fetch a runtime version from the cache or if there is no cached version yet, create
/// the runtime version entry for `code`, determines whether `Compatibility::IsCompatible`
/// can be used by comparing returned RuntimeVersion to `ref_version`
fn fetch_cached_runtime_version<'a, E: Externalities<Blake2Hasher>>(
	wasm_executor: &WasmExecutor,
	cache: &'a mut RefMut<CacheType>,
	ext: &mut E,
	default_heap_pages: Option<u64>,
) -> Result<(&'a WasmModuleInstanceRef, &'a Option<RuntimeVersion>)> {
	let code_hash = match ext.original_storage_hash(well_known_keys::CODE) {
		Some(code_hash) => code_hash,
		None => return Err(Error::InvalidCode(vec![])),
	};

	let maybe_runtime_preproc = cache.borrow_mut().entry(code_hash.into())
		.or_insert_with(|| {
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
						.and_then(|v| RuntimeVersion::decode(&mut v.as_slice()));
					RuntimePreproc::ValidCode(module, version)
				}
				Err(e) => {
					trace!(target: "executor", "Invalid code presented to executor ({:?})", e);
					RuntimePreproc::InvalidCode
				}
			}
		});

	match maybe_runtime_preproc {
		RuntimePreproc::InvalidCode => {
			let code = ext.original_storage(well_known_keys::CODE).unwrap_or(vec![]);
			Err(Error::InvalidCode(code))
		},
		RuntimePreproc::ValidCode(m, v) => {
			Ok((m, v))
		}
	}
}

fn safe_call<F, U>(f: F) -> Result<U>
	where F: UnwindSafe + FnOnce() -> U
{
	// Substrate uses custom panic hook that terminates process on panic. Disable termination for the native call.
	let _guard = panic_handler::AbortGuard::new(false);
	::std::panic::catch_unwind(f).map_err(|_| Error::Runtime)
}

/// Set up the externalities and safe calling environment to execute calls to a native runtime.
///
/// If the inner closure panics, it will be caught and return an error.
pub fn with_native_environment<F, U>(ext: &mut dyn Externalities<Blake2Hasher>, f: F) -> Result<U>
	where F: UnwindSafe + FnOnce() -> U
{
	::runtime_io::with_externalities(ext, move || safe_call(f))
}

/// Delegate for dispatching a CodeExecutor call to native code.
pub trait NativeExecutionDispatch: Send + Sync {
	/// Get the wasm code that the native dispatch will be equivalent to.
	fn native_equivalent() -> &'static [u8];

	/// Dispatch a method and input data to be executed natively. Returns `Some` result or `None`
	/// if the `method` is unknown. Panics if there's an unrecoverable error.
	// fn dispatch<H: hash_db::Hasher>(ext: &mut Externalities<H>, method: &str, data: &[u8]) -> Result<Vec<u8>>;
	fn dispatch(ext: &mut dyn Externalities<Blake2Hasher>, method: &str, data: &[u8]) -> Result<Vec<u8>>;

	/// Provide native runtime version.
	fn native_version() -> NativeVersion;

	/// Construct corresponding `NativeExecutor`
	fn new(default_heap_pages: Option<u64>) -> NativeExecutor<Self> where Self: Sized;
}

/// A generic `CodeExecutor` implementation that uses a delegate to determine wasm code equivalence
/// and dispatch to native code when possible, falling back on `WasmExecutor` when not.
#[derive(Debug)]
pub struct NativeExecutor<D> {
	/// Dummy field to avoid the compiler complaining about us not using `D`.
	_dummy: ::std::marker::PhantomData<D>,
	/// The fallback executor in case native isn't available.
	fallback: WasmExecutor,
	/// Native runtime version info.
	native_version: NativeVersion,
	/// The default number of 64KB pages to allocate for Wasm execution.
	default_heap_pages: Option<u64>,
}

impl<D: NativeExecutionDispatch> NativeExecutor<D> {
	/// Create new instance.
	pub fn new(default_heap_pages: Option<u64>) -> Self {
		NativeExecutor {
			_dummy: Default::default(),
			fallback: WasmExecutor::new(),
			native_version: D::native_version(),
			default_heap_pages,
		}
	}
}

impl<D: NativeExecutionDispatch> Clone for NativeExecutor<D> {
	fn clone(&self) -> Self {
		NativeExecutor {
			_dummy: Default::default(),
			fallback: self.fallback.clone(),
			native_version: D::native_version(),
			default_heap_pages: self.default_heap_pages,
		}
	}
}

impl<D: NativeExecutionDispatch> RuntimeInfo for NativeExecutor<D> {
	fn native_version(&self) -> &NativeVersion {
		&self.native_version
	}

	fn runtime_version<E: Externalities<Blake2Hasher>>(
		&self,
		ext: &mut E,
	) -> Option<RuntimeVersion> {
		RUNTIMES_CACHE.with(|c|
			fetch_cached_runtime_version(&self.fallback, &mut c.borrow_mut(), ext, self.default_heap_pages)
				.ok()?.1.clone()
		)
	}
}

impl<D: NativeExecutionDispatch> CodeExecutor<Blake2Hasher> for NativeExecutor<D> {
	type Error = Error;

	fn call
	<
		E: Externalities<Blake2Hasher>,
		R:Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, &'static str> + UnwindSafe
	>(
		&self,
		ext: &mut E,
		method: &str,
		data: &[u8],
		use_native: bool,
		native_call: Option<NC>,
	) -> (Result<NativeOrEncoded<R>>, bool) {
		RUNTIMES_CACHE.with(|c| {
			let mut c = c.borrow_mut();
			let (module, onchain_version) = match fetch_cached_runtime_version(
				&self.fallback, &mut c, ext, self.default_heap_pages) {
					Ok((module, onchain_version)) => (module, onchain_version),
					Err(e) => return (Err(e), false),
			};
			match (
				use_native,
				onchain_version
					.as_ref()
					.map_or(false, |v| v.can_call_with(&self.native_version.runtime_version)),
				native_call,
			) {
				(_, false, _) => {
					trace!(
						target: "executor",
						"Request for native execution failed (native: {}, chain: {})",
						self.native_version.runtime_version,
						onchain_version
							.as_ref()
							.map_or_else(||"<None>".into(), |v| format!("{}", v))
					);
					(
						self.fallback
							.call_in_wasm_module(ext, module, method, data)
							.map(NativeOrEncoded::Encoded),
						false
					)
				}
				(false, _, _) => {
					(
						self.fallback
							.call_in_wasm_module(ext, module, method, data)
							.map(NativeOrEncoded::Encoded),
						false
					)
				}
				(true, true, Some(call)) => {
					trace!(
						target: "executor",
						"Request for native execution with native call succeeded (native: {}, chain: {}).",
						self.native_version.runtime_version,
						onchain_version
							.as_ref()
							.map_or_else(||"<None>".into(), |v| format!("{}", v))
					);
					(
						with_native_environment(ext, move || (call)())
							.and_then(|r| r.map(NativeOrEncoded::Native).map_err(|s| Error::ApiError(s.to_string()))),
						true
					)
				}
				_ => {
					trace!(
						target: "executor",
						"Request for native execution succeeded (native: {}, chain: {})",
						self.native_version.runtime_version,
						onchain_version.as_ref().map_or_else(||"<None>".into(), |v| format!("{}", v))
					);
					(D::dispatch(ext, method, data).map(NativeOrEncoded::Encoded), true)
				}
			}
		})
	}
}

/// Implements a `NativeExecutionDispatch` for provided parameters.
#[macro_export]
macro_rules! native_executor_instance {
	( $pub:vis $name:ident, $dispatcher:path, $version:path, $code:expr) => {
		/// A unit struct which implements `NativeExecutionDispatch` feeding in the hard-coded runtime.
		$pub struct $name;
		$crate::native_executor_instance!(IMPL $name, $dispatcher, $version, $code);
	};
	(IMPL $name:ident, $dispatcher:path, $version:path, $code:expr) => {
		impl $crate::NativeExecutionDispatch for $name {
			fn native_equivalent() -> &'static [u8] {
				// WARNING!!! This assumes that the runtime was built *before* the main project. Until we
				// get a proper build script, this must be strictly adhered to or things will go wrong.
				$code
			}
			fn dispatch(ext: &mut $crate::Externalities<$crate::Blake2Hasher>, method: &str, data: &[u8]) -> $crate::error::Result<Vec<u8>> {
				$crate::with_native_environment(ext, move || $dispatcher(method, data))?
					.ok_or_else(|| $crate::error::Error::MethodNotFound(method.to_owned()))
			}

			fn native_version() -> $crate::NativeVersion {
				$version()
			}

			fn new(default_heap_pages: Option<u64>) -> $crate::NativeExecutor<$name> {
				$crate::NativeExecutor::new(default_heap_pages)
			}
		}
	}
}
