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

use std::{result, cell::RefCell, panic::{UnwindSafe, AssertUnwindSafe}};
use crate::error::{Error, Result};
use crate::wasm_runtime::{RuntimesCache, WasmExecutionMethod, WasmRuntime};
use crate::RuntimeInfo;
use runtime_version::{NativeVersion, RuntimeVersion};
use codec::{Decode, Encode};
use primitives::{NativeOrEncoded, traits::{CodeExecutor, Externalities}};
use log::{trace, warn};

thread_local! {
	static RUNTIMES_CACHE: RefCell<RuntimesCache> = RefCell::new(RuntimesCache::new());
}

/// Default num of pages for the heap
const DEFAULT_HEAP_PAGES: u64 = 1024;

pub(crate) fn safe_call<F, U>(f: F) -> Result<U>
	where F: UnwindSafe + FnOnce() -> U
{
	// Substrate uses custom panic hook that terminates process on panic. Disable termination for the native call.
	let _guard = panic_handler::AbortGuard::force_unwind();
	std::panic::catch_unwind(f).map_err(|_| Error::Runtime)
}

/// Set up the externalities and safe calling environment to execute calls to a native runtime.
///
/// If the inner closure panics, it will be caught and return an error.
pub fn with_native_environment<F, U>(ext: &mut dyn Externalities, f: F) -> Result<U>
	where F: UnwindSafe + FnOnce() -> U
{
	externalities::set_and_run_with_externalities(ext, move || safe_call(f))
}

/// Delegate for dispatching a CodeExecutor call.
///
/// By dispatching we mean that we execute a runtime function specified by it's name.
pub trait NativeExecutionDispatch: Send + Sync {
	/// Dispatch a method in the runtime.
	///
	/// If the method with the specified name doesn't exist then `Err` is returned.
	fn dispatch(ext: &mut dyn Externalities, method: &str, data: &[u8]) -> Result<Vec<u8>>;

	/// Provide native runtime version.
	fn native_version() -> NativeVersion;
}

/// A generic `CodeExecutor` implementation that uses a delegate to determine wasm code equivalence
/// and dispatch to native code when possible, falling back on `WasmExecutor` when not.
#[derive(Debug)]
pub struct NativeExecutor<D> {
	/// Dummy field to avoid the compiler complaining about us not using `D`.
	_dummy: std::marker::PhantomData<D>,
	/// Method used to execute fallback Wasm code.
	fallback_method: WasmExecutionMethod,
	/// Native runtime version info.
	native_version: NativeVersion,
	/// The number of 64KB pages to allocate for Wasm execution.
	default_heap_pages: u64,
}

impl<D: NativeExecutionDispatch> NativeExecutor<D> {
	/// Create new instance.
	///
	/// # Parameters
	///
	/// `fallback_method` - Method used to execute fallback Wasm code.
	///
	/// `default_heap_pages` - Number of 64KB pages to allocate for Wasm execution.
	/// 	Defaults to `DEFAULT_HEAP_PAGES` if `None` is provided.
	pub fn new(fallback_method: WasmExecutionMethod, default_heap_pages: Option<u64>) -> Self {
		NativeExecutor {
			_dummy: Default::default(),
			fallback_method,
			native_version: D::native_version(),
			default_heap_pages: default_heap_pages.unwrap_or(DEFAULT_HEAP_PAGES),
		}
	}

	/// Execute the given closure `f` with the latest runtime (based on the `CODE` key in `ext`).
	///
	/// The closure `f` is expected to return `Err(_)` when there happened a `panic!` in native code
	/// while executing the runtime in Wasm. If a `panic!` occurred, the runtime is invalidated to
	/// prevent any poisoned state. Native runtime execution does not need to report back
	/// any `panic!`.
	///
	/// # Safety
	///
	/// `runtime` and `ext` are given as `AssertUnwindSafe` to the closure. As described above, the
	/// runtime is invalidated on any `panic!` to prevent a poisoned state. `ext` is already
	/// implicitly handled as unwind safe, as we store it in a global variable while executing the
	/// native runtime.
	fn with_runtime<E, R>(
		&self,
		ext: &mut E,
		f: impl for<'a> FnOnce(
			AssertUnwindSafe<&'a mut (dyn WasmRuntime + 'static)>,
			AssertUnwindSafe<&'a mut E>,
		) -> Result<Result<R>>,
	) -> Result<R> where E: Externalities {
		RUNTIMES_CACHE.with(|cache| {
			let mut cache = cache.borrow_mut();
			let (runtime, code_hash) = cache.fetch_runtime(
				ext,
				self.fallback_method,
				self.default_heap_pages,
			)?;

			let runtime = AssertUnwindSafe(runtime);
			let ext = AssertUnwindSafe(ext);

			match f(runtime, ext) {
				Ok(res) => res,
				Err(e) => {
					cache.invalidate_runtime(self.fallback_method, code_hash);
					Err(e)
				}
			}
		})
	}
}

impl<D: NativeExecutionDispatch> Clone for NativeExecutor<D> {
	fn clone(&self) -> Self {
		NativeExecutor {
			_dummy: Default::default(),
			fallback_method: self.fallback_method,
			native_version: D::native_version(),
			default_heap_pages: self.default_heap_pages,
		}
	}
}

impl<D: NativeExecutionDispatch> RuntimeInfo for NativeExecutor<D> {
	fn native_version(&self) -> &NativeVersion {
		&self.native_version
	}

	fn runtime_version<E: Externalities>(
		&self,
		ext: &mut E,
	) -> Option<RuntimeVersion> {
		match self.with_runtime(ext, |runtime, _ext| Ok(Ok(runtime.version()))) {
			Ok(version) => version,
			Err(e) => {
				warn!(target: "executor", "Failed to fetch runtime: {:?}", e);
				None
			}
		}
	}
}

impl<D: NativeExecutionDispatch> CodeExecutor for NativeExecutor<D> {
	type Error = Error;

	fn call
	<
		E: Externalities,
		R: Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
	>(
		&self,
		ext: &mut E,
		method: &str,
		data: &[u8],
		use_native: bool,
		native_call: Option<NC>,
	) -> (Result<NativeOrEncoded<R>>, bool){
		let mut used_native = false;
		let result = self.with_runtime(ext, |mut runtime, mut ext| {
			let onchain_version = runtime.version();
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

					safe_call(
						move || runtime.call(&mut **ext, method, data).map(NativeOrEncoded::Encoded)
					)
				}
				(false, _, _) => {
					safe_call(
						move || runtime.call(&mut **ext, method, data).map(NativeOrEncoded::Encoded)
					)
				},
				(true, true, Some(call)) => {
					trace!(
						target: "executor",
						"Request for native execution with native call succeeded (native: {}, chain: {}).",
						self.native_version.runtime_version,
						onchain_version
							.as_ref()
							.map_or_else(||"<None>".into(), |v| format!("{}", v))
					);

					used_native = true;
					let res = with_native_environment(&mut **ext, move || (call)())
						.and_then(|r| r
							.map(NativeOrEncoded::Native)
							.map_err(|s| Error::ApiError(s.to_string()))
						);

					Ok(res)
				}
				_ => {
					trace!(
						target: "executor",
						"Request for native execution succeeded (native: {}, chain: {})",
						self.native_version.runtime_version,
						onchain_version.as_ref().map_or_else(||"<None>".into(), |v| format!("{}", v))
					);

					used_native = true;
					Ok(D::dispatch(&mut **ext, method, data).map(NativeOrEncoded::Encoded))
				}
			}
		});
		(result, used_native)
	}
}

/// Implements a `NativeExecutionDispatch` for provided parameters.
#[macro_export]
macro_rules! native_executor_instance {
	( $pub:vis $name:ident, $dispatcher:path, $version:path $(,)?) => {
		/// A unit struct which implements `NativeExecutionDispatch` feeding in the hard-coded runtime.
		$pub struct $name;
		$crate::native_executor_instance!(IMPL $name, $dispatcher, $version);
	};
	(IMPL $name:ident, $dispatcher:path, $version:path) => {
		impl $crate::NativeExecutionDispatch for $name {
			fn dispatch(
				ext: &mut $crate::Externalities,
				method: &str,
				data: &[u8]
			) -> $crate::error::Result<Vec<u8>> {
				$crate::with_native_environment(ext, move || $dispatcher(method, data))?
					.ok_or_else(|| $crate::error::Error::MethodNotFound(method.to_owned()))
			}

			fn native_version() -> $crate::NativeVersion {
				$version()
			}
		}
	}
}
