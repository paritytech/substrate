// Copyright 2017 Parity Technologies (UK) Ltd.
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

use error::{Error, ErrorKind, Result};
use state_machine::{CodeExecutor, Externalities};
use wasm_executor::WasmExecutor;
use wasmi::Module as WasmModule;
use runtime_version::RuntimeVersion;
use std::collections::HashMap;
use codec::Decode;
use twox_hash::XxHash;
use std::hash::Hasher;
use parking_lot::{Mutex, MutexGuard};
use RuntimeInfo;

// For the internal Runtime Cache:
// Is it compatible enough to run this natively or do we need to fall back on the WasmModule
enum Compatibility {
	InvalidVersion(WasmModule),
	IsCompatible(RuntimeVersion),
	NotCompatible(RuntimeVersion, WasmModule)
}

type CacheType = HashMap<u64, Compatibility>;

lazy_static! {
	static ref RUNTIMES_CACHE: Mutex<CacheType> = Mutex::new(HashMap::new());
}

// helper function to generate low-over-head caching_keys
// it is asserted that part of the audit process that any potential on-chain code change
// will have done is to ensure that the two-x hash is different to that of any other
// :code value from the same chain
fn gen_cache_key(code: &[u8]) -> u64 {
	let mut h = XxHash::with_seed(0);
	h.write(code);
	h.finish()
}

/// fetch a runtime version from the cache or if there is no cached version yet, create
/// the runtime version entry for `code`, determines whether `Compatibility::IsCompatible`
/// can be used by by comparing returned RuntimeVersion to `ref_version`
fn fetch_cached_runtime_version<'a, E: Externalities>(
	cache: &'a mut MutexGuard<CacheType>,
	ext: &mut E,
	code: &[u8],
	ref_version: RuntimeVersion
) -> &'a Compatibility {
	cache.entry(gen_cache_key(code))
		.or_insert_with(|| {
			let module = WasmModule::from_buffer(code).expect("all modules compiled with rustc are valid wasm code; qed");
			let version = WasmExecutor::new(8, 8).call_in_wasm_module(ext, &module, "version", &[]).ok()
				.and_then(|v| RuntimeVersion::decode(&mut v.as_slice()));

			if let Some(v) = version {
				if ref_version.can_call_with(&v) {
					Compatibility::IsCompatible(v)
				} else {
					Compatibility::NotCompatible(v, module)
				}
			} else {
				Compatibility::InvalidVersion(module)
			}
	})
}

fn safe_call<F, U>(f: F) -> Result<U>
	where F: ::std::panic::UnwindSafe + FnOnce() -> U
{
	// Substrate uses custom panic hook that terminates process on panic. Disable it for the native call.
	let hook = ::std::panic::take_hook();
	let result = ::std::panic::catch_unwind(f).map_err(|_| ErrorKind::Runtime.into());
	::std::panic::set_hook(hook);
	result
}

/// Set up the externalities and safe calling environment to execute calls to a native runtime.
///
/// If the inner closure panics, it will be caught and return an error.
pub fn with_native_environment<F, U>(ext: &mut Externalities, f: F) -> Result<U>
	where F: ::std::panic::UnwindSafe + FnOnce() -> U
{
	::runtime_io::with_externalities(ext, move || safe_call(f))
}

/// Delegate for dispatching a CodeExecutor call to native code.
pub trait NativeExecutionDispatch: Send + Sync {
	/// Get the wasm code that the native dispatch will be equivalent to.
	fn native_equivalent() -> &'static [u8];

	/// Dispatch a method and input data to be executed natively. Returns `Some` result or `None`
	/// if the `method` is unknown. Panics if there's an unrecoverable error.
	fn dispatch(ext: &mut Externalities, method: &str, data: &[u8]) -> Result<Vec<u8>>;

	/// Get native runtime version.
	const VERSION: RuntimeVersion;

	/// Construct corresponding `NativeExecutor` with given `heap_pages`.
	fn with_heap_pages(min_heap_pages: usize, max_heap_pages: usize) -> NativeExecutor<Self> where Self: Sized {
		NativeExecutor::with_heap_pages(min_heap_pages, max_heap_pages)
	}
}

/// A generic `CodeExecutor` implementation that uses a delegate to determine wasm code equivalence
/// and dispatch to native code when possible, falling back on `WasmExecutor` when not.
#[derive(Debug)]
pub struct NativeExecutor<D: NativeExecutionDispatch> {
	/// Dummy field to avoid the compiler complaining about us not using `D`.
	_dummy: ::std::marker::PhantomData<D>,
	/// The fallback executor in case native isn't available.
	fallback: WasmExecutor,
}

impl<D: NativeExecutionDispatch> NativeExecutor<D> {
	/// Create new instance with specific number of pages for wasm fallback's heap.
	pub fn with_heap_pages(min_heap_pages: usize, max_heap_pages: usize) -> Self {
		// FIXME: set this entry at compile time
		RUNTIMES_CACHE.lock().insert(
			gen_cache_key(D::native_equivalent()),
			Compatibility::IsCompatible(D::VERSION));

		NativeExecutor {
			_dummy: Default::default(),
			fallback: WasmExecutor::new(min_heap_pages, max_heap_pages),
		}
	}
}

impl<D: NativeExecutionDispatch> Clone for NativeExecutor<D> {
	fn clone(&self) -> Self {
		NativeExecutor {
			_dummy: Default::default(),
			fallback: self.fallback.clone(),
		}
	}
}

impl<D: NativeExecutionDispatch> RuntimeInfo for NativeExecutor<D> {
	const NATIVE_VERSION: Option<RuntimeVersion> = Some(D::VERSION);

	fn runtime_version<E: Externalities>(
		&self,
		ext: &mut E,
		code: &[u8],
	) -> Option<RuntimeVersion> {
		let mut c = RUNTIMES_CACHE.lock();
		match fetch_cached_runtime_version(&mut c, ext, code, D::VERSION) {
			Compatibility::IsCompatible(v) | Compatibility::NotCompatible(v, _) => Some(v.clone()),
			Compatibility::InvalidVersion(_m) => None
		}
	}
}

impl<D: NativeExecutionDispatch> CodeExecutor for NativeExecutor<D> {
	type Error = Error;

	fn call<E: Externalities>(
		&self,
		ext: &mut E,
		code: &[u8],
		method: &str,
		data: &[u8],
		use_native: bool,
	) -> (Result<Vec<u8>>, bool) {
		let mut c = RUNTIMES_CACHE.lock();
		match (use_native, fetch_cached_runtime_version(&mut c, ext, code, D::VERSION)) {
			(_, Compatibility::NotCompatible(_, m)) | (_, Compatibility::InvalidVersion(m)) =>
				(self.fallback.call_in_wasm_module(ext, m, method, data), false),
			(false, _) =>
				(self.fallback.call(ext, code, method, data, false).0, false),
			_ => (D::dispatch(ext, method, data), true),
		}
	}
}

#[macro_export]
macro_rules! native_executor_instance {
	(pub $name:ident, $dispatcher:path, $version:path, $code:expr) => {
		pub struct $name;
		native_executor_instance!(IMPL $name, $dispatcher, $version, $code);
	};
	($name:ident, $dispatcher:path, $version:path, $code:expr) => {
		/// A unit struct which implements `NativeExecutionDispatch` feeding in the hard-coded runtime.
		struct $name;
		native_executor_instance!(IMPL $name, $dispatcher, $version, $code);
	};
	(IMPL $name:ident, $dispatcher:path, $version:path, $code:expr) => {
		impl $crate::NativeExecutionDispatch for $name {
			const VERSION: $crate::RuntimeVersion = $version;
			fn native_equivalent() -> &'static [u8] {
				// WARNING!!! This assumes that the runtime was built *before* the main project. Until we
				// get a proper build script, this must be strictly adhered to or things will go wrong.
				$code
			}

			fn dispatch(ext: &mut $crate::Externalities, method: &str, data: &[u8]) -> $crate::error::Result<Vec<u8>> {
				$crate::with_native_environment(ext, move || $dispatcher(method, data))?
					.ok_or_else(|| $crate::error::ErrorKind::MethodNotFound(method.to_owned()).into())
			}

			fn with_heap_pages(min_heap_pages: usize, max_heap_pages: usize) -> $crate::NativeExecutor<$name> {
				$crate::NativeExecutor::with_heap_pages(min_heap_pages, max_heap_pages)
			}
		}
	}
}
