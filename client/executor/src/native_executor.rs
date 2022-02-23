// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use crate::{
	error::{Error, Result},
	wasm_runtime::{RuntimeCache, WasmExecutionMethod},
	RuntimeVersionOf,
};

use std::{
	collections::HashMap,
	marker::PhantomData,
	panic::{AssertUnwindSafe, UnwindSafe},
	path::PathBuf,
	result,
	sync::{
		atomic::{AtomicU64, Ordering},
		mpsc, Arc,
	},
};

use codec::{Decode, Encode};
use sc_executor_common::{
	runtime_blob::RuntimeBlob,
	wasm_runtime::{InvokeMethod, WasmInstance, WasmModule},
};
use sp_core::{
	traits::{CodeExecutor, Externalities, RuntimeCode, RuntimeSpawn, RuntimeSpawnExt},
	NativeOrEncoded,
};
use sp_externalities::ExternalitiesExt as _;
use sp_tasks::new_async_externalities;
use sp_version::{GetNativeVersion, NativeVersion, RuntimeVersion};
use sp_wasm_interface::{ExtendedHostFunctions, HostFunctions};

/// Default num of pages for the heap
const DEFAULT_HEAP_PAGES: u64 = 2048;

/// Set up the externalities and safe calling environment to execute runtime calls.
///
/// If the inner closure panics, it will be caught and return an error.
pub fn with_externalities_safe<F, U>(ext: &mut dyn Externalities, f: F) -> Result<U>
where
	F: UnwindSafe + FnOnce() -> U,
{
	sp_externalities::set_and_run_with_externalities(ext, move || {
		// Substrate uses custom panic hook that terminates process on panic. Disable
		// termination for the native call.
		let _guard = sp_panic_handler::AbortGuard::force_unwind();
		std::panic::catch_unwind(f).map_err(|e| {
			if let Some(err) = e.downcast_ref::<String>() {
				Error::RuntimePanicked(err.clone())
			} else if let Some(err) = e.downcast_ref::<&'static str>() {
				Error::RuntimePanicked(err.to_string())
			} else {
				Error::RuntimePanicked("Unknown panic".into())
			}
		})
	})
}

/// Delegate for dispatching a CodeExecutor call.
///
/// By dispatching we mean that we execute a runtime function specified by it's name.
pub trait NativeExecutionDispatch: Send + Sync {
	/// Host functions for custom runtime interfaces that should be callable from within the runtime
	/// besides the default Substrate runtime interfaces.
	type ExtendHostFunctions: HostFunctions;

	/// Dispatch a method in the runtime.
	fn dispatch(method: &str, data: &[u8]) -> Option<Vec<u8>>;

	/// Provide native runtime version.
	fn native_version() -> NativeVersion;
}

/// An abstraction over Wasm code executor. Supports selecting execution backend and
/// manages runtime cache.
pub struct WasmExecutor<H> {
	/// Method used to execute fallback Wasm code.
	method: WasmExecutionMethod,
	/// The number of 64KB pages to allocate for Wasm execution.
	default_heap_pages: u64,
	/// WASM runtime cache.
	cache: Arc<RuntimeCache>,
	/// The path to a directory which the executor can leverage for a file cache, e.g. put there
	/// compiled artifacts.
	cache_path: Option<PathBuf>,

	phantom: PhantomData<H>,
}

impl<H> Clone for WasmExecutor<H> {
	fn clone(&self) -> Self {
		Self {
			method: self.method,
			default_heap_pages: self.default_heap_pages,
			cache: self.cache.clone(),
			cache_path: self.cache_path.clone(),
			phantom: self.phantom,
		}
	}
}

impl<H> WasmExecutor<H>
where
	H: HostFunctions,
{
	/// Create new instance.
	///
	/// # Parameters
	///
	/// `method` - Method used to execute Wasm code.
	///
	/// `default_heap_pages` - Number of 64KB pages to allocate for Wasm execution.
	///   Defaults to `DEFAULT_HEAP_PAGES` if `None` is provided.
	///
	/// `host_functions` - The set of host functions to be available for import provided by this
	///   executor.
	///
	/// `max_runtime_instances` - The number of runtime instances to keep in memory ready for reuse.
	///
	/// `cache_path` - A path to a directory where the executor can place its files for purposes of
	///   caching. This may be important in cases when there are many different modules with the
	///   compiled execution method is used.
	pub fn new(
		method: WasmExecutionMethod,
		default_heap_pages: Option<u64>,
		max_runtime_instances: usize,
		cache_path: Option<PathBuf>,
		runtime_cache_size: u8,
	) -> Self {
		WasmExecutor {
			method,
			default_heap_pages: default_heap_pages.unwrap_or(DEFAULT_HEAP_PAGES),
			cache: Arc::new(RuntimeCache::new(
				max_runtime_instances,
				cache_path.clone(),
				runtime_cache_size,
			)),
			cache_path,
			phantom: PhantomData,
		}
	}

	/// Execute the given closure `f` with the latest runtime (based on `runtime_code`).
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
	fn with_instance<R, F>(
		&self,
		runtime_code: &RuntimeCode,
		ext: &mut dyn Externalities,
		allow_missing_host_functions: bool,
		f: F,
	) -> Result<R>
	where
		F: FnOnce(
			AssertUnwindSafe<&Arc<dyn WasmModule>>,
			AssertUnwindSafe<&mut dyn WasmInstance>,
			Option<&RuntimeVersion>,
			AssertUnwindSafe<&mut dyn Externalities>,
		) -> Result<Result<R>>,
	{
		match self.cache.with_instance::<H, _, _>(
			runtime_code,
			ext,
			self.method,
			self.default_heap_pages,
			allow_missing_host_functions,
			|module, instance, version, ext| {
				let module = AssertUnwindSafe(module);
				let instance = AssertUnwindSafe(instance);
				let ext = AssertUnwindSafe(ext);
				f(module, instance, version, ext)
			},
		)? {
			Ok(r) => r,
			Err(e) => Err(e),
		}
	}

	/// Perform a call into the given runtime.
	///
	/// The runtime is passed as a [`RuntimeBlob`]. The runtime will be instantiated with the
	/// parameters this `WasmExecutor` was initialized with.
	///
	/// In case of problems with during creation of the runtime or instantation, a `Err` is
	/// returned. that describes the message.
	#[doc(hidden)] // We use this function for tests across multiple crates.
	pub fn uncached_call(
		&self,
		runtime_blob: RuntimeBlob,
		ext: &mut dyn Externalities,
		allow_missing_host_functions: bool,
		export_name: &str,
		call_data: &[u8],
	) -> std::result::Result<Vec<u8>, Error> {
		let module = crate::wasm_runtime::create_wasm_runtime_with_code::<H>(
			self.method,
			self.default_heap_pages,
			runtime_blob,
			allow_missing_host_functions,
			self.cache_path.as_deref(),
		)
		.map_err(|e| format!("Failed to create module: {}", e))?;

		let instance =
			module.new_instance().map_err(|e| format!("Failed to create instance: {}", e))?;

		let mut instance = AssertUnwindSafe(instance);
		let mut ext = AssertUnwindSafe(ext);
		let module = AssertUnwindSafe(module);

		with_externalities_safe(&mut **ext, move || {
			preregister_builtin_ext(module.clone());
			instance.call_export(export_name, call_data)
		})
		.and_then(|r| r)
	}
}

impl<H> sp_core::traits::ReadRuntimeVersion for WasmExecutor<H>
where
	H: HostFunctions,
{
	fn read_runtime_version(
		&self,
		wasm_code: &[u8],
		ext: &mut dyn Externalities,
	) -> std::result::Result<Vec<u8>, String> {
		let runtime_blob = RuntimeBlob::uncompress_if_needed(&wasm_code)
			.map_err(|e| format!("Failed to create runtime blob: {:?}", e))?;

		if let Some(version) = crate::wasm_runtime::read_embedded_version(&runtime_blob)
			.map_err(|e| format!("Failed to read the static section: {:?}", e))
			.map(|v| v.map(|v| v.encode()))?
		{
			return Ok(version)
		}

		// If the blob didn't have embedded runtime version section, we fallback to the legacy
		// way of fetching the version: i.e. instantiating the given instance and calling
		// `Core_version` on it.

		self.uncached_call(
			runtime_blob,
			ext,
			// If a runtime upgrade introduces new host functions that are not provided by
			// the node, we should not fail at instantiation. Otherwise nodes that are
			// updated could run this successfully and it could lead to a storage root
			// mismatch when importing this block.
			true,
			"Core_version",
			&[],
		)
		.map_err(|e| e.to_string())
	}
}

impl<H> CodeExecutor for WasmExecutor<H>
where
	H: HostFunctions,
{
	type Error = Error;

	fn call<
		R: Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, Box<dyn std::error::Error + Send + Sync>> + UnwindSafe,
	>(
		&self,
		ext: &mut dyn Externalities,
		runtime_code: &RuntimeCode,
		method: &str,
		data: &[u8],
		_use_native: bool,
		_native_call: Option<NC>,
	) -> (Result<NativeOrEncoded<R>>, bool) {
		tracing::trace!(
			target: "executor",
			%method,
			"Executing function",
		);

		let result = self.with_instance(
			runtime_code,
			ext,
			false,
			|module, mut instance, _onchain_version, mut ext| {
				with_externalities_safe(&mut **ext, move || {
					preregister_builtin_ext(module.clone());
					instance.call_export(method, data).map(NativeOrEncoded::Encoded)
				})
			},
		);
		(result, false)
	}
}

impl<H> RuntimeVersionOf for WasmExecutor<H>
where
	H: HostFunctions,
{
	fn runtime_version(
		&self,
		ext: &mut dyn Externalities,
		runtime_code: &RuntimeCode,
	) -> Result<RuntimeVersion> {
		self.with_instance(runtime_code, ext, false, |_module, _instance, version, _ext| {
			Ok(version.cloned().ok_or_else(|| Error::ApiError("Unknown version".into())))
		})
	}
}

/// A generic `CodeExecutor` implementation that uses a delegate to determine wasm code equivalence
/// and dispatch to native code when possible, falling back on `WasmExecutor` when not.
pub struct NativeElseWasmExecutor<D>
where
	D: NativeExecutionDispatch,
{
	/// Dummy field to avoid the compiler complaining about us not using `D`.
	_dummy: std::marker::PhantomData<D>,
	/// Native runtime version info.
	native_version: NativeVersion,
	/// Fallback wasm executor.
	wasm:
		WasmExecutor<ExtendedHostFunctions<sp_io::SubstrateHostFunctions, D::ExtendHostFunctions>>,
}

impl<D: NativeExecutionDispatch> NativeElseWasmExecutor<D> {
	/// Create new instance.
	///
	/// # Parameters
	///
	/// `fallback_method` - Method used to execute fallback Wasm code.
	///
	/// `default_heap_pages` - Number of 64KB pages to allocate for Wasm execution.
	/// 	Defaults to `DEFAULT_HEAP_PAGES` if `None` is provided.
	pub fn new(
		fallback_method: WasmExecutionMethod,
		default_heap_pages: Option<u64>,
		max_runtime_instances: usize,
		runtime_cache_size: u8,
	) -> Self {
		let wasm_executor = WasmExecutor::new(
			fallback_method,
			default_heap_pages,
			max_runtime_instances,
			None,
			runtime_cache_size,
		);

		NativeElseWasmExecutor {
			_dummy: Default::default(),
			native_version: D::native_version(),
			wasm: wasm_executor,
		}
	}
}

impl<D: NativeExecutionDispatch> RuntimeVersionOf for NativeElseWasmExecutor<D> {
	fn runtime_version(
		&self,
		ext: &mut dyn Externalities,
		runtime_code: &RuntimeCode,
	) -> Result<RuntimeVersion> {
		self.wasm
			.with_instance(runtime_code, ext, false, |_module, _instance, version, _ext| {
				Ok(version.cloned().ok_or_else(|| Error::ApiError("Unknown version".into())))
			})
	}
}

impl<D: NativeExecutionDispatch> GetNativeVersion for NativeElseWasmExecutor<D> {
	fn native_version(&self) -> &NativeVersion {
		&self.native_version
	}
}

/// Helper inner struct to implement `RuntimeSpawn` extension.
pub struct RuntimeInstanceSpawn {
	module: Arc<dyn WasmModule>,
	tasks: parking_lot::Mutex<HashMap<u64, mpsc::Receiver<Vec<u8>>>>,
	counter: AtomicU64,
	scheduler: Box<dyn sp_core::traits::SpawnNamed>,
}

impl RuntimeSpawn for RuntimeInstanceSpawn {
	fn spawn_call(&self, dispatcher_ref: u32, func: u32, data: Vec<u8>) -> u64 {
		let new_handle = self.counter.fetch_add(1, Ordering::Relaxed);

		let (sender, receiver) = mpsc::channel();
		self.tasks.lock().insert(new_handle, receiver);

		let module = self.module.clone();
		let scheduler = self.scheduler.clone();
		self.scheduler.spawn(
			"executor-extra-runtime-instance",
			None,
			Box::pin(async move {
				let module = AssertUnwindSafe(module);

				let async_ext = match new_async_externalities(scheduler.clone()) {
					Ok(val) => val,
					Err(e) => {
						tracing::error!(
							target: "executor",
							error = %e,
							"Failed to setup externalities for async context.",
						);

						// This will drop sender and receiver end will panic
						return
					},
				};

				let mut async_ext = match async_ext.with_runtime_spawn(Box::new(
					RuntimeInstanceSpawn::new(module.clone(), scheduler),
				)) {
					Ok(val) => val,
					Err(e) => {
						tracing::error!(
							target: "executor",
							error = %e,
							"Failed to setup runtime extension for async externalities",
						);

						// This will drop sender and receiver end will panic
						return
					},
				};

				let result = with_externalities_safe(&mut async_ext, move || {
					// FIXME: Should be refactored to shared "instance factory".
					// Instantiating wasm here every time is suboptimal at the moment, shared
					// pool of instances should be used.
					//
					// https://github.com/paritytech/substrate/issues/7354
					let mut instance = match module.new_instance() {
						Ok(instance) => instance,
						Err(error) =>
							panic!("failed to create new instance from module: {}", error),
					};

					match instance
						.call(InvokeMethod::TableWithWrapper { dispatcher_ref, func }, &data[..])
					{
						Ok(result) => result,
						Err(error) => panic!("failed to invoke instance: {}", error),
					}
				});

				match result {
					Ok(output) => {
						let _ = sender.send(output);
					},
					Err(error) => {
						// If execution is panicked, the `join` in the original runtime code will
						// panic as well, since the sender is dropped without sending anything.
						tracing::error!(error = %error, "Call error in spawned task");
					},
				}
			}),
		);

		new_handle
	}

	fn join(&self, handle: u64) -> Vec<u8> {
		let receiver = self.tasks.lock().remove(&handle).expect("No task for the handle");
		let output = receiver.recv().expect("Spawned task panicked for the handle");
		output
	}
}

impl RuntimeInstanceSpawn {
	pub fn new(
		module: Arc<dyn WasmModule>,
		scheduler: Box<dyn sp_core::traits::SpawnNamed>,
	) -> Self {
		Self { module, scheduler, counter: 0.into(), tasks: HashMap::new().into() }
	}

	fn with_externalities_and_module(
		module: Arc<dyn WasmModule>,
		mut ext: &mut dyn Externalities,
	) -> Option<Self> {
		ext.extension::<sp_core::traits::TaskExecutorExt>()
			.map(move |task_ext| Self::new(module, task_ext.clone()))
	}
}

/// Pre-registers the built-in extensions to the currently effective externalities.
///
/// Meant to be called each time before calling into the runtime.
fn preregister_builtin_ext(module: Arc<dyn WasmModule>) {
	sp_externalities::with_externalities(move |mut ext| {
		if let Some(runtime_spawn) =
			RuntimeInstanceSpawn::with_externalities_and_module(module, ext)
		{
			if let Err(e) = ext.register_extension(RuntimeSpawnExt(Box::new(runtime_spawn))) {
				tracing::trace!(
					target: "executor",
					error = ?e,
					"Failed to register `RuntimeSpawnExt` instance on externalities",
				)
			}
		}
	});
}

impl<D: NativeExecutionDispatch + 'static> CodeExecutor for NativeElseWasmExecutor<D> {
	type Error = Error;

	fn call<
		R: Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, Box<dyn std::error::Error + Send + Sync>> + UnwindSafe,
	>(
		&self,
		ext: &mut dyn Externalities,
		runtime_code: &RuntimeCode,
		method: &str,
		data: &[u8],
		use_native: bool,
		native_call: Option<NC>,
	) -> (Result<NativeOrEncoded<R>>, bool) {
		tracing::trace!(
			target: "executor",
			function = %method,
			"Executing function",
		);

		let mut used_native = false;
		let result = self.wasm.with_instance(
			runtime_code,
			ext,
			false,
			|module, mut instance, onchain_version, mut ext| {
				let onchain_version =
					onchain_version.ok_or_else(|| Error::ApiError("Unknown version".into()))?;

				let can_call_with =
					onchain_version.can_call_with(&self.native_version.runtime_version);

				match (use_native, can_call_with, native_call) {
					(_, false, _) | (false, _, _) => {
						if !can_call_with {
							tracing::trace!(
								target: "executor",
								native = %self.native_version.runtime_version,
								chain = %onchain_version,
								"Request for native execution failed",
							);
						}

						with_externalities_safe(&mut **ext, move || {
							preregister_builtin_ext(module.clone());
							instance.call_export(method, data).map(NativeOrEncoded::Encoded)
						})
					},
					(true, true, Some(call)) => {
						tracing::trace!(
							target: "executor",
							native = %self.native_version.runtime_version,
							chain = %onchain_version,
							"Request for native execution with native call succeeded"
						);

						used_native = true;
						let res = with_externalities_safe(&mut **ext, move || (call)())
							.and_then(|r| r.map(NativeOrEncoded::Native).map_err(Error::ApiError));

						Ok(res)
					},
					_ => {
						tracing::trace!(
							target: "executor",
							native = %self.native_version.runtime_version,
							chain = %onchain_version,
							"Request for native execution succeeded",
						);

						used_native = true;
						Ok(with_externalities_safe(&mut **ext, move || D::dispatch(method, data))?
							.map(NativeOrEncoded::Encoded)
							.ok_or_else(|| Error::MethodNotFound(method.to_owned())))
					},
				}
			},
		);
		(result, used_native)
	}
}

impl<D: NativeExecutionDispatch> Clone for NativeElseWasmExecutor<D> {
	fn clone(&self) -> Self {
		NativeElseWasmExecutor {
			_dummy: Default::default(),
			native_version: D::native_version(),
			wasm: self.wasm.clone(),
		}
	}
}

impl<D: NativeExecutionDispatch> sp_core::traits::ReadRuntimeVersion for NativeElseWasmExecutor<D> {
	fn read_runtime_version(
		&self,
		wasm_code: &[u8],
		ext: &mut dyn Externalities,
	) -> std::result::Result<Vec<u8>, String> {
		self.wasm.read_runtime_version(wasm_code, ext)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime_interface::runtime_interface;

	#[runtime_interface]
	trait MyInterface {
		fn say_hello_world(data: &str) {
			println!("Hello world from: {}", data);
		}
	}

	pub struct MyExecutorDispatch;

	impl NativeExecutionDispatch for MyExecutorDispatch {
		type ExtendHostFunctions = (my_interface::HostFunctions, my_interface::HostFunctions);

		fn dispatch(method: &str, data: &[u8]) -> Option<Vec<u8>> {
			substrate_test_runtime::api::dispatch(method, data)
		}

		fn native_version() -> NativeVersion {
			substrate_test_runtime::native_version()
		}
	}

	#[test]
	fn native_executor_registers_custom_interface() {
		let executor = NativeElseWasmExecutor::<MyExecutorDispatch>::new(
			WasmExecutionMethod::Interpreted,
			None,
			8,
			2,
		);

		fn extract_host_functions<H>(
			_: &WasmExecutor<H>,
		) -> Vec<&'static dyn sp_wasm_interface::Function>
		where
			H: HostFunctions,
		{
			H::host_functions()
		}

		my_interface::HostFunctions::host_functions().iter().for_each(|function| {
			assert_eq!(
				extract_host_functions(&executor.wasm).iter().filter(|f| f == &function).count(),
				2
			);
		});

		my_interface::say_hello_world("hey");
	}
}
