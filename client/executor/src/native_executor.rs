// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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
	RuntimeInfo, error::{Error, Result},
	wasm_runtime::{RuntimeCache, WasmExecutionMethod},
};

use std::{
	collections::HashMap,
	panic::{UnwindSafe, AssertUnwindSafe},
	result,
	sync::{Arc, atomic::{AtomicU64, Ordering}, mpsc},
};

use sp_version::{NativeVersion, RuntimeVersion};
use codec::{Decode, Encode};
use sp_core::{
	NativeOrEncoded,
	traits::{
		CodeExecutor, Externalities, RuntimeCode, MissingHostFunctions,
		RuntimeSpawnExt, RuntimeSpawn, RemoteHandle, BoxFuture,
	},
};
use log::trace;
use sp_wasm_interface::{HostFunctions, Function};
use sc_executor_common::wasm_runtime::{WasmInstance, WasmModule};
use sp_externalities::{ExternalitiesExt as _, WorkerResult};
use sp_tasks::{new_async_externalities, AsyncExt};
use sc_executor_common::inline_spawn::{WasmTask, NativeTask, Task, PendingTask as InlineTask, spawn_call_ext};

/// Default num of pages for the heap
const DEFAULT_HEAP_PAGES: u64 = 1024;

/// Set up the externalities and safe calling environment to execute runtime calls.
///
/// If the inner closure panics, it will be caught and return an error.
pub fn with_externalities_safe<F, U>(ext: &mut dyn Externalities, f: F) -> Result<U>
	where F: UnwindSafe + FnOnce() -> U
{
	Ok(sc_executor_common::inline_spawn::with_externalities_safe(ext, f)?)
}

fn instantiate_inline(
	module: &Option<Arc<dyn WasmModule>>,
) -> Option<AssertUnwindSafe<Box<dyn WasmInstance>>> {
	sc_executor_common::inline_spawn::instantiate(module.as_ref().map(AsRef::as_ref))
}

/// Delegate for dispatching a CodeExecutor call.
///
/// By dispatching we mean that we execute a runtime function specified by it's name.
pub trait NativeExecutionDispatch: Send + Sync {
	/// Host functions for custom runtime interfaces that should be callable from within the runtime
	/// besides the default Substrate runtime interfaces.
	type ExtendHostFunctions: HostFunctions;

	/// Dispatch a method in the runtime.
	///
	/// If the method with the specified name doesn't exist then `Err` is returned.
	fn dispatch(ext: &mut dyn Externalities, method: &str, data: &[u8]) -> Result<Vec<u8>>;

	/// Provide native runtime version.
	fn native_version() -> NativeVersion;
}

/// An abstraction over Wasm code executor. Supports selecting execution backend and
/// manages runtime cache.
#[derive(Clone)]
pub struct WasmExecutor {
	/// Method used to execute fallback Wasm code.
	method: WasmExecutionMethod,
	/// The number of 64KB pages to allocate for Wasm execution.
	default_heap_pages: u64,
	/// The host functions registered with this instance.
	host_functions: Arc<Vec<&'static dyn Function>>,
	/// WASM runtime cache.
	cache: Arc<RuntimeCache>,
	/// The size of the instances cache.
	max_runtime_instances: usize,
}

impl WasmExecutor {
	/// Create new instance.
	///
	/// # Parameters
	///
	/// `method` - Method used to execute Wasm code.
	///
	/// `default_heap_pages` - Number of 64KB pages to allocate for Wasm execution.
	/// 	Defaults to `DEFAULT_HEAP_PAGES` if `None` is provided.
	pub fn new(
		method: WasmExecutionMethod,
		default_heap_pages: Option<u64>,
		host_functions: Vec<&'static dyn Function>,
		max_runtime_instances: usize,
	) -> Self {
		WasmExecutor {
			method,
			default_heap_pages: default_heap_pages.unwrap_or(DEFAULT_HEAP_PAGES),
			host_functions: Arc::new(host_functions),
			cache: Arc::new(RuntimeCache::new(max_runtime_instances)),
			max_runtime_instances,
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
		where F: FnOnce(
			AssertUnwindSafe<&Arc<dyn WasmModule>>,
			AssertUnwindSafe<&dyn WasmInstance>,
			Option<&RuntimeVersion>,
			AssertUnwindSafe<&mut dyn Externalities>,
		) -> Result<Result<R>>,
	{
		match self.cache.with_instance(
			runtime_code,
			ext,
			self.method,
			self.default_heap_pages,
			&*self.host_functions,
			allow_missing_host_functions,
			|module, instance, version, ext| {
				let module = AssertUnwindSafe(module);
				let instance = AssertUnwindSafe(instance);
				let ext = AssertUnwindSafe(ext);
				f(module, instance, version, ext)
			}
		)? {
			Ok(r) => r,
			Err(e) => Err(e),
		}
	}
}

struct InlineInstantiate<'a, 'b> {
	module: &'a Option<Arc<dyn WasmModule>>,
	guard: &'a mut parking_lot::MutexGuard<'b, Option<AssertUnwindSafe<Box<dyn WasmInstance>>>>,
}

impl<'a, 'b> sc_executor_common::inline_spawn::LazyInstanciate<'a> for InlineInstantiate<'a, 'b> {
	fn instantiate(self) -> Option<&'a AssertUnwindSafe<Box<dyn WasmInstance>>> {
		if self.guard.is_none() {
			**self.guard = if let Some(instance) = instantiate_inline(self.module) {
				Some(instance)
			} else {
				return None;
			};
		}

		self.guard.as_ref()
	}
}

struct InlineInstantiateRef<'a> {
	module: &'a Option<Arc<dyn WasmModule>>,
	instance: &'a mut Option<AssertUnwindSafe<Box<dyn WasmInstance>>>,
}

impl<'a> sc_executor_common::inline_spawn::LazyInstanciate<'a> for InlineInstantiateRef<'a> {
	fn instantiate(self) -> Option<&'a AssertUnwindSafe<Box<dyn WasmInstance>>> {
		if self.instance.is_none() {
			*self.instance = if let Some(instance) = instantiate_inline(self.module) {
				Some(instance)
			} else {
				return None
			}
		};
		self.instance.as_ref()
	}
}

impl sp_core::traits::CallInWasm for WasmExecutor {
	fn call_in_wasm(
		&self,
		wasm_code: &[u8],
		code_hash: Option<Vec<u8>>,
		method: &str,
		call_data: &[u8],
		ext: &mut dyn Externalities,
		missing_host_functions: MissingHostFunctions,
	) -> std::result::Result<Vec<u8>, String> {
		let allow_missing_host_functions = missing_host_functions.allowed();

		if let Some(hash) = code_hash {
			let code = RuntimeCode {
				code_fetcher: &sp_core::traits::WrappedRuntimeCode(wasm_code.into()),
				hash,
				heap_pages: None,
			};

			self.with_instance(&code, ext, allow_missing_host_functions, |module, instance, _, mut ext| {
				with_externalities_safe(
					&mut **ext,
					move || {
						RuntimeInstanceSpawn::register_on_externalities(module.clone());
						instance.call_export(method, call_data)
					}
				)
			}).map_err(|e| e.to_string())
		} else {
			let module = crate::wasm_runtime::create_wasm_runtime_with_code(
				self.method,
				self.default_heap_pages,
				&wasm_code,
				self.host_functions.to_vec(),
				allow_missing_host_functions,
			)
				.map_err(|e| format!("Failed to create module: {:?}", e))?;

			let instance = module.new_instance()
				.map_err(|e| format!("Failed to create instance: {:?}", e))?;

			let instance = AssertUnwindSafe(instance);
			let mut ext = AssertUnwindSafe(ext);
			let module = AssertUnwindSafe(module);

			with_externalities_safe(
				&mut **ext,
				move || {
					RuntimeInstanceSpawn::register_on_externalities(module.clone());
					instance.call_export(method, call_data)
				}
			)
			.and_then(|r| r)
			.map_err(|e| e.to_string())
		}
	}
}

/// A generic `CodeExecutor` implementation that uses a delegate to determine wasm code equivalence
/// and dispatch to native code when possible, falling back on `WasmExecutor` when not.
pub struct NativeExecutor<D> {
	/// Dummy field to avoid the compiler complaining about us not using `D`.
	_dummy: std::marker::PhantomData<D>,
	/// Native runtime version info.
	native_version: NativeVersion,
	/// Fallback wasm executor.
	wasm: WasmExecutor,
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
	pub fn new(
		fallback_method: WasmExecutionMethod,
		default_heap_pages: Option<u64>,
		max_runtime_instances: usize,
	) -> Self {
		let mut host_functions = D::ExtendHostFunctions::host_functions();

		// Add the custom host functions provided by the user.
		host_functions.extend(sp_io::SubstrateHostFunctions::host_functions());
		let wasm_executor = WasmExecutor::new(
			fallback_method,
			default_heap_pages,
			host_functions,
			max_runtime_instances,
		);

		NativeExecutor {
			_dummy: Default::default(),
			native_version: D::native_version(),
			wasm: wasm_executor,
		}
	}
}

impl<D: NativeExecutionDispatch> RuntimeInfo for NativeExecutor<D> {
	fn native_version(&self) -> &NativeVersion {
		&self.native_version
	}

	fn runtime_version(
		&self,
		ext: &mut dyn Externalities,
		runtime_code: &RuntimeCode,
	) -> Result<RuntimeVersion> {
		self.wasm.with_instance(
			runtime_code,
			ext,
			false,
			|_module, _instance, version, _ext|
				Ok(version.cloned().ok_or_else(|| Error::ApiError("Unknown version".into()))),
		)
	}
}

/// Helper inner struct to implement `RuntimeSpawn` extension.
#[derive(Clone)]
pub struct RuntimeInstanceSpawn {
	module: Option<Arc<dyn WasmModule>>,
	instance: Arc<parking_lot::Mutex<Option<AssertUnwindSafe<Box<dyn WasmInstance>>>>>,
	tasks: Arc<parking_lot::Mutex<HashMap<u64, PendingTask>>>,
	infos: Arc<parking_lot::Mutex<RuntimeInstanceSpawnInfo>>,
	counter: Arc<AtomicU64>,
	scheduler: Box<dyn sp_core::traits::SpawnNamed>,
	task_receiver: Arc<parking_lot::Mutex<mpsc::Receiver<RemoteTask>>>,
	task_sender: mpsc::Sender<RemoteTask>,
	recursive_level: usize,
	dismiss_handles: dismiss_handle::DismissHandles,
}


#[cfg(all(feature = "abort-future", feature = "std"))]
mod dismiss_handle {
	use super::*;
	use std::collections::BTreeMap;

	#[derive(Default, Clone)]
	pub(super) struct DismissHandles(Arc<parking_lot::Mutex<DismissHandlesInner>>);

	struct DismissHandlesInner {
		/// threads handle with associated pthread.
		running: BTreeMap<u64, RemoteHandle>,
		/// worker mapping with their thread ids.
		workers: BTreeMap<u64, u64>,
	}

	impl Default for DismissHandlesInner {
		fn default() -> Self {
			DismissHandlesInner {
				running: BTreeMap::new(),
				workers: BTreeMap::new(),
			}
		}
	}

	impl DismissHandles {
		pub(super) fn new_thread_id(&self, counter: &Arc<AtomicU64>) -> u64 {
			counter.fetch_add(1, Ordering::Relaxed)
		}
		pub(super) fn register_new_thread(&self, handle: Option<RemoteHandle>, thread_id: u64) {
			if let Some(handle) = handle {
				self.0.lock().running.insert(thread_id, handle);
			}
		}
		pub(super) fn register_worker(&self, worker: u64, thread_id: u64) {
			self.0.lock().workers.insert(worker, thread_id);
		}
		pub(super) fn finished_worker(&self, worker: u64) {
			let mut lock = self.0.lock();
			if let Some(pthread_id) = lock.workers.remove(&worker) {
				lock.running.remove(&pthread_id);
			}
		}
		pub(super) fn dismiss_thread(&self, worker: u64) {
			let mut lock = self.0.lock();
			if let Some(handle_id) = lock.workers.remove(&worker) {
				if let Some(mut handle) = lock.running.remove(&handle_id) {
					handle.dismiss();
				}
			}
		}
	}
}

#[cfg(not(all(feature = "abort-future", feature = "std")))]
mod dismiss_handle {
	use super::*;

	#[derive(Default, Clone)]
	pub(super) struct DismissHandles;

	impl DismissHandles {
		pub(super) fn new_thread_id(&self, _counter: &Arc<AtomicU64>) -> u64 {
			0
		}
		pub(super) fn register_new_thread(&self, _handle: Option<RemoteHandle>, _thread_id: u64) {
		}
		pub(super) fn register_worker(&self, _worker: u64, _thread_id: u64) {
		}
		pub(super) fn finished_worker(&self, _worker: u64) {
		}
		pub(super) fn dismiss_thread(&self, _worker: u64) {
		}
	}
}

/// Task info for this instance.
/// Instance is local to a wasm call.
pub struct RuntimeInstanceSpawnInfo {
	// consider atomic instead (depending on usefullness
	// of this struct
	nb_runing: usize,
	capacity: usize,
}

enum PendingTask {
	Remote(mpsc::Receiver<Option<WorkerResult>>),
	Inline(InlineTask),
}

struct RemoteTask {
	handle: u64,
	task: Task,
	ext: AsyncExt,
	result_sender: mpsc::Sender<Option<WorkerResult>>,
}

impl RuntimeInstanceSpawnInfo {
	fn new(
		capacity: usize,
	) -> Self {
		RuntimeInstanceSpawnInfo {
			nb_runing: 0,
			capacity,
		}
	}
	
	fn start(&mut self, depth: usize) -> Processing {
		if self.nb_runing < self.capacity {
			self.nb_runing += 1;
			Processing::SpawnNew
		} else {
			if self.capacity > depth {
				Processing::Queue
			} else {
				Processing::RunInline
			}
		}
	}

	fn finished(&mut self) {
		self.nb_runing -= 1;
	}

	fn set_capacity(&mut self, capacity: u32) {
		let capacity: usize = capacity as usize;
		if capacity > self.capacity {
			self.capacity = capacity;
		}
	}
}

enum Processing {
	SpawnNew,
	RunInline,
	Queue,
}

impl RuntimeInstanceSpawn {
	fn nested_instance(&self) -> Self {
		RuntimeInstanceSpawn {
			// For inline recursive call would dead lock,
			// this instance is the one for inline, reinit here.
			instance: Arc::new(parking_lot::Mutex::new(None)),
			counter: Default::default(),
			tasks: Default::default(),
			recursive_level: self.recursive_level + 1,
			dismiss_handles: Default::default(),

			module: self.module.clone(),
			infos: self.infos.clone(),
			scheduler: self.scheduler.clone(),
			task_receiver: self.task_receiver.clone(),
			task_sender: self.task_sender.clone(),
		}
	}

	fn insert(
		&self,
		handle: u64,
		task: Task,
		ext: AsyncExt,
	) {
		let mut infos = self.infos.lock();
		match infos.start(self.recursive_level) {
			Processing::SpawnNew => {
				// warning self.tasks is locked when calling spawn_new
				if !self.spawn_new() {
					let task = InlineTask { task, ext };
					self.tasks.lock().insert(handle, PendingTask::Inline(task));
					return;
				}
			},
			Processing::Queue => (),
			Processing::RunInline => {
				let task = InlineTask { task, ext };
				self.tasks.lock().insert(handle, PendingTask::Inline(task));
				return;
			},
		}
		let (result_sender, result_receiver) = mpsc::channel();
		let task = RemoteTask { task, ext, result_sender, handle };
		self.task_sender.send(task).expect("Receiver is in scope");
		self.tasks.lock().insert(handle, PendingTask::Remote (
			result_receiver,
		));
	}

	// TODO should make a variant without module instantiation for native
	fn spawn_new(&self) -> bool {
		let module = self.module.clone();
		let scheduler = self.scheduler.clone();
		let task_receiver = self.task_receiver.clone();
		let infos = self.infos.clone();
		let runtime_spawn = Box::new(self.nested_instance());
		let module = AssertUnwindSafe(module);
		let dismiss_handles = self.dismiss_handles.clone();
		let thread_id = dismiss_handles.new_thread_id(&self.counter);
		let thread_handle = self.spawn_with_handle(
			"executor-extra-runtime-instance",
			Box::pin(async move {
			let task_receiver = task_receiver.clone();
			let mut instance: Option<AssertUnwindSafe<Box<dyn WasmInstance>>> = None;
			while let Ok(RemoteTask { handle, task, ext, result_sender }) = {
				let task_receiver_locked = task_receiver.lock();
				task_receiver_locked.recv()
			} {
				dismiss_handles.register_worker(handle, thread_id);
				let async_ext = || {
					let async_ext = match new_async_externalities(scheduler.clone(), ext) {
						Ok(val) => val,
						Err(e) => {
							log::error!(
								target: "executor",
								"Failed to setup externalities for async context: {}",
								e,
							);

							return None;
						}
					};
					let async_ext = match async_ext.with_runtime_spawn(runtime_spawn.clone()) {
						Ok(val) => val,
						Err(e) => {
							log::error!(
								target: "executor",
								"Failed to setup runtime extension for async externalities: {}",
								e,
							);

							return None;
						}
					};
					Some(async_ext)
				};

				let result = if let Some(async_ext) = async_ext() {
					let instance_ref = InlineInstantiateRef {
						module: &*module,
						instance: &mut instance,
					};

					sc_executor_common::inline_spawn::process_task::<(), _>(
						task,
						async_ext,
						handle,
						instance_ref,
					)
				} else {
					WorkerResult::HardPanic
				};

				let mut end = false;
				if let &WorkerResult::Panic = &result {
					log::error!("Panic error in spawned task, dropping instance");
					// Here we don't just shut all because panic will only transmit to parent
					// if 'join' is call, if 'dismiss' is call then it is fine to ignore a panic.
					instance = None; // will be lazilly re-instantiated
				}
				if let &WorkerResult::HardPanic = &result {
					end = true;
				}
				if let Err(_) = result_sender.send(Some(result)) {
					// Closed channel, remove this thread instance.
					end = true;
				}
				if end {
					dismiss_handles.finished_worker(handle);
					infos.lock().finished();
					return;
				}
			}
			log::error!("Sender dropped, closing all instance.");
			infos.lock().finished();
		}));
		if let Some(thread_handle) = thread_handle {
			self.dismiss_handles.register_new_thread(thread_handle, thread_id);
			true
		} else {
			false
		}
	}

	#[cfg(feature = "abort-future")]
	fn spawn_with_handle(
		&self,
		name: &'static str,
		future: BoxFuture,
	) -> Option<Option<RemoteHandle>> {
		self.scheduler.spawn_with_handle(name, future)
			.map(|th| Some(th))
	}

	#[cfg(not(feature = "abort-future"))]
	fn spawn_with_handle(
		&self,
		name: &'static str,
		future: BoxFuture,
	) -> Option<Option<RemoteHandle>> {
		self.scheduler.spawn(name, future);
		Some(None)
	}

}

impl RuntimeInstanceSpawn {
	fn spawn_call_inner(
		&self,
		task: Task,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		let handle = self.counter.fetch_add(1, Ordering::Relaxed);
		let ext = spawn_call_ext(handle, kind, calling_ext);

		self.insert(handle, task, ext);

		handle
	}
}

impl RuntimeSpawn for RuntimeInstanceSpawn {
	fn spawn_call_native(
		&self,
		func: fn(Vec<u8>) -> Vec<u8>,
		data: Vec<u8>,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		let task = Task::Native(NativeTask { func, data });
		self.spawn_call_inner(task, kind, calling_ext)
	}

	fn spawn_call(
		&self,
		dispatcher_ref: u32,
		func: u32,
		data: Vec<u8>,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		let task = Task::Wasm(WasmTask { dispatcher_ref, func, data });
		self.spawn_call_inner(task, kind, calling_ext)
	}

	fn join(&self, handle: u64, calling_ext: &mut dyn Externalities) -> Option<Vec<u8>> {
		let task = self.tasks.lock().remove(&handle);
		let worker_result = match task {
			Some(PendingTask::Remote(receiver)) => match receiver.recv() {
				Ok(Some(output)) => output,
				Ok(None)
				| Err(_) => {
					// spawned task did end with no result, so panic
					WorkerResult::Panic
				},
			},
			Some(PendingTask::Inline(task)) => {
				let mut instance = self.instance.lock();
				let instance_ref = InlineInstantiate {
					module: &self.module,
					guard: &mut instance,
				};

				let runtime_spawn = Box::new(self.nested_instance());
				sc_executor_common::inline_spawn::process_task_inline::<(), _>(
					task.task,
					task.ext,
					handle,
					runtime_spawn,
					instance_ref,
				)
			},
			// handle has been removed due to dismiss or
			// invalid externality condition.
			None => WorkerResult::Invalid,
		};

		calling_ext.resolve_worker_result(worker_result)
	}

	fn dismiss(&self, handle: u64) {
		self.dismiss_handles.dismiss_thread(handle);
		self.tasks.lock().remove(&handle);
	}

	fn set_capacity(&self, capacity: u32) {
		self.infos.lock().set_capacity(capacity);
	}
}

impl RuntimeInstanceSpawn {
	/// Instantiate a new `RuntimeInstanceSpawn`.
	/// 
	/// Usualy one should rather be using `register_on_externalities`.
	fn new(
		module: Option<Arc<dyn WasmModule>>,
		scheduler: Box<dyn sp_core::traits::SpawnNamed>,
		capacity: usize,
	) -> Self {
		let infos = RuntimeInstanceSpawnInfo::new(capacity);
		let (task_sender, task_receiver) = mpsc::channel();
		Self {
			module,
			scheduler,
			counter: Arc::new(0.into()),
			tasks: Arc::new(parking_lot::Mutex::new(Default::default())),
			infos: Arc::new(parking_lot::Mutex::new(infos)),
			task_receiver: Arc::new(parking_lot::Mutex::new(task_receiver)),
			task_sender,
			instance: Arc::new(parking_lot::Mutex::new(None)),
			recursive_level: 0,
			dismiss_handles: Default::default(),
		}
	}

	/// Allows to register an `RunstimeSpawn` without a
	/// wasm module.
	/// 
	/// In most case `register_on_externalities` should be use,
	/// this function is mostly for testing purpose (when
	/// it is guaranteed to run in native mode).
	pub fn with_externalities_and_module(
		module: Option<Arc<dyn WasmModule>>,
		mut ext: &mut dyn Externalities,
	) -> Option<Self> {
		// Using 0 as capacity is only if we got the sp::io host
		// function to change this capacity.
		ext.extension::<sp_core::traits::TaskExecutorExt>()
			.map(move |task_ext| Self::new(module, task_ext.clone(), 0))
	}

	/// Register new `RuntimeSpawnExt` on current externalities.
	///
	/// This extensions will spawn instances from provided `module`.
	pub fn register_on_externalities(module: Arc<dyn WasmModule>) {
		sp_externalities::with_externalities(
			move |mut ext| {
				if let Some(runtime_spawn) =
					Self::with_externalities_and_module(Some(module.clone()), ext)
				{
					if let Err(e) = ext.register_extension(
						RuntimeSpawnExt(Box::new(runtime_spawn))
					) {
						trace!(
							target: "executor",
							"Failed to register `RuntimeSpawnExt` instance on externalities: {:?}",
							e,
						)
					}
				}
			}
		);
	}
}

impl<D: NativeExecutionDispatch + 'static> CodeExecutor for NativeExecutor<D> {
	type Error = Error;

	fn call<
		R: Decode + Encode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
	>(
		&self,
		ext: &mut dyn Externalities,
		runtime_code: &RuntimeCode,
		method: &str,
		data: &[u8],
		use_native: bool,
		native_call: Option<NC>,
	) -> (Result<NativeOrEncoded<R>>, bool) {
		let mut used_native = false;
		let result = self.wasm.with_instance(
			runtime_code,
			ext,
			false,
			|module, instance, onchain_version, mut ext| {
				let onchain_version = onchain_version.ok_or_else(
					|| Error::ApiError("Unknown version".into())
				)?;

				let can_call_with = onchain_version.can_call_with(&self.native_version.runtime_version);

				match (
					use_native,
					can_call_with,
					native_call,
				) {
					(_, false, _) | (false, _, _) => {
						if !can_call_with {
							trace!(
								target: "executor",
								"Request for native execution failed (native: {}, chain: {})",
								self.native_version.runtime_version,
								onchain_version,
							);
						}

						with_externalities_safe(
							&mut **ext,
							move || {
								RuntimeInstanceSpawn::register_on_externalities(module.clone());
								instance.call_export(method, data).map(NativeOrEncoded::Encoded)
							}
						)
					},
					(true, true, Some(call)) => {
						trace!(
							target: "executor",
							"Request for native execution with native call succeeded \
							(native: {}, chain: {}).",
							self.native_version.runtime_version,
							onchain_version,
						);

						used_native = true;
						let res = with_externalities_safe(
							&mut **ext,
							move || {
								// Here module is in theory not use, but we still pass it because
								// it is just a reference counted.
								RuntimeInstanceSpawn::register_on_externalities(module.clone());
								(call)()
							}
						).and_then(|r| r
							.map(NativeOrEncoded::Native)
							.map_err(|s| Error::ApiError(s))
						);

						Ok(res)
					}
					_ => {
						trace!(
							target: "executor",
							"Request for native execution succeeded (native: {}, chain: {})",
							self.native_version.runtime_version,
							onchain_version
						);

						used_native = true;
						Ok(D::dispatch(&mut **ext, method, data).map(NativeOrEncoded::Encoded))
					}
				}
			}
		);
		(result, used_native)
	}
}

impl<D: NativeExecutionDispatch> Clone for NativeExecutor<D> {
	fn clone(&self) -> Self {
		NativeExecutor {
			_dummy: Default::default(),
			native_version: D::native_version(),
			wasm: self.wasm.clone(),
		}
	}
}

impl<D: NativeExecutionDispatch> sp_core::traits::CallInWasm for NativeExecutor<D> {
	fn call_in_wasm(
		&self,
		wasm_blob: &[u8],
		code_hash: Option<Vec<u8>>,
		method: &str,
		call_data: &[u8],
		ext: &mut dyn Externalities,
		missing_host_functions: MissingHostFunctions,
	) -> std::result::Result<Vec<u8>, String> {
		self.wasm.call_in_wasm(wasm_blob, code_hash, method, call_data, ext, missing_host_functions)
	}
}

/// Implements a `NativeExecutionDispatch` for provided parameters.
///
/// # Example
///
/// ```
/// sc_executor::native_executor_instance!(
///     pub MyExecutor,
///     substrate_test_runtime::api::dispatch,
///     substrate_test_runtime::native_version,
/// );
/// ```
///
/// # With custom host functions
///
/// When you want to use custom runtime interfaces from within your runtime, you need to make the
/// executor aware of the host functions for these interfaces.
///
/// ```
/// # use sp_runtime_interface::runtime_interface;
///
/// #[runtime_interface]
/// trait MyInterface {
///     fn say_hello_world(data: &str) {
///         println!("Hello world from: {}", data);
///     }
/// }
///
/// sc_executor::native_executor_instance!(
///     pub MyExecutor,
///     substrate_test_runtime::api::dispatch,
///     substrate_test_runtime::native_version,
///     my_interface::HostFunctions,
/// );
/// ```
///
/// When you have multiple interfaces, you can give the host functions as a tuple e.g.:
/// `(my_interface::HostFunctions, my_interface2::HostFunctions)`
///
#[macro_export]
macro_rules! native_executor_instance {
	( $pub:vis $name:ident, $dispatcher:path, $version:path $(,)?) => {
		/// A unit struct which implements `NativeExecutionDispatch` feeding in the
		/// hard-coded runtime.
		$pub struct $name;
		$crate::native_executor_instance!(IMPL $name, $dispatcher, $version, ());
	};
	( $pub:vis $name:ident, $dispatcher:path, $version:path, $custom_host_functions:ty $(,)?) => {
		/// A unit struct which implements `NativeExecutionDispatch` feeding in the
		/// hard-coded runtime.
		$pub struct $name;
		$crate::native_executor_instance!(
			IMPL $name, $dispatcher, $version, $custom_host_functions
		);
	};
	(IMPL $name:ident, $dispatcher:path, $version:path, $custom_host_functions:ty) => {
		impl $crate::NativeExecutionDispatch for $name {
			type ExtendHostFunctions = $custom_host_functions;

			fn dispatch(
				ext: &mut dyn $crate::Externalities,
				method: &str,
				data: &[u8]
			) -> $crate::error::Result<Vec<u8>> {
				$crate::with_externalities_safe(ext, move || $dispatcher(method, data))?
					.ok_or_else(|| $crate::error::Error::MethodNotFound(method.to_owned()))
			}

			fn native_version() -> $crate::NativeVersion {
				$version()
			}
		}
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

	native_executor_instance!(
		pub MyExecutor,
		substrate_test_runtime::api::dispatch,
		substrate_test_runtime::native_version,
		(my_interface::HostFunctions, my_interface::HostFunctions),
	);

	#[test]
	fn native_executor_registers_custom_interface() {
		let executor = NativeExecutor::<MyExecutor>::new(
			WasmExecutionMethod::Interpreted,
			None,
			8,
		);
		my_interface::HostFunctions::host_functions().iter().for_each(|function| {
			assert_eq!(
				executor.wasm.host_functions.iter().filter(|f| f == &function).count(),
				2,
			);
		});

		my_interface::say_hello_world("hey");
	}
}
