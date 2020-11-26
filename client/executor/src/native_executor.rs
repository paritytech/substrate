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
		RuntimeSpawnExt, RuntimeSpawn,
	},
};
use log::trace;
use sp_wasm_interface::{HostFunctions, Function};
use sc_executor_common::wasm_runtime::{WasmInstance, WasmModule, InvokeMethod};
use sp_externalities::{ExternalitiesExt as _, AsyncBackend};
use sp_tasks::{new_async_externalities, AsyncExt, AsyncStateType};

/// Default num of pages for the heap
const DEFAULT_HEAP_PAGES: u64 = 1024;

/// Set up the externalities and safe calling environment to execute runtime calls.
///
/// If the inner closure panics, it will be caught and return an error.
pub fn with_externalities_safe<F, U>(ext: &mut dyn Externalities, f: F) -> Result<U>
	where F: UnwindSafe + FnOnce() -> U
{
	// TODO here externalities is used as environmental and inherently is
	// making the `AssertUnwindSafe` assertion, that is not true.
	// Worst case is probably locked mutex, so not that harmfull.
	// The thread scenario adds a bit over it but there was already
	// locked backend.
	sp_externalities::set_and_run_with_externalities(
		ext,
		move || {
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
		},
	)
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
/// TODO consider Arc outside of the spawn: to many here
#[derive(Clone)]
pub struct RuntimeInstanceSpawn {
	module: Option<Arc<dyn WasmModule>>,
	instance: Arc<parking_lot::Mutex<Option<Box<dyn WasmInstance>>>>,
	tasks: Arc<parking_lot::Mutex<RuntimeInstanceSpawnInfo>>,
	counter: Arc<AtomicU64>,
	scheduler: Box<dyn sp_core::traits::SpawnNamed>,
	task_receiver: Arc<parking_lot::Mutex<mpsc::Receiver<PendingTask>>>,
	task_sender: mpsc::Sender<PendingTask>,
	recursive_level: usize,
}

/// Task info for this instance.
/// Instance is local to a wasm call.
pub struct RuntimeInstanceSpawnInfo {
	tasks: HashMap<u64, RuningTask>,
	// consider atomic instead (depending on usefullness
	// of this struct
	nb_runing: usize,
	capacity: usize,
}

// TODO naming is bad (inline are not runing)
enum RuningTask {
	// TODO condvar?
	Task(mpsc::Receiver<Option<Vec<u8>>>),
	// TODO need to ad context of exteranlity init
	Inline(Task),
}

struct WasmTask {
	dispatcher_ref: u32,
	data: Vec<u8>,
	func: u32,
}

struct NativeTask {
	data: Vec<u8>,
	func: fn(Vec<u8>) -> Vec<u8>,
}

enum Task {
	Native(NativeTask),
	Wasm(WasmTask),
}

struct PendingTask {
	task: Task,
	ext: AsyncExt,
	result_sender: mpsc::Sender<Option<Vec<u8>>>,
}

impl RuntimeInstanceSpawnInfo {
	fn new(
		capacity: usize,
	) -> Self {
		RuntimeInstanceSpawnInfo {
			tasks: HashMap::new(),
			nb_runing: 0,
			capacity,
		}
	}
	
	fn start(&mut self, depth: usize) -> Processing {
		if self.nb_runing < self.capacity {
			self.nb_runing += 1;
			Processing::SpawnNew
		} else {
			// Note that this does not prevent
			// from deadlocking in case there
			// is multiple recursive call in paralell.
			// TODO also consider model where recursive
			// call must be declare first hand (depth replaced
			// by recursive declared) or it run inline.
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
	fn rec_clone(&self) -> Self {
		let mut result = self.clone();
		result.recursive_level += 1;
		result
	}

	fn remove(&self, handle: u64) -> RuningTask {
		self.tasks.lock().tasks.remove(&handle)
			.expect("Existing handle use for join")
	}

	fn insert(
		&self,
		handle: u64,
		task: PendingTask,
		result_receiver: mpsc::Receiver<Option<Vec<u8>>>,
	) {
		let mut tasks = self.tasks.lock();
		match tasks.start(self.recursive_level) {
			Processing::SpawnNew => {
				// warning self.tasks is locked when calling spawn_new
				self.spawn_new();
			},
			Processing::Queue => (),
			Processing::RunInline => {
				// TODO in this case a useless channel was opened.
				tasks.tasks.insert(handle, RuningTask::Inline(task.task));
				return;
			},
		}
		tasks.tasks.insert(handle, RuningTask::Task (
			result_receiver,
		));
		self.task_sender.send(task).expect("TODO mgmt");
	}

	fn instantiate(
		module: &Option<Arc<dyn WasmModule>>,
		tasks: &Arc<parking_lot::Mutex<RuntimeInstanceSpawnInfo>>,
	) -> Option<AssertUnwindSafe<Box<dyn WasmInstance>>> {
		Some(match module.as_ref().map(|m| m.new_instance()) {
			Some(Ok(val)) => AssertUnwindSafe(val),
			Some(Err(e)) => {
				log::error!(
					target: "executor",
					"Failed to create new instance for module for async context: {}",
					e,
				);

				tasks.lock().finished();
				return None;
			}
			None => {
				log::error!(target: "executor", "No module for a wasm task.");
				tasks.lock().finished();
				return None;
			},
		})
	}

	// TODO should make a variant without module instantiation for native
	fn spawn_new(&self) {
		let module = self.module.clone();
		let scheduler = self.scheduler.clone();
		let task_receiver = self.task_receiver.clone();
		let tasks = self.tasks.clone();
		let runtime_spawn = Box::new(self.rec_clone());
		let module = AssertUnwindSafe(module);
		self.scheduler.spawn("executor-extra-runtime-instance", Box::pin(async move {
			let task_receiver = task_receiver.clone();
			while let PendingTask { task, ext, result_sender } = { 
				let task_receiver_locked = task_receiver.lock();
				task_receiver_locked.recv()
			}.expect("Sender dropped, closing all instance.") {
				let async_ext = match new_async_externalities(scheduler.clone(), ext) {
					Ok(val) => val,
					Err(e) => {
						log::error!(
							target: "executor",
							"Failed to setup externalities for async context: {}",
							e,
						);

						// TODO send back message and count (to run non asynch at some point).
						// tasks.lock().finished();
						continue;
					}
				};
				let mut async_ext = match async_ext.with_runtime_spawn(runtime_spawn.clone()) {
					Ok(val) => val,
					Err(e) => {
						log::error!(
							target: "executor",
							"Failed to setup runtime extension for async externalities: {}",
							e,
						);

						// TODO send back message and count (to run non asynch at some point).
						// tasks.lock().finished();
						continue;
					}
				};
				match task {
					Task::Wasm(WasmTask { dispatcher_ref, func, data }) => {
						let mut instance = if let Some(instance) = Self::instantiate(&*module, &tasks) {
							instance
						} else {
							return;
						};

						match with_externalities_safe(
							&mut async_ext,
							|| instance.call(
								InvokeMethod::TableWithWrapper { dispatcher_ref, func },
								&data[..],
							)
						) {
							Ok(result) => {
								if let Err(_) = result_sender.send(match result {
									Ok(output) => Some(output),
									Err(error) => {
										log::error!("Call error in spawned task: {:?}", error);
										None
									},
								}) {
									// Closed channel, remove this thread instance.
									tasks.lock().finished();
									return;
								}
							},
							Err(error) => {
								log::error!("Panic error in spawned task: {:?}", error);
								instance = if let Some(instance) = Self::instantiate(&*module, &tasks) {
									instance
								} else {
									return;
								};
							}
						}
					},
					Task::Native(NativeTask { func, data }) => {
						// We do not instantiate, this assume we never run both Wasm and
						// native for a single instance spawn.
						match with_externalities_safe(
							&mut async_ext,
							|| func(data)
						) {
							Ok(result) => {
								if let Err(_) = result_sender.send(Some(result)) {
									// Closed channel, remove this thread instance.
									tasks.lock().finished();
									return;
								}
							},
							Err(error) => {
								log::error!("Panic error in spawned task: {:?}", error);
							}
						}
					},
				}
			}

			tasks.lock().finished();
		}));
	}
}

impl RuntimeInstanceSpawn {
	fn spawn_call_ext(
		&self,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> (AsyncExt, u64) {
		let new_handle = self.counter.fetch_add(1, Ordering::Relaxed);
		(match AsyncStateType::from_u8(kind)
			// TODO better message
			.expect("Only from existing kind") {
			AsyncStateType::Stateless => {
				AsyncExt::stateless_ext()
			},
			AsyncStateType::ReadLastBlock => {
				let backend = calling_ext.get_past_async_backend()
					.expect("Unsupported spawn kind.");
				AsyncExt::previous_block_read(backend)
			},
			AsyncStateType::ReadAtSpawn => {
				let backend = calling_ext.get_async_backend(new_handle)
					.expect("Unsupported spawn kind.");
				AsyncExt::state_at_spawn_read(backend, new_handle)
			},
		}, new_handle)
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
		let (ext, new_handle) = self.spawn_call_ext(kind, calling_ext);

		let (result_sender, result_receiver) = mpsc::channel();
		let task = PendingTask { task: Task::Native(NativeTask { func, data }), ext, result_sender};
		self.insert(new_handle, task, result_receiver);

		new_handle
/*		let scheduler = sp_externalities::with_externalities(|mut ext| ext.extension::<TaskExecutorExt>()
			.expect("No task executor associated with the current context!")
			.clone()
		).expect("Spawn called outside of externalities context!");

		let backend = match kind {
			AsyncStateType::Stateless => AsyncExt::stateless_ext(),
			AsyncStateType::ReadLastBlock => {
				let backend = sp_externalities::with_externalities(|mut ext|
					ext.get_past_async_backend()
						.expect("Unsupported spawn kind.")
				).expect("Spawn called outside of externalities context!");

				AsyncExt::previous_block_read(backend)
			},
			AsyncStateType::ReadAtSpawn => {
				let spawn_id = unimplemented!("TODO need handle on state machine and generally a thread pool like for wasm");
				let backend = sp_externalities::with_externalities(|mut ext|
					ext.get_async_backend(spawn_id)
						.expect("Unsupported spawn kind.")
				).expect("Spawn called outside of externalities context!");
				AsyncExt::state_at_spawn_read(backend, Default::default(), spawn_id)
			},
		};

		let (sender, receiver) = mpsc::channel();
		let extra_scheduler = scheduler.clone();
		scheduler.spawn("parallel-runtime-spawn", Box::pin(async move {
			let result = match crate::new_async_externalities(extra_scheduler, backend) {
				Ok(mut ext) => {
					let mut ext = AssertUnwindSafe(&mut ext);
					match std::panic::catch_unwind(move || {
						sp_externalities::set_and_run_with_externalities(
							&mut **ext,
							move || entry_point(data),
						)
					}) {
						Ok(result) => result,
						Err(panic) => {
							log::error!(
								target: "runtime",
								"Spawned task panicked: {:?}",
								panic,
							);

							// This will drop sender without sending anything.
							return;
						}
					}
				},
				Err(e) => {
					log::error!(
						target: "runtime",
						"Unable to run async task: {}",
						e,
					);

					return;
				},
			};

			let _ = sender.send(result);
		}));

		DataJoinHandle { receiver }
*/
	}

	fn spawn_call(
		&self,
		dispatcher_ref: u32,
		func: u32,
		data: Vec<u8>,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		let (ext, new_handle) = self.spawn_call_ext(kind, calling_ext);

		let (result_sender, result_receiver) = mpsc::channel();
		let task = PendingTask { task: Task::Wasm(WasmTask { dispatcher_ref, func, data }), ext, result_sender};
		self.insert(new_handle, task, result_receiver);

		new_handle
	}

	fn join(&self, handle: u64) -> Vec<u8> {
		match self.remove(handle) {
			RuningTask::Task(receiver) => {
				if let Some(output) = receiver.recv()
					.expect("Spawned task panicked for the handle") {
					output
				} else {
					panic!("Spawned task panicked for the handle");
				}
			},
			RuningTask::Inline(Task::Wasm(WasmTask { dispatcher_ref, func, data })) => {
				let mut instance = self.instance.lock();
				if instance.is_none() {
					*instance = self.module.as_ref().map(|m| m.new_instance()
						.expect("Failed to create new instance from module"));
				}
				// TODO this require inline async ext the reproduce the limited
				// externality context of AsyncExt and also a panic handler.
				// Not srue about panic handler since currently even if panic
				// is handled we panic on result receiver.
				// -> so no panic handler I guess.
				let result = instance.as_ref().expect("lazy init above").call(
					InvokeMethod::TableWithWrapper { dispatcher_ref, func },
					&data[..],
				);
				match result {
					Ok(output) => output,
					Err(error) => {
						log::error!("Call error in spawned task: {:?}", error);
						panic!("Spawned task panicked for the handle");
					},
				}
			},
			RuningTask::Inline(Task::Native(NativeTask { func, data })) => {
				// Same TODO for ext (actually without we double ext borrow_mut).
				func(data)
			},
		}
	}

	fn kill(&self, handle: u64) {
		unimplemented!()
	}

	fn set_capacity(&self, capacity: u32) {
		self.tasks.lock().set_capacity(capacity);
	}
}

impl RuntimeInstanceSpawn {
	pub fn new(
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
			tasks: Arc::new(parking_lot::Mutex::new(infos)),
			task_receiver: Arc::new(parking_lot::Mutex::new(task_receiver)),
			task_sender,
			instance: Arc::new(parking_lot::Mutex::new(None)),
			recursive_level: 0,
		}
	}

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
						let res = with_externalities_safe(&mut **ext, move || (call)())
							.and_then(|r| r
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
