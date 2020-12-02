// This file is part of Substrate.

// Copyright (C) 2020-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Inline RuntimeSpawn implementation.
//!
//! This is a minimal implementation to support runtime workers.
//!
//! As a minimal implementation it can run in no_std (with alloc), but do not
//! actually spawn threads, all execution is done inline in the parent thread.

use crate::{new_inline_only_externalities, AsyncExt, AsyncStateType};
use sp_core::traits::RuntimeSpawn;
use sp_externalities::{WorkerResult, Externalities};
use sp_wasm_interface::wasm_runtime::{WasmInstance, WasmModule, Error, InvokeMethod};
use sp_std::rc::Rc;
use sp_std::cell::RefCell;
use sp_std::collections::btree_map::BTreeMap;
use sp_std::sync::Arc;
use sp_std::boxed::Box;
use sp_std::vec::Vec;
use sp_std::marker::PhantomData;
#[cfg(feature = "std")]
use parking_lot::Mutex;
#[cfg(feature = "std")]
use std::panic::{AssertUnwindSafe, UnwindSafe};
#[cfg(feature = "std")]
pub use log::error as log_error;
#[cfg(not(feature = "std"))]
use sp_state_machine::log_error;

/// Indicate if this run as a local
/// function without runtime boundaries.
/// If it does, it is safe to assume
/// that a wasm pointer can be call directly.
pub trait HostLocalFunction {
	const HOST_LOCAL: bool = false;
}

impl HostLocalFunction for () { }

struct HostLocal;
impl HostLocalFunction for HostLocal {
	const HOST_LOCAL: bool = true;
}

/// Helper inner struct to implement `RuntimeSpawn` extension.
pub struct RuntimeInstanceSpawn<RunningTask, HostLocalFunction = ()> {
	module: Option<Box<dyn WasmModule>>,
	#[cfg(feature = "std")]
	instance: Option<AssertUnwindSafe<Box<dyn WasmInstance>>>,
	#[cfg(not(feature = "std"))]
	instance: Option<Box<dyn WasmInstance>>,
	tasks: RuntimeInstanceSpawnInfo<RunningTask>,
	counter: u64,
	_ph: PhantomData<HostLocalFunction>,
}

/// Wasm module trait, this is usually define at a client level.
pub trait Module {
}

/// Set up the externalities and safe calling environment to execute runtime calls.
///
/// If the inner closure panics, it will be caught and return an error.
#[cfg(feature = "std")]
pub fn with_externalities_safe<F, U>(ext: &mut dyn Externalities, f: F) -> Result<U, Error>
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

/// Not std `with_externalities_safe` is only for use with environment
/// where no threads are use.
/// This will NOT catch panic.
///
/// This explains that any panic from a worker using thread have to panic
/// the parent thread on join (not if dismissed since inline processing
/// is lazy).
#[cfg(not(feature = "std"))]
pub fn with_externalities_safe<F, U>(ext: &mut dyn Externalities, f: F) -> Result<U, Error>
	where F: FnOnce() -> U
{
	Ok(sp_externalities::set_and_run_with_externalities(
		ext,
		f,
	))
}

/// Task info for this instance.
/// Instance is local to a wasm call.
pub struct RuntimeInstanceSpawnInfo<RunningTask> {
	// TODO rename Running Task, it is only pending
	tasks: BTreeMap<u64, RunningTask>,

	// TODO split struct (the two fields are unused).
	// consider atomic instead (depending on usefullness
	// of this struct
	nb_runing: usize,
	capacity: usize,
}

// TODO naming is bad (inline are not running)
pub struct RunningTask(PendingInlineTask);

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

struct PendingInlineTask {
	task: Task,
	ext: AsyncExt,
}

impl<RunningTask, HostLocal: HostLocalFunction> RuntimeInstanceSpawn<RunningTask, HostLocal> {
	// TODO
	pub fn new(module: Option<Box<dyn WasmModule>>) -> Self {
		RuntimeInstanceSpawn {
			module,
			instance: None,
			tasks: RuntimeInstanceSpawnInfo {
				tasks: BTreeMap::new(),
				nb_runing: 0,
				capacity: 0,
			},
			counter: 0,
			_ph: PhantomData,
		}
	}

	#[cfg(feature = "std")]
	fn instantiate_inline(
		module: &Option<Box<dyn WasmModule>>,
	) -> Option<AssertUnwindSafe<Box<dyn WasmInstance>>> {
		// TODO factor code with instantiate (FnOnce as param)
		Some(match module.as_ref().map(|m| m.new_instance()) {
			Some(Ok(val)) => AssertUnwindSafe(val),
			Some(Err(e)) => {
				log_error!(
					target: "executor",
					"Failed to create new instance for module for async context: {}",
					e,
				);
				return None;
			}
			None => {
				log_error!(target: "executor", "No module for a wasm task.");
				return None;
			},
		})
	}


	/// Obtain externality and get id for worker.
	pub fn spawn_call_ext(
		&mut self,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> (AsyncExt, u64) {
		let new_handle = self.counter;
		self.counter += 1;
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

	fn remove(&mut self, handle: u64) -> Option<RunningTask> {
		self.tasks.tasks.remove(&handle)
	}

	fn insert(
		&mut self,
		handle: u64,
		task: RunningTask,
	) {
		// TODO  could be in spawn_call_inner directly (see how we factor that with client executor
		self.tasks.tasks.insert(handle, task);
	}

	/// Base implementation for `RuntimeSpawn` method.
	pub fn dismiss(&mut self, handle: u64) {
		self.remove(handle);
	}
}

impl<HostLocal: HostLocalFunction> RuntimeInstanceSpawn<RunningTask, HostLocal> {
	fn spawn_call_inner(
		&mut self,
		task: Task,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		let (ext, handle) = self.spawn_call_ext(kind, calling_ext);

		self.insert(handle, RunningTask(PendingInlineTask {task, ext}));

		handle
	}

	/// Base implementation for `RuntimeSpawn` method.
	pub fn spawn_call_native(
		&mut self,
		func: fn(Vec<u8>) -> Vec<u8>,
		data: Vec<u8>,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		let task = Task::Native(NativeTask { func, data });
		self.spawn_call_inner(task, kind, calling_ext)
	}

	/// Base implementation for `RuntimeSpawn` method.
	pub fn spawn_call(
		&mut self,
		dispatcher_ref: u32,
		func: u32,
		data: Vec<u8>,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		let task = Task::Wasm(WasmTask { dispatcher_ref, func, data });
		self.spawn_call_inner(task, kind, calling_ext)
	}

	/// Base implementation for `RuntimeSpawn` method.
	pub fn join(&mut self, handle: u64, calling_ext: &mut dyn Externalities) -> Option<Vec<u8>> {
		let mut worker_result = || match self.remove(handle) {
			Some(RunningTask(
				PendingInlineTask { ext, task: Task::Wasm(WasmTask { dispatcher_ref, func, data }) },
			)) => {
				let need_resolve = ext.need_resolve();

				let mut async_ext = match new_inline_only_externalities(ext) {
					Ok(val) => val,
					Err(e) => {
						log_error!(
							target: "executor",
							"Failed to setup externalities for inline async context: {}",
							e,
						);
						return WorkerResult::HardPanic;
					}
				};

				#[cfg(feature = "std")]
				let result = if HostLocal::HOST_LOCAL {
					panic!("HOST_LOCAL is only expected for a wasm call");
				} else {
					// TODO put instanciation outside (need join over &self!! to reduce locks)
					// eg first prepare join returning the task and second run without lock
					let mut instance = &mut self.instance;
					if instance.is_none() {
						*instance = if let Some(instance) = Self::instantiate_inline(&self.module) {
							Some(instance)
						} else {
							return WorkerResult::HardPanic;
						};
					}

					let instance = instance.as_ref().expect("Lazy init at start");

					with_externalities_safe(
						&mut async_ext,
						|| instance.call(
							InvokeMethod::TableWithWrapper { dispatcher_ref, func },
							&data[..],
						)
					)
				};
				#[cfg(not(feature = "std"))]
				let result: Result<Result<_, ()>, _> = if HostLocal::HOST_LOCAL {
					let f: fn(Vec<u8>) -> Vec<u8> = unsafe { sp_std::mem::transmute(func) };
					with_externalities_safe(
						&mut async_ext,
						|| Ok(f(data)),
					)
				} else {
					panic!("No no_std wasm runner");
				};

				match result {
					// TODO if we knew tihs is stateless, we could return valid
					Ok(Ok(result)) => if need_resolve {
						WorkerResult::CallAt(result, handle)
					} else {
						WorkerResult::Valid(result)
					},
					Ok(Err(error)) => {
						log_error!("Wasm instance error in : {:?}", error);
						WorkerResult::HardPanic
					},
					Err(error) => {
						log_error!("Panic error in sinlined task: {:?}", error);
						WorkerResult::Panic
					}
				}
			},
			Some(RunningTask(
				PendingInlineTask { ext, task: Task::Native(NativeTask { func, data }) },
			)) => {
				// TODO factor code with wasm
				let need_resolve = ext.need_resolve();
				let mut async_ext = match new_inline_only_externalities(ext) {
					Ok(val) => val,
					Err(e) => {
						log_error!(
							target: "executor",
							"Failed to setup externalities for inline async context: {}",
							e,
						);
						return WorkerResult::HardPanic;
					}
				};
				match with_externalities_safe(
					&mut async_ext,
					|| func(data),
				) {
					// TODO Here if we got info about task being stateless, we could
					// directly return Valid
					Ok(result) => if need_resolve {
						WorkerResult::CallAt(result, handle)
					} else {
						WorkerResult::Valid(result)
					},
					Err(error) => {
						log_error!("Panic error in sinlined task: {:?}", error);
						WorkerResult::Panic
					}
				}
			},
			// handle has been removed due to dismiss or
			// invalid externality condition.
			None => WorkerResult::Invalid,
		};

		calling_ext.resolve_worker_result(worker_result())
	}

}

/// Inline instance spawn, to use with nodes that can manage threads.
#[cfg(feature = "std")]
pub struct RuntimeInstanceSpawnSend<RunningTask>(Arc<Mutex<RuntimeInstanceSpawn<RunningTask>>>);

#[cfg(feature = "std")]
impl RuntimeSpawn for RuntimeInstanceSpawnSend<RunningTask> {
	fn spawn_call_native(
		&self,
		func: fn(Vec<u8>) -> Vec<u8>,
		data: Vec<u8>,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		self.0.lock().spawn_call_native(func, data, kind, calling_ext)
	}

	fn spawn_call(
		&self,
		dispatcher_ref: u32,
		func: u32,
		data: Vec<u8>,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		self.0.lock().spawn_call(dispatcher_ref, func, data, kind, calling_ext)
	}

	fn join(&self, handle: u64, calling_ext: &mut dyn Externalities) -> Option<Vec<u8>> {
		self.0.lock().join(handle, calling_ext)
	}

	fn dismiss(&self, handle: u64) {
		self.0.lock().dismiss(handle)
	}

	fn set_capacity(&self, _capacity: u32) {
		// No capacity, only inline, skip useless lock.
	}
}


/// Inline instance spawn, to use with environment that do not use threads
/// and allows running an unsafe `Send` declaration.
pub struct RuntimeInstanceSpawnForceSend<RunningTask>(Rc<RefCell<RuntimeInstanceSpawn<RunningTask, HostLocal>>>);

unsafe impl Send for RuntimeInstanceSpawnForceSend<RunningTask> { }

impl RuntimeSpawn for RuntimeInstanceSpawnForceSend<RunningTask> {
	fn spawn_call_native(
		&self,
		func: fn(Vec<u8>) -> Vec<u8>,
		data: Vec<u8>,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		self.0.borrow_mut().spawn_call_native(func, data, kind, calling_ext)
	}

	fn spawn_call(
		&self,
		dispatcher_ref: u32,
		func: u32,
		data: Vec<u8>,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		self.0.borrow_mut().spawn_call(dispatcher_ref, func, data, kind, calling_ext)
	}

	fn join(&self, handle: u64, calling_ext: &mut dyn Externalities) -> Option<Vec<u8>> {
		self.0.borrow_mut().join(handle, calling_ext)
	}

	fn dismiss(&self, handle: u64) {
		self.0.borrow_mut().dismiss(handle)
	}

	fn set_capacity(&self, _capacity: u32) {
		// No capacity, only inline, skip useless lock.
	}
}

impl RuntimeInstanceSpawnForceSend<RunningTask> {
	// TODO
	pub fn new() -> Self {
		RuntimeInstanceSpawnForceSend(Rc::new(RefCell::new(RuntimeInstanceSpawn::new(None))))
	}
}

/// Alias to an inline implementation that can be use when runtime interface
/// is skipped.
pub type HostRuntimeInstanceSpawn = RuntimeInstanceSpawnForceSend<RunningTask>;
