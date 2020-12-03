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

use sp_tasks::{new_inline_only_externalities, AsyncExt, AsyncStateType};
use sp_core::traits::RuntimeSpawn;
use sp_externalities::{WorkerResult, Externalities};
use sp_std::rc::Rc;
use sp_std::cell::RefCell;
use sp_std::collections::btree_map::BTreeMap;
use sp_std::sync::Arc;
use sp_std::boxed::Box;
use sp_std::vec::Vec;
use sp_std::marker::PhantomData;
#[cfg(feature = "std")]
use crate::wasm_runtime::{WasmInstance, WasmModule, InvokeMethod};
#[cfg(feature = "std")]
use crate::error::Error;
#[cfg(feature = "std")]
use parking_lot::Mutex;
#[cfg(feature = "std")]
use std::panic::{AssertUnwindSafe, UnwindSafe};
#[cfg(feature = "std")]
pub use log::error as log_error;

/// In no_std we skip log, this macro
/// is a noops.
#[cfg(not(feature = "std"))]
macro_rules! log_error {
	(target: $target:expr, $($arg:tt)+) => (
		()
	);
	($($arg:tt)+) => (
		()
	);
}

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
/// TODO maybe RunningTask param is useless
pub struct RuntimeInstanceSpawn<RunningTask, HostLocalFunction = ()> {
	#[cfg(feature = "std")]
	module: Option<Box<dyn WasmModule>>,
	#[cfg(feature = "std")]
	instance: Option<AssertUnwindSafe<Box<dyn WasmInstance>>>,
	tasks: BTreeMap<u64, RunningTask>,
	counter: u64,
	_ph: PhantomData<HostLocalFunction>,
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
fn with_externalities_safe<F, U>(ext: &mut dyn Externalities, f: F) -> Result<U, ()>
	where F: FnOnce() -> U
{
	Ok(sp_externalities::set_and_run_with_externalities(
		ext,
		f,
	))
}

/// TODO
pub struct WasmTask {
	pub dispatcher_ref: u32,
	pub data: Vec<u8>,
	pub func: u32,
}

/// TODO
pub struct NativeTask {
	pub data: Vec<u8>,
	pub func: fn(Vec<u8>) -> Vec<u8>,
}

/// TODO
pub enum Task {
	Native(NativeTask),
	Wasm(WasmTask),
}

/// TODO
pub struct PendingInlineTask {
	pub task: Task,
	pub ext: AsyncExt,
}

#[cfg(feature = "std")]
/// TODO
pub fn instantiate(
	module: Option<&dyn WasmModule>,
) -> Option<AssertUnwindSafe<Box<dyn WasmInstance>>> {
	Some(match module.map(|m| m.new_instance()) {
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
	handle: u64,
	kind: u8,
	calling_ext: &mut dyn Externalities,
) -> AsyncExt {
	match AsyncStateType::from_u8(kind)
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
			let backend = calling_ext.get_async_backend(handle)
				.expect("Unsupported spawn kind.");
			AsyncExt::state_at_spawn_read(backend, handle)
		},
	}
}

/// Technical trait to factor code.
/// It access the instance lazilly from a module.
#[cfg(feature = "std")]
pub trait LazyInstanciate<'a> {
	fn instantiate(self) -> Option<&'a AssertUnwindSafe<Box<dyn WasmInstance>>>;
}

#[cfg(feature = "std")]
struct InlineInstantiate<'a> {
	module: &'a Option<Box<dyn WasmModule>>,
	instance: &'a mut Option<AssertUnwindSafe<Box<dyn WasmInstance>>>,
}

#[cfg(feature = "std")]
impl<'a> LazyInstanciate<'a> for InlineInstantiate<'a> {
	fn instantiate(self) -> Option<&'a AssertUnwindSafe<Box<dyn WasmInstance>>> {
		if self.instance.is_none() {
			*self.instance = if let Some(instance) = instantiate(self.module.as_ref().map(AsRef::as_ref)) {
				Some(instance)
			} else {
				return None
			}
		};
		self.instance.as_ref()
	}
}

pub fn join_inline<
	'a,
	HostLocal: HostLocalFunction,
	#[cfg(feature = "std")]
	I: LazyInstanciate<'a> + 'a,
>(
	task: PendingInlineTask,
	handle: u64,
	calling_ext: &mut dyn Externalities,
	#[cfg(feature = "std")]
	mut instance_ref: I,
) -> WorkerResult {
	match task {
		PendingInlineTask {
			ext,
			task: Task::Wasm(WasmTask { dispatcher_ref, func, data }),
		} => {
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
				let instance = if let Some(instance) = instance_ref.instantiate() {
					instance
				} else {
					return WorkerResult::HardPanic;
				};
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
		PendingInlineTask {
			ext,
			task: Task::Native(NativeTask { func, data }),
		} => {
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
	}
}



impl<RunningTask, HostLocal: HostLocalFunction> RuntimeInstanceSpawn<RunningTask, HostLocal> {
	// TODO
	#[cfg(feature = "std")]
	pub fn with_module(module: Box<dyn WasmModule>) -> Self {
		let mut result = Self::new();
		result.module = Some(module);
		result
	}

	/// TODO
	pub fn new() -> Self {
		RuntimeInstanceSpawn {
			#[cfg(feature = "std")]
			module: None,
			#[cfg(feature = "std")]
			instance: None,
			tasks: BTreeMap::new(),
			counter: 0,
			_ph: PhantomData,
		}
	}

	fn remove(&mut self, handle: u64) -> Option<RunningTask> {
		self.tasks.remove(&handle)
	}

	/// Base implementation for `RuntimeSpawn` method.
	pub fn dismiss(&mut self, handle: u64) {
		self.remove(handle);
	}
}

impl<HostLocal: HostLocalFunction> RuntimeInstanceSpawn<PendingInlineTask, HostLocal> {
	fn spawn_call_inner(
		&mut self,
		task: Task,
		kind: u8,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		let handle = self.counter;
		self.counter += 1;
		let ext = spawn_call_ext(handle, kind, calling_ext);

		self.tasks.insert(handle, PendingInlineTask {task, ext});

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
		let worker_result = match self.remove(handle) {
			Some(task) => {
				#[cfg(feature = "std")]
				{
					let instance_ref = InlineInstantiate {
						module: &self.module,
						instance: &mut self.instance,
					};
					join_inline::<HostLocal, _>(task, handle, calling_ext, instance_ref)
				}
				#[cfg(not(feature = "std"))]
				join_inline::<HostLocal>(task, handle, calling_ext)
			},
			// handle has been removed due to dismiss or
			// invalid externality condition.
			None => WorkerResult::Invalid,
		};

		calling_ext.resolve_worker_result(worker_result)
	}

}

/// Inline instance spawn, to use with nodes that can manage threads.
#[cfg(feature = "std")]
pub struct RuntimeInstanceSpawnSend<RunningTask>(Arc<Mutex<RuntimeInstanceSpawn<RunningTask>>>);

#[cfg(feature = "std")]
impl RuntimeSpawn for RuntimeInstanceSpawnSend<PendingInlineTask> {
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

unsafe impl Send for RuntimeInstanceSpawnForceSend<PendingInlineTask> { }

impl RuntimeSpawn for RuntimeInstanceSpawnForceSend<PendingInlineTask> {
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

impl RuntimeInstanceSpawnForceSend<PendingInlineTask> {
	// TODO
	pub fn new() -> Self {
		RuntimeInstanceSpawnForceSend(Rc::new(RefCell::new(RuntimeInstanceSpawn::new())))
	}
}

/// Alias to an inline implementation that can be use when runtime interface
/// is skipped.
pub type HostRuntimeInstanceSpawn = RuntimeInstanceSpawnForceSend<PendingInlineTask>;
