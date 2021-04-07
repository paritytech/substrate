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

use crate::new_inline_only_externalities;
use sp_core::traits::RuntimeSpawn;
use sp_externalities::{WorkerResult, Externalities, AsyncExternalities, TaskId};
use sp_std::rc::Rc;
use sp_std::cell::RefCell;
use sp_std::collections::btree_map::BTreeMap;
use sp_std::boxed::Box;
use sp_std::vec::Vec;
#[cfg(feature = "std")]
pub use log::error as log_error;
#[cfg(feature = "std")]
use crate::common::{
	LazyInstanciate, InlineInstantiateRef,
};
use crate::common::{
	WasmTask, NativeTask, Task, PendingTask,
	HostLocalFunction,
};

/// Helper inner struct to implement `RuntimeSpawn` extension.
///
/// It manages a `TaskId` current counter and keep trace
/// of task pending for those ids.
pub struct RuntimeInstanceSpawn {
	tasks: BTreeMap<TaskId, PendingTask>,
	counter: TaskId,
}

/// Run a given task inline.
pub fn process_task_inline<
	'a,
	#[cfg(feature = "std")]
	I: LazyInstanciate<'a> + 'a,
>(
	task: Task,
	ext: Box<dyn AsyncExternalities>,
	runtime_ext: Box<dyn RuntimeSpawn>,
	#[cfg(feature = "std")]
	instance_ref: I,
) -> WorkerResult {
	#[cfg(feature = "std")] {
		process_task_inline_inner::<(), I>(
			task,
			ext,
			runtime_ext,
			instance_ref,
		)
	}
	#[cfg(not(feature = "std"))] {
		process_task_inline_inner::<()>(
			task,
			ext,
			runtime_ext,
		)
	}
}

/// Run a given task inline.
fn process_task_inline_inner<
	'a,
	HostLocal: HostLocalFunction,
	#[cfg(feature = "std")]
	I: LazyInstanciate<'a> + 'a,
>(
	task: Task,
	ext: Box<dyn AsyncExternalities>,
	runtime_ext: Box<dyn RuntimeSpawn>,
	#[cfg(feature = "std")]
	instance_ref: I,
) -> WorkerResult {

	let async_ext = match new_inline_only_externalities(ext) {
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
	let async_ext = match async_ext.with_runtime_spawn(runtime_ext) {
		Ok(val) => val,
		Err(e) => {
			log_error!(
				target: "executor",
				"Failed to setup runtime extension for async externalities: {}",
				e,
			);
			return WorkerResult::HardPanic;
		}
	};

	#[cfg(feature = "std")]
	{
		crate::common::process_task_inner::<HostLocal, _>(task, async_ext, instance_ref)
	}
	#[cfg(not(feature = "std"))]
	{
		crate::common::process_task_inner::<HostLocal>(task, async_ext)
	}
}

impl RuntimeInstanceSpawn {
	fn nested_instance(&self) -> Self {
		RuntimeInstanceSpawn {
			tasks: Default::default(),
			counter: 0,
		}
	}
}

impl RuntimeInstanceSpawn {
	/// Instantiate an inline instance spawn without
	/// a wasm module.
	/// This can be use if we are sure native only will
	/// be use or if we are not using sp_io calls.
	pub fn new() -> Self {
		RuntimeInstanceSpawn {
			tasks: BTreeMap::new(),
			counter: 0,
		}
	}

	/// Base implementation for `RuntimeSpawn` method.
	pub fn dismiss(&mut self, handle: TaskId) {
		self.tasks.remove(&handle);
	}
}

impl RuntimeInstanceSpawn {
	fn spawn_call_inner(
		&mut self,
		task: Task,
		calling_ext: &mut dyn Externalities,
	) -> TaskId {
		let handle = self.counter;
		self.counter += 1;
		let ext = calling_ext.get_worker_externalities(handle);

		self.tasks.insert(handle, PendingTask {task, ext});

		handle
	}

	/// Base implementation for `RuntimeSpawn` method.
	pub fn spawn_call_native(
		&mut self,
		func: fn(Vec<u8>) -> Vec<u8>,
		data: Vec<u8>,
		calling_ext: &mut dyn Externalities,
	) -> TaskId {
		let task = Task::Native(NativeTask { func, data });
		self.spawn_call_inner(task, calling_ext)
	}

	/// Base implementation for `RuntimeSpawn` method.
	pub fn spawn_call(
		&mut self,
		dispatcher_ref: u32,
		func: u32,
		data: Vec<u8>,
		calling_ext: &mut dyn Externalities,
	) -> TaskId {
		let task = Task::Wasm(WasmTask { dispatcher_ref, func, data });
		self.spawn_call_inner(task, calling_ext)
	}
}

/// Variant to use when the calls do not use the runtime interface.
/// For instance doing a proof verification in wasm.
pub mod hosted_runtime {
	use super::*;
	use sp_core::traits::RuntimeSpawnExt;

	/// Inline instance spawn, this run all workers lazily when `join` is called.
	///
	///
	/// This should only be use with hosted runtime.
	///
	/// Warning to use only with environment that do not use threads (mainly wasm)
	/// and thus allows the unsafe `Send` declaration.
	pub struct RuntimeInstanceHostLocal(
		Rc<RefCell<RuntimeInstanceSpawn>>,
	);

	unsafe impl Send for RuntimeInstanceHostLocal { }

	impl RuntimeInstanceHostLocal {
		fn nested_instance(&self) -> Self {
			RuntimeInstanceHostLocal(
				Rc::new(RefCell::new(self.0.borrow().nested_instance())),
			)
		}
	}

	impl RuntimeSpawn for RuntimeInstanceHostLocal {
		fn spawn_call_native(
			&self,
			func: fn(Vec<u8>) -> Vec<u8>,
			data: Vec<u8>,
			calling_ext: &mut dyn Externalities,
		) -> TaskId {
			self.0.borrow_mut().spawn_call_native(func, data, calling_ext)
		}

		fn spawn_call(
			&self,
			dispatcher_ref: u32,
			func: u32,
			data: Vec<u8>,
			calling_ext: &mut dyn Externalities,
		) -> TaskId {
			self.0.borrow_mut().spawn_call(dispatcher_ref, func, data, calling_ext)
		}

		fn join(&self, handle: TaskId, calling_ext: &mut dyn Externalities) -> Option<Vec<u8>> {
			let nested = Box::new(self.nested_instance());
			let worker_result = match self.0.borrow_mut().tasks.remove(&handle) {
				Some(task) => {
					// hosted in std does not make sense, but we can
					// be use in native mode without wasm.
					#[cfg(feature = "std")]
					{
						let mut instance = None;
						let module = None;
						let instance_ref = InlineInstantiateRef {
							instance: &mut instance,
							module: &module,
						};

						process_task_inline_inner::<HostLocal, _>(
							task.task,
							task.ext,
							nested,
							instance_ref,
						)
					}
					#[cfg(not(feature = "std"))]
					process_task_inline_inner::<HostLocal>(task.task, task.ext, nested)
				},
				// handle has been removed due to dismiss or
				// invalid externality condition.
				None => WorkerResult::Invalid,
			};

			calling_ext.resolve_worker_result(worker_result)
		}

		fn dismiss(&self, handle: TaskId, calling_ext: &mut dyn Externalities) {
			calling_ext.dismiss_worker(handle);
			self.0.borrow_mut().dismiss(handle)
		}

		fn set_capacity(&self, _capacity: u32) {
			// No capacity, only inline, skip useless lock.
		}
	}

	impl RuntimeInstanceHostLocal {
		/// Instantial a new inline `RuntimeSpawn`.
		///
		/// Warning this is implementing `Send` when it should not and
		/// should never be use in environment supporting threads.
		pub fn new() -> Self {
			RuntimeInstanceHostLocal(
				Rc::new(RefCell::new(RuntimeInstanceSpawn::new())),
			)
		}
	}

	/// Alias to an inline implementation that can be use when runtime interface
	/// is skipped.
	pub type HostRuntimeInstanceSpawn = RuntimeInstanceHostLocal;

	/// Hosted runtime variant of sp_io `RuntimeTasks` `set_capacity`.
	///
	/// Warning this is actually a noops, if at some point there is
	/// hosted threads, it will need the boilerpalte code to call
	/// current externality.
	pub fn host_runtime_tasks_set_capacity(_capacity: u32) {
		// Ignore (this implementation only run inline, so no
		// need to call extension).
	}

	/// Hosted runtime variant of sp_io `RuntimeTasks` `spawn`.
	pub fn host_runtime_tasks_spawn(
		dispatcher_ref: u32,
		entry: u32,
		payload: Vec<u8>,
	) -> TaskId {
		sp_externalities::with_externalities_and_extension::<RuntimeSpawnExt, _, _>(|ext, runtime_spawn| {
			runtime_spawn.spawn_call(dispatcher_ref, entry, payload, ext)
		}).unwrap()
	}

	/// Hosted runtime variant of sp_io `RuntimeTasks` `spawn`.
	pub fn host_runtime_tasks_join(handle: TaskId) -> Option<Vec<u8>> {
		sp_externalities::with_externalities_and_extension::<RuntimeSpawnExt, _, _>(|ext, runtime_spawn| {
			runtime_spawn.join(handle, ext)
		}).unwrap()
	}

	/// Hosted runtime variant of sp_io `RuntimeTasks` `spawn`.
	pub fn host_runtime_tasks_dismiss(handle: TaskId) {
		sp_externalities::with_externalities_and_extension::<RuntimeSpawnExt, _, _>(|ext, runtime_spawn| {
			runtime_spawn.dismiss(handle, ext)
		}).unwrap()
	}
}

/// `HostLocalFunction` implementation that
/// indicate we are using hosted runtime.
#[derive(Clone, Copy)]
struct HostLocal;

impl HostLocalFunction for HostLocal {
	const HOST_LOCAL: bool = true;
}
