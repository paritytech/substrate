// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! `RuntimeSpawn` implementation implementing
//! a pool or running worker for a given execution.

use std::{
	collections::HashMap,
	panic::{UnwindSafe, AssertUnwindSafe},
	sync::{Arc, atomic::{AtomicU64, Ordering}, mpsc},
};

use sp_core::{
	traits::{
		Externalities, AsyncExternalities,
		RuntimeSpawnExt, RuntimeSpawn, DismissHandle, BoxFuture, SpawnLimiter,
	},
};
use log::trace;
use sp_externalities::{ExternalitiesExt as _, WorkerResult};
use crate::{
	new_async_externalities, WorkerDeclaration,
	wasm_runtime::{WasmInstance, WasmModule}, error::Result,
	inline_spawn::{
		WasmTask, NativeTask, Task, PendingTask as InlineTask,
		InlineInstantiateRef, instantiate_inline,
	},
};

/// Set up the externalities and safe calling environment to execute runtime calls.
///
/// If the inner closure panics, it will be caught and return an error.
pub fn with_externalities_safe<F, U>(ext: &mut dyn Externalities, f: F) -> Result<U>
	where F: UnwindSafe + FnOnce() -> U
{
	Ok(crate::inline_spawn::with_externalities_safe(ext, f)?)
}

struct InlineInstantiate<'a, 'b> {
	module: &'a Option<Arc<dyn WasmModule>>,
	guard: &'a mut parking_lot::MutexGuard<'b, Option<AssertUnwindSafe<Box<dyn WasmInstance>>>>,
}

impl<'a, 'b> crate::inline_spawn::LazyInstanciate<'a> for InlineInstantiate<'a, 'b> {
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
		running: BTreeMap<u64, Option<DismissHandle>>,
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
			let thread_id = counter.fetch_add(1, Ordering::Relaxed);
			self.0.lock().running.insert(thread_id, None);
			thread_id
		}
		pub(super) fn register_new_thread(&self, handle: DismissHandle, thread_id: u64) {
			self.0.lock().running.insert(thread_id, Some(handle));
		}
		pub(super) fn drop_new_thread(&self, thread_id: u64) {
			self.0.lock().running.remove(&thread_id);
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
				if let Some(handle) = lock.running.remove(&handle_id) {
					handle.map(|mut handle| handle.dismiss());
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
		pub(super) fn register_new_thread(&self, _handle: DismissHandle, _thread_id: u64) {
		}
		pub(super) fn drop_new_thread(&self, _thread_id: u64) {
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
	limiter: Box<dyn sp_core::traits::SpawnNamed>,
}

enum PendingTask {
	Remote(mpsc::Receiver<Option<WorkerResult>>),
	Inline(InlineTask),
}

struct RemoteTask {
	handle: u64,
	task: Task,
	ext: Box<dyn AsyncExternalities>,
	result_sender: mpsc::Sender<Option<WorkerResult>>,
}

impl RuntimeInstanceSpawnInfo {
	fn new(
		capacity: usize,
		limiter: Box<dyn sp_core::traits::SpawnNamed>,
	) -> Self {
		RuntimeInstanceSpawnInfo {
			nb_runing: 0,
			capacity,
			limiter,
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
			let needed = capacity - self.capacity;
			let reserved = self.limiter.try_reserve(needed);
			self.capacity += reserved;
		}
	}
}

impl Drop for RuntimeInstanceSpawnInfo {
	fn drop(&mut self) {
		self.limiter.release(self.capacity);
		self.capacity = 0;
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
		ext: Box<dyn AsyncExternalities>,
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

	// Spawn a new worker loop listening on the task queue.
	fn spawn_new(&self) -> bool {
		let module = self.module.clone();
		let scheduler = self.scheduler.clone();
		let task_receiver = self.task_receiver.clone();
		let infos = self.infos.clone();
		let runtime_spawn = Box::new(self.nested_instance());
		let module = AssertUnwindSafe(module);
		let dismiss_handles = self.dismiss_handles.clone();
		let thread_id = dismiss_handles.new_thread_id(&self.counter);
		let thread_handle = self.spawn(
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

					crate::inline_spawn::process_task(
						task,
						async_ext,
						handle,
						instance_ref,
					)
				} else {
					WorkerResult::HardPanic
				};

				let mut end = false;
				if let &WorkerResult::RuntimePanic = &result {
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
			self.dismiss_handles.drop_new_thread(thread_id);
			false
		}
	}

	#[cfg(feature = "abort-future")]
	fn spawn(
		&self,
		name: &'static str,
		future: BoxFuture,
	) -> Option<DismissHandle> {
		self.scheduler.spawn(name, future)
	}

	#[cfg(not(feature = "abort-future"))]
	fn spawn(
		&self,
		name: &'static str,
		future: BoxFuture,
	) -> Option<DismissHandle> {
		self.scheduler.spawn(name, future);
		None
	}
}

impl RuntimeInstanceSpawn {
	fn spawn_call_inner(
		&self,
		task: Task,
		declaration: WorkerDeclaration,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		let handle = self.counter.fetch_add(1, Ordering::Relaxed);
		let ext = calling_ext.get_worker_externalities(handle, declaration);

		self.insert(handle, task, ext);

		handle
	}
}

impl RuntimeSpawn for RuntimeInstanceSpawn {
	fn spawn_call_native(
		&self,
		func: fn(Vec<u8>) -> Vec<u8>,
		data: Vec<u8>,
		declaration: WorkerDeclaration,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		let task = Task::Native(NativeTask { func, data });
		self.spawn_call_inner(task, declaration, calling_ext)
	}

	fn spawn_call(
		&self,
		dispatcher_ref: u32,
		func: u32,
		data: Vec<u8>,
		declaration: WorkerDeclaration,
		calling_ext: &mut dyn Externalities,
	) -> u64 {
		let task = Task::Wasm(WasmTask { dispatcher_ref, func, data });
		self.spawn_call_inner(task, declaration, calling_ext)
	}

	fn join(&self, handle: u64, calling_ext: &mut dyn Externalities) -> Option<Vec<u8>> {
		let task = self.tasks.lock().remove(&handle);
		let worker_result = match task {
			Some(PendingTask::Remote(receiver)) => match receiver.recv() {
				Ok(Some(output)) => output,
				Ok(None)
				| Err(_) => {
					// spawned task did end with no result, so panic
					WorkerResult::RuntimePanic
				},
			},
			Some(PendingTask::Inline(task)) => {
				let mut instance = self.instance.lock();
				let instance_ref = InlineInstantiate {
					module: &self.module,
					guard: &mut instance,
				};

				let runtime_spawn = Box::new(self.nested_instance());
				crate::inline_spawn::process_task_inline(
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

	fn dismiss(&self, handle: u64, calling_ext: &mut dyn Externalities) {
		calling_ext.dismiss_worker(handle);
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
	pub fn new(
		module: Option<Arc<dyn WasmModule>>,
		scheduler: Box<dyn sp_core::traits::SpawnNamed>,
		capacity: usize,
	) -> Self {
		let infos = RuntimeInstanceSpawnInfo::new(capacity, scheduler.clone());
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
