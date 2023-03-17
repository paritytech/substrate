// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Substrate service tasks management module.

use crate::{config::TaskType, Error};
use exit_future::Signal;
use futures::{
	future::{pending, select, try_join_all, BoxFuture, Either},
	Future, FutureExt, StreamExt,
};
use parking_lot::Mutex;
use prometheus_endpoint::{
	exponential_buckets, register, CounterVec, HistogramOpts, HistogramVec, Opts, PrometheusError,
	Registry, U64,
};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use std::{
	collections::{hash_map::Entry, HashMap},
	panic,
	pin::Pin,
	result::Result,
	sync::Arc,
};
use tokio::runtime::Handle;
use tracing_futures::Instrument;

mod prometheus_future;
#[cfg(test)]
mod tests;

/// Default task group name.
pub const DEFAULT_GROUP_NAME: &str = "default";

/// The name of a group a task belongs to.
///
/// This name is passed belong-side the task name to the prometheus metrics and can be used
/// to group tasks.
pub enum GroupName {
	/// Sets the group name to `default`.
	Default,
	/// Use the specifically given name as group name.
	Specific(&'static str),
}

impl From<Option<&'static str>> for GroupName {
	fn from(name: Option<&'static str>) -> Self {
		match name {
			Some(name) => Self::Specific(name),
			None => Self::Default,
		}
	}
}

impl From<&'static str> for GroupName {
	fn from(name: &'static str) -> Self {
		Self::Specific(name)
	}
}

/// An handle for spawning tasks in the service.
#[derive(Clone)]
pub struct SpawnTaskHandle {
	on_exit: exit_future::Exit,
	tokio_handle: Handle,
	metrics: Option<Metrics>,
	task_registry: TaskRegistry,
}

impl SpawnTaskHandle {
	/// Spawns the given task with the given name and a group name.
	/// If group is not specified `DEFAULT_GROUP_NAME` will be used.
	///
	/// Note that the `name` is a `&'static str`. The reason for this choice is that
	/// statistics about this task are getting reported to the Prometheus endpoint (if enabled), and
	/// that therefore the set of possible task names must be bounded.
	///
	/// In other words, it would be a bad idea for someone to do for example
	/// `spawn(format!("{:?}", some_public_key))`.
	pub fn spawn(
		&self,
		name: &'static str,
		group: impl Into<GroupName>,
		task: impl Future<Output = ()> + Send + 'static,
	) {
		self.spawn_inner(name, group, task, TaskType::Async)
	}

	/// Spawns the blocking task with the given name. See also `spawn`.
	pub fn spawn_blocking(
		&self,
		name: &'static str,
		group: impl Into<GroupName>,
		task: impl Future<Output = ()> + Send + 'static,
	) {
		self.spawn_inner(name, group, task, TaskType::Blocking)
	}

	/// Helper function that implements the spawning logic. See `spawn` and `spawn_blocking`.
	fn spawn_inner(
		&self,
		name: &'static str,
		group: impl Into<GroupName>,
		task: impl Future<Output = ()> + Send + 'static,
		task_type: TaskType,
	) {
		let on_exit = self.on_exit.clone();
		let metrics = self.metrics.clone();
		let registry = self.task_registry.clone();

		let group = match group.into() {
			GroupName::Specific(var) => var,
			// If no group is specified use default.
			GroupName::Default => DEFAULT_GROUP_NAME,
		};

		let task_type_label = match task_type {
			TaskType::Blocking => "blocking",
			TaskType::Async => "async",
		};

		// Note that we increase the started counter here and not within the future. This way,
		// we could properly visualize on Prometheus situations where the spawning doesn't work.
		if let Some(metrics) = &self.metrics {
			metrics.tasks_spawned.with_label_values(&[name, group, task_type_label]).inc();
			// We do a dummy increase in order for the task to show up in metrics.
			metrics
				.tasks_ended
				.with_label_values(&[name, "finished", group, task_type_label])
				.inc_by(0);
		}

		let future = async move {
			// Register the task and keep the "token" alive until the task is ended. Then this
			// "token" will unregister this task.
			let _registry_token = registry.register_task(name, group);

			if let Some(metrics) = metrics {
				// Add some wrappers around `task`.
				let task = {
					let poll_duration =
						metrics.poll_duration.with_label_values(&[name, group, task_type_label]);
					let poll_start =
						metrics.poll_start.with_label_values(&[name, group, task_type_label]);
					let inner =
						prometheus_future::with_poll_durations(poll_duration, poll_start, task);
					// The logic of `AssertUnwindSafe` here is ok considering that we throw
					// away the `Future` after it has panicked.
					panic::AssertUnwindSafe(inner).catch_unwind()
				};
				futures::pin_mut!(task);

				match select(on_exit, task).await {
					Either::Right((Err(payload), _)) => {
						metrics
							.tasks_ended
							.with_label_values(&[name, "panic", group, task_type_label])
							.inc();
						panic::resume_unwind(payload)
					},
					Either::Right((Ok(()), _)) => {
						metrics
							.tasks_ended
							.with_label_values(&[name, "finished", group, task_type_label])
							.inc();
					},
					Either::Left(((), _)) => {
						// The `on_exit` has triggered.
						metrics
							.tasks_ended
							.with_label_values(&[name, "interrupted", group, task_type_label])
							.inc();
					},
				}
			} else {
				futures::pin_mut!(task);
				let _ = select(on_exit, task).await;
			}
		}
		.in_current_span();

		match task_type {
			TaskType::Async => {
				self.tokio_handle.spawn(future);
			},
			TaskType::Blocking => {
				let handle = self.tokio_handle.clone();
				self.tokio_handle.spawn_blocking(move || {
					handle.block_on(future);
				});
			},
		}
	}
}

impl sp_core::traits::SpawnNamed for SpawnTaskHandle {
	fn spawn_blocking(
		&self,
		name: &'static str,
		group: Option<&'static str>,
		future: BoxFuture<'static, ()>,
	) {
		self.spawn_inner(name, group, future, TaskType::Blocking)
	}

	fn spawn(
		&self,
		name: &'static str,
		group: Option<&'static str>,
		future: BoxFuture<'static, ()>,
	) {
		self.spawn_inner(name, group, future, TaskType::Async)
	}
}

/// A wrapper over `SpawnTaskHandle` that will notify a receiver whenever any
/// task spawned through it fails. The service should be on the receiver side
/// and will shut itself down whenever it receives any message, i.e. an
/// essential task has failed.
#[derive(Clone)]
pub struct SpawnEssentialTaskHandle {
	essential_failed_tx: TracingUnboundedSender<()>,
	inner: SpawnTaskHandle,
}

impl SpawnEssentialTaskHandle {
	/// Creates a new `SpawnEssentialTaskHandle`.
	pub fn new(
		essential_failed_tx: TracingUnboundedSender<()>,
		spawn_task_handle: SpawnTaskHandle,
	) -> SpawnEssentialTaskHandle {
		SpawnEssentialTaskHandle { essential_failed_tx, inner: spawn_task_handle }
	}

	/// Spawns the given task with the given name.
	///
	/// See also [`SpawnTaskHandle::spawn`].
	pub fn spawn(
		&self,
		name: &'static str,
		group: impl Into<GroupName>,
		task: impl Future<Output = ()> + Send + 'static,
	) {
		self.spawn_inner(name, group, task, TaskType::Async)
	}

	/// Spawns the blocking task with the given name.
	///
	/// See also [`SpawnTaskHandle::spawn_blocking`].
	pub fn spawn_blocking(
		&self,
		name: &'static str,
		group: impl Into<GroupName>,
		task: impl Future<Output = ()> + Send + 'static,
	) {
		self.spawn_inner(name, group, task, TaskType::Blocking)
	}

	fn spawn_inner(
		&self,
		name: &'static str,
		group: impl Into<GroupName>,
		task: impl Future<Output = ()> + Send + 'static,
		task_type: TaskType,
	) {
		let essential_failed = self.essential_failed_tx.clone();
		let essential_task = std::panic::AssertUnwindSafe(task).catch_unwind().map(move |_| {
			log::error!("Essential task `{}` failed. Shutting down service.", name);
			let _ = essential_failed.close_channel();
		});

		let _ = self.inner.spawn_inner(name, group, essential_task, task_type);
	}
}

impl sp_core::traits::SpawnEssentialNamed for SpawnEssentialTaskHandle {
	fn spawn_essential_blocking(
		&self,
		name: &'static str,
		group: Option<&'static str>,
		future: BoxFuture<'static, ()>,
	) {
		self.spawn_blocking(name, group, future);
	}

	fn spawn_essential(
		&self,
		name: &'static str,
		group: Option<&'static str>,
		future: BoxFuture<'static, ()>,
	) {
		self.spawn(name, group, future);
	}
}

/// Helper struct to manage background/async tasks in Service.
pub struct TaskManager {
	/// A future that resolves when the service has exited, this is useful to
	/// make sure any internally spawned futures stop when the service does.
	on_exit: exit_future::Exit,
	/// A signal that makes the exit future above resolve, fired on drop.
	_signal: Signal,
	/// Tokio runtime handle that is used to spawn futures.
	tokio_handle: Handle,
	/// Prometheus metric where to report the polling times.
	metrics: Option<Metrics>,
	/// Send a signal when a spawned essential task has concluded. The next time
	/// the service future is polled it should complete with an error.
	essential_failed_tx: TracingUnboundedSender<()>,
	/// A receiver for spawned essential-tasks concluding.
	essential_failed_rx: TracingUnboundedReceiver<()>,
	/// Things to keep alive until the task manager is dropped.
	keep_alive: Box<dyn std::any::Any + Send>,
	/// A list of other `TaskManager`'s to terminate and gracefully shutdown when the parent
	/// terminates and gracefully shutdown. Also ends the parent `future()` if a child's essential
	/// task fails.
	children: Vec<TaskManager>,
	/// The registry of all running tasks.
	task_registry: TaskRegistry,
}

impl TaskManager {
	/// If a Prometheus registry is passed, it will be used to report statistics about the
	/// service tasks.
	pub fn new(
		tokio_handle: Handle,
		prometheus_registry: Option<&Registry>,
	) -> Result<Self, PrometheusError> {
		let (signal, on_exit) = exit_future::signal();

		// A side-channel for essential tasks to communicate shutdown.
		let (essential_failed_tx, essential_failed_rx) =
			tracing_unbounded("mpsc_essential_tasks", 100);

		let metrics = prometheus_registry.map(Metrics::register).transpose()?;

		Ok(Self {
			on_exit,
			_signal: signal,
			tokio_handle,
			metrics,
			essential_failed_tx,
			essential_failed_rx,
			keep_alive: Box::new(()),
			children: Vec::new(),
			task_registry: Default::default(),
		})
	}

	/// Get a handle for spawning tasks.
	pub fn spawn_handle(&self) -> SpawnTaskHandle {
		SpawnTaskHandle {
			on_exit: self.on_exit.clone(),
			tokio_handle: self.tokio_handle.clone(),
			metrics: self.metrics.clone(),
			task_registry: self.task_registry.clone(),
		}
	}

	/// Get a handle for spawning essential tasks.
	pub fn spawn_essential_handle(&self) -> SpawnEssentialTaskHandle {
		SpawnEssentialTaskHandle::new(self.essential_failed_tx.clone(), self.spawn_handle())
	}

	/// Return a future that will end with success if the signal to terminate was sent
	/// (`self.terminate()`) or with an error if an essential task fails.
	///
	/// # Warning
	///
	/// This function will not wait until the end of the remaining task.
	pub fn future<'a>(
		&'a mut self,
	) -> Pin<Box<dyn Future<Output = Result<(), Error>> + Send + 'a>> {
		Box::pin(async move {
			let mut t1 = self.essential_failed_rx.next().fuse();
			let mut t2 = self.on_exit.clone().fuse();
			let mut t3 = try_join_all(
				self.children
					.iter_mut()
					.map(|x| x.future())
					// Never end this future if there is no error because if there is no children,
					// it must not stop
					.chain(std::iter::once(pending().boxed())),
			)
			.fuse();

			futures::select! {
				_ = t1 => Err(Error::Other("Essential task failed.".into())),
				_ = t2 => Ok(()),
				res = t3 => Err(res.map(|_| ()).expect_err("this future never ends; qed")),
			}
		})
	}

	/// Set what the task manager should keep alive, can be called multiple times.
	pub fn keep_alive<T: 'static + Send>(&mut self, to_keep_alive: T) {
		// allows this fn to safely called multiple times.
		use std::mem;
		let old = mem::replace(&mut self.keep_alive, Box::new(()));
		self.keep_alive = Box::new((to_keep_alive, old));
	}

	/// Register another TaskManager to terminate and gracefully shutdown when the parent
	/// terminates and gracefully shutdown. Also ends the parent `future()` if a child's essential
	/// task fails. (But don't end the parent if a child's normal task fails.)
	pub fn add_child(&mut self, child: TaskManager) {
		self.children.push(child);
	}

	/// Consume `self` and return the [`TaskRegistry`].
	///
	/// This [`TaskRegistry`] can be used to check for still running tasks after this task manager
	/// was dropped.
	pub fn into_task_registry(self) -> TaskRegistry {
		self.task_registry
	}
}

#[derive(Clone)]
struct Metrics {
	// This list is ordered alphabetically
	poll_duration: HistogramVec,
	poll_start: CounterVec<U64>,
	tasks_spawned: CounterVec<U64>,
	tasks_ended: CounterVec<U64>,
}

impl Metrics {
	fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			poll_duration: register(HistogramVec::new(
				HistogramOpts {
					common_opts: Opts::new(
						"substrate_tasks_polling_duration",
						"Duration in seconds of each invocation of Future::poll"
					),
					buckets: exponential_buckets(0.001, 4.0, 9)
						.expect("function parameters are constant and always valid; qed"),
				},
				&["task_name", "task_group", "kind"]
			)?, registry)?,
			poll_start: register(CounterVec::new(
				Opts::new(
					"substrate_tasks_polling_started_total",
					"Total number of times we started invoking Future::poll"
				),
				&["task_name", "task_group", "kind"]
			)?, registry)?,
			tasks_spawned: register(CounterVec::new(
				Opts::new(
					"substrate_tasks_spawned_total",
					"Total number of tasks that have been spawned on the Service"
				),
				&["task_name", "task_group", "kind"]
			)?, registry)?,
			tasks_ended: register(CounterVec::new(
				Opts::new(
					"substrate_tasks_ended_total",
					"Total number of tasks for which Future::poll has returned Ready(()) or panicked"
				),
				&["task_name", "reason", "task_group", "kind"]
			)?, registry)?,
		})
	}
}

/// Ensures that a [`Task`] is unregistered when this object is dropped.
struct UnregisterOnDrop {
	task: Task,
	registry: TaskRegistry,
}

impl Drop for UnregisterOnDrop {
	fn drop(&mut self) {
		let mut tasks = self.registry.tasks.lock();

		if let Entry::Occupied(mut entry) = (*tasks).entry(self.task.clone()) {
			*entry.get_mut() -= 1;

			if *entry.get() == 0 {
				entry.remove();
			}
		}
	}
}

/// Represents a running async task in the [`TaskManager`].
///
/// As a task is identified by a name and a group, it is totally valid that there exists multiple
/// tasks with the same name and group.
#[derive(Clone, Hash, Eq, PartialEq)]
pub struct Task {
	/// The name of the task.
	pub name: &'static str,
	/// The group this task is associated to.
	pub group: &'static str,
}

impl Task {
	/// Returns if the `group` is the [`DEFAULT_GROUP_NAME`].
	pub fn is_default_group(&self) -> bool {
		self.group == DEFAULT_GROUP_NAME
	}
}

/// Keeps track of all running [`Task`]s in [`TaskManager`].
#[derive(Clone, Default)]
pub struct TaskRegistry {
	tasks: Arc<Mutex<HashMap<Task, usize>>>,
}

impl TaskRegistry {
	/// Register a task with the given `name` and `group`.
	///
	/// Returns [`UnregisterOnDrop`] that ensures that the task is unregistered when this value is
	/// dropped.
	fn register_task(&self, name: &'static str, group: &'static str) -> UnregisterOnDrop {
		let task = Task { name, group };

		{
			let mut tasks = self.tasks.lock();

			*(*tasks).entry(task.clone()).or_default() += 1;
		}

		UnregisterOnDrop { task, registry: self.clone() }
	}

	/// Returns the running tasks.
	///
	/// As a task is only identified by its `name` and `group`, there can be duplicate tasks. The
	/// number per task represents the concurrently running tasks with the same identifier.
	pub fn running_tasks(&self) -> HashMap<Task, usize> {
		(*self.tasks.lock()).clone()
	}
}
