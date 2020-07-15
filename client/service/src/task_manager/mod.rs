// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

//! Substrate service tasks management module.

use std::{panic, result::Result, pin::Pin};
use exit_future::Signal;
use log::{debug, error};
use futures::{
	Future, FutureExt, StreamExt,
	future::{select, Either, BoxFuture},
	compat::*,
	task::{Spawn, FutureObj, SpawnError},
	sink::SinkExt,
};
use prometheus_endpoint::{
	exponential_buckets, register,
	PrometheusError,
	CounterVec, HistogramOpts, HistogramVec, Opts, Registry, U64
};
use sc_client_api::CloneableSpawn;
use sp_utils::mpsc::{TracingUnboundedSender, TracingUnboundedReceiver, tracing_unbounded};
use crate::{config::{TaskExecutor, TaskType, JoinFuture}, Error};

mod prometheus_future;
#[cfg(test)]
mod tests;

/// An handle for spawning tasks in the service.
#[derive(Clone)]
pub struct SpawnTaskHandle {
	on_exit: exit_future::Exit,
	executor: TaskExecutor,
	metrics: Option<Metrics>,
	task_notifier: TracingUnboundedSender<JoinFuture>,
}

impl SpawnTaskHandle {
	/// Spawns the given task with the given name.
	///
	/// Note that the `name` is a `&'static str`. The reason for this choice is that statistics
	/// about this task are getting reported to the Prometheus endpoint (if enabled), and that
	/// therefore the set of possible task names must be bounded.
	///
	/// In other words, it would be a bad idea for someone to do for example
	/// `spawn(format!("{:?}", some_public_key))`.
	pub fn spawn(&self, name: &'static str, task: impl Future<Output = ()> + Send + 'static) {
		self.spawn_inner(name, task, TaskType::Async)
	}

	/// Spawns the blocking task with the given name. See also `spawn`.
	pub fn spawn_blocking(&self, name: &'static str, task: impl Future<Output = ()> + Send + 'static) {
		self.spawn_inner(name, task, TaskType::Blocking)
	}

	/// Helper function that implements the spawning logic. See `spawn` and `spawn_blocking`.
	fn spawn_inner(
		&self,
		name: &'static str,
		task: impl Future<Output = ()> + Send + 'static,
		task_type: TaskType,
	) {
		if self.task_notifier.is_closed() {
			debug!("Attempt to spawn a new task has been prevented: {}", name);
			return;
		}

		let on_exit = self.on_exit.clone();
		let metrics = self.metrics.clone();

		// Note that we increase the started counter here and not within the future. This way,
		// we could properly visualize on Prometheus situations where the spawning doesn't work.
		if let Some(metrics) = &self.metrics {
			metrics.tasks_spawned.with_label_values(&[name]).inc();
			// We do a dummy increase in order for the task to show up in metrics.
			metrics.tasks_ended.with_label_values(&[name, "finished"]).inc_by(0);
		}

		let future = async move {
			if let Some(metrics) = metrics {
				// Add some wrappers around `task`.
				let task = {
					let poll_duration = metrics.poll_duration.with_label_values(&[name]);
					let poll_start = metrics.poll_start.with_label_values(&[name]);
					let inner = prometheus_future::with_poll_durations(poll_duration, poll_start, task);
					// The logic of `AssertUnwindSafe` here is ok considering that we throw
					// away the `Future` after it has panicked.
					panic::AssertUnwindSafe(inner).catch_unwind()
				};
				futures::pin_mut!(task);

				match select(on_exit, task).await {
					Either::Right((Err(payload), _)) => {
						metrics.tasks_ended.with_label_values(&[name, "panic"]).inc();
						panic::resume_unwind(payload)
					}
					Either::Right((Ok(()), _)) => {
						metrics.tasks_ended.with_label_values(&[name, "finished"]).inc();
					}
					Either::Left(((), _)) => {
						// The `on_exit` has triggered.
						metrics.tasks_ended.with_label_values(&[name, "interrupted"]).inc();
					}
				}

			} else {
				futures::pin_mut!(task);
				let _ = select(on_exit, task).await;
			}
		};

		let join_handle = self.executor.spawn(Box::pin(future), task_type);
		let mut task_notifier = self.task_notifier.clone();
		self.executor.spawn(
			Box::pin(async move {
				if let Err(err) = task_notifier.send(join_handle).await {
					error!("Could not send spawned task handle to queue: {}", err);
				}
			}),
			TaskType::Async,
		);
	}
}

impl Spawn for SpawnTaskHandle {
	fn spawn_obj(&self, future: FutureObj<'static, ()>)
	-> Result<(), SpawnError> {
		self.spawn("unnamed", future);
		Ok(())
	}
}

impl sp_core::traits::SpawnNamed for SpawnTaskHandle {
	fn spawn_blocking(&self, name: &'static str, future: BoxFuture<'static, ()>) {
		self.spawn_blocking(name, future);
	}

	fn spawn(&self, name: &'static str, future: BoxFuture<'static, ()>) {
		self.spawn(name, future);
	}
}

impl sc_client_api::CloneableSpawn for SpawnTaskHandle {
	fn clone(&self) -> Box<dyn CloneableSpawn> {
		Box::new(Clone::clone(self))
	}
}

type Boxed01Future01 = Box<dyn futures01::Future<Item = (), Error = ()> + Send + 'static>;

impl futures01::future::Executor<Boxed01Future01> for SpawnTaskHandle {
	fn execute(&self, future: Boxed01Future01) -> Result<(), futures01::future::ExecuteError<Boxed01Future01>>{
		self.spawn("unnamed", future.compat().map(drop));
		Ok(())
	}
}

/// A wrapper over `SpawnTaskHandle` that will notify a receiver whenever any
/// task spawned through it fails. The service should be on the receiver side
/// and will shut itself down whenever it receives any message, i.e. an
/// essential task has failed.
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
		SpawnEssentialTaskHandle {
			essential_failed_tx,
			inner: spawn_task_handle,
		}
	}

	/// Spawns the given task with the given name.
	///
	/// See also [`SpawnTaskHandle::spawn`].
	pub fn spawn(&self, name: &'static str, task: impl Future<Output = ()> + Send + 'static) {
		self.spawn_inner(name, task, TaskType::Async)
	}

	/// Spawns the blocking task with the given name.
	///
	/// See also [`SpawnTaskHandle::spawn_blocking`].
	pub fn spawn_blocking(
		&self,
		name: &'static str,
		task: impl Future<Output = ()> + Send + 'static,
	) {
		self.spawn_inner(name, task, TaskType::Blocking)
	}

	fn spawn_inner(
		&self,
		name: &'static str,
		task: impl Future<Output = ()> + Send + 'static,
		task_type: TaskType,
	) {
		let essential_failed = self.essential_failed_tx.clone();
		let essential_task = std::panic::AssertUnwindSafe(task)
			.catch_unwind()
			.map(move |_| {
				log::error!("Essential task `{}` failed. Shutting down service.", name);
				let _ = essential_failed.close_channel();
			});

		let _ = self.inner.spawn_inner(name, essential_task, task_type);
	}
}

/// Helper struct to manage background/async tasks in Service.
pub struct TaskManager {
	/// A future that resolves when the service has exited, this is useful to
	/// make sure any internally spawned futures stop when the service does.
	on_exit: exit_future::Exit,
	/// A signal that makes the exit future above resolve, fired on service drop.
	signal: Option<Signal>,
	/// How to spawn background tasks.
	executor: TaskExecutor,
	/// Prometheus metric where to report the polling times.
	metrics: Option<Metrics>,
	/// Send a signal when a spawned essential task has concluded. The next time
	/// the service future is polled it should complete with an error.
	essential_failed_tx: TracingUnboundedSender<()>,
	/// A receiver for spawned essential-tasks concluding.
	essential_failed_rx: TracingUnboundedReceiver<()>,
	/// Things to keep alive until the task manager is dropped.
	keep_alive: Box<dyn std::any::Any + Send + Sync>,
	task_notifier: TracingUnboundedSender<JoinFuture>,
	completion_future: JoinFuture,
}

impl TaskManager {
 	/// If a Prometheus registry is passed, it will be used to report statistics about the
 	/// service tasks.
	pub(super) fn new(
		executor: TaskExecutor,
		prometheus_registry: Option<&Registry>
	) -> Result<Self, PrometheusError> {
		let (signal, on_exit) = exit_future::signal();

		// A side-channel for essential tasks to communicate shutdown.
		let (essential_failed_tx, essential_failed_rx) = tracing_unbounded("mpsc_essential_tasks");

		let metrics = prometheus_registry.map(Metrics::register).transpose()?;

		let (task_notifier, background_tasks) = tracing_unbounded("mpsc_background_tasks");
		// NOTE: for_each_concurrent will await on all the JoinHandle futures at the same time. It
		// is possible to limit this but it's actually better for the memory foot print to await
		// them all to not accumulate anything on that stream.
		let completion_future = executor.spawn(
			Box::pin(background_tasks.for_each_concurrent(None, |x| x)),
			TaskType::Async,
		);

		Ok(Self {
			on_exit,
			signal: Some(signal),
			executor,
			metrics,
			essential_failed_tx,
			essential_failed_rx,
			keep_alive: Box::new(()),
			task_notifier,
			completion_future,
		})
	}

	/// Get a handle for spawning tasks.
	pub fn spawn_handle(&self) -> SpawnTaskHandle {
		SpawnTaskHandle {
			on_exit: self.on_exit.clone(),
			executor: self.executor.clone(),
			metrics: self.metrics.clone(),
			task_notifier: self.task_notifier.clone(),
		}
	}

	/// Get a handle for spawning essential tasks.
	pub fn spawn_essential_handle(&self) -> SpawnEssentialTaskHandle {
		SpawnEssentialTaskHandle::new(self.essential_failed_tx.clone(), self.spawn_handle())
	}

	/// Send the signal for termination, prevent new tasks to be created, await for all the existing
	/// tasks to be finished and drop the object. You can consider this as an async drop.
	pub fn clean_shutdown(mut self) -> Pin<Box<dyn Future<Output = ()> + Send>> {
		self.terminate();
		let keep_alive = self.keep_alive;
		let completion_future = self.completion_future;

		Box::pin(async move {
			completion_future.await;
			drop(keep_alive);
		})
	}

	/// Return a future that will end with success if the signal to terminate was sent
	/// (`self.terminate()`) or with an error if an essential task fails.
	///
	/// # Warning
	///
	/// This function will not wait until the end of the remaining task. You must call and await
	/// `clean_shutdown()` after this.
	pub fn future<'a>(&'a mut self) -> Pin<Box<dyn Future<Output = Result<(), Error>> + Send + 'a>> {
		Box::pin(async move {
			let mut t1 = self.essential_failed_rx.next().fuse();
			let mut t2 = self.on_exit.clone().fuse();

			futures::select! {
				_ = t1 => Err(Error::Other("Essential task failed.".into())),
				_ = t2 => Ok(()),
			}
		})
	}

	/// Signal to terminate all the running tasks.
	pub fn terminate(&mut self) {
		if let Some(signal) = self.signal.take() {
			let _ = signal.fire();
			// NOTE: task will prevent new tasks to be spawned
			self.task_notifier.close_channel();
		}
	}

	/// Set what the task manager should keep alivei
	pub(super) fn keep_alive<T: 'static + Send + Sync>(&mut self, to_keep_alive: T) {
		self.keep_alive = Box::new(to_keep_alive);
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
						"tasks_polling_duration",
						"Duration in seconds of each invocation of Future::poll"
					),
					buckets: exponential_buckets(0.001, 4.0, 9)
						.expect("function parameters are constant and always valid; qed"),
				},
				&["task_name"]
			)?, registry)?,
			poll_start: register(CounterVec::new(
				Opts::new(
					"tasks_polling_started_total",
					"Total number of times we started invoking Future::poll"
				),
				&["task_name"]
			)?, registry)?,
			tasks_spawned: register(CounterVec::new(
				Opts::new(
					"tasks_spawned_total",
					"Total number of tasks that have been spawned on the Service"
				),
				&["task_name"]
			)?, registry)?,
			tasks_ended: register(CounterVec::new(
				Opts::new(
					"tasks_ended_total",
					"Total number of tasks for which Future::poll has returned Ready(()) or panicked"
				),
				&["task_name", "reason"]
			)?, registry)?,
		})
	}
}
