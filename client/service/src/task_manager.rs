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

use std::{panic, pin::Pin, result::Result, sync::Arc};
use exit_future::Signal;
use log::debug;
use futures::{
	Future, FutureExt,
	future::{select, Either, BoxFuture},
	compat::*,
	task::{Spawn, FutureObj, SpawnError},
};
use prometheus_endpoint::{
	exponential_buckets, register,
	PrometheusError,
	CounterVec, HistogramOpts, HistogramVec, Opts, Registry, U64
};
use sc_client_api::CloneableSpawn;
use crate::config::TaskType;

mod prometheus_future;

/// Type alias for service task executor (usually runtime).
pub type ServiceTaskExecutor = Arc<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>, TaskType) + Send + Sync>;

/// An handle for spawning tasks in the service.
#[derive(Clone)]
pub struct SpawnTaskHandle {
	on_exit: exit_future::Exit,
	executor: ServiceTaskExecutor,
	metrics: Option<Metrics>,
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

		(self.executor)(Box::pin(future), task_type);
	}
}

impl Spawn for SpawnTaskHandle {
	fn spawn_obj(&self, future: FutureObj<'static, ()>)
	-> Result<(), SpawnError> {
		self.spawn("unnamed", future);
		Ok(())
	}
}

impl sp_core::traits::SpawnBlocking for SpawnTaskHandle {
	fn spawn_blocking(&self, name: &'static str, future: BoxFuture<'static, ()>) {
		self.spawn_blocking(name, future);
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

/// Helper struct to manage background/async tasks in Service.
pub struct TaskManager {
	/// A future that resolves when the service has exited, this is useful to
	/// make sure any internally spawned futures stop when the service does.
	on_exit: exit_future::Exit,
	/// A signal that makes the exit future above resolve, fired on service drop.
	signal: Option<Signal>,
	/// How to spawn background tasks.
	executor: ServiceTaskExecutor,
	/// Prometheus metric where to report the polling times.
	metrics: Option<Metrics>,
}

impl TaskManager {
 	/// If a Prometheus registry is passed, it will be used to report statistics about the
 	/// service tasks.
	pub(super) fn new(
		executor: ServiceTaskExecutor,
		prometheus_registry: Option<&Registry>
	) -> Result<Self, PrometheusError> {
		let (signal, on_exit) = exit_future::signal();

		let metrics = prometheus_registry.map(Metrics::register).transpose()?;

		Ok(Self {
			on_exit,
			signal: Some(signal),
			executor,
			metrics,
		})
	}

	/// Spawn background/async task, which will be aware on exit signal.
	///
	/// See also the documentation of [`SpawnTaskHandler::spawn`].
	pub(super) fn spawn(&self, name: &'static str, task: impl Future<Output = ()> + Send + 'static) {
		self.spawn_handle().spawn(name, task)
	}

	pub(super) fn spawn_handle(&self) -> SpawnTaskHandle {
		SpawnTaskHandle {
			on_exit: self.on_exit.clone(),
			executor: self.executor.clone(),
			metrics: self.metrics.clone(),
		}
	}

	/// Clone on exit signal.
	pub(super) fn on_exit(&self) -> exit_future::Exit {
		self.on_exit.clone()
	}
}

impl Drop for TaskManager {
	fn drop(&mut self) {
		debug!(target: "service", "Tasks manager shutdown");
		if let Some(signal) = self.signal.take() {
			let _ = signal.fire();
		}
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
