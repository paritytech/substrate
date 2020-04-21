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

use std::{
	pin::Pin,
	result::Result, sync::Arc,
	task::{Poll, Context},
};
use exit_future::Signal;
use log::{debug, error};
use futures::{
	Future, FutureExt, Stream,
	future::select,
	compat::*,
	task::{Spawn, FutureObj, SpawnError},
};
use prometheus_endpoint::{
	exponential_buckets, register,
	PrometheusError,
	CounterVec, HistogramOpts, HistogramVec, Opts, Registry, U64
};
use sc_client_api::CloneableSpawn;
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedSender, TracingUnboundedReceiver};

mod prometheus_future;

/// Type alias for service task executor (usually runtime).
pub type ServiceTaskExecutor = Arc<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>) + Send + Sync>;

/// Type alias for the task scheduler.
pub type TaskScheduler = TracingUnboundedSender<Pin<Box<dyn Future<Output = ()> + Send>>>;

/// Helper struct to setup background tasks execution for service.
pub struct TaskManagerBuilder {
	/// A future that resolves when the service has exited, this is useful to
	/// make sure any internally spawned futures stop when the service does.
	on_exit: exit_future::Exit,
	/// A signal that makes the exit future above resolve, fired on service drop.
	signal: Option<Signal>,
	/// Sender for futures that must be spawned as background tasks.
	to_spawn_tx: TaskScheduler,
	/// Receiver for futures that must be spawned as background tasks.
	to_spawn_rx: TracingUnboundedReceiver<Pin<Box<dyn Future<Output = ()> + Send>>>,
	/// Prometheus metrics where to report the stats about tasks.
	metrics: Option<Metrics>,
}

impl TaskManagerBuilder {
	/// New asynchronous task manager setup.
	///
	/// If a Prometheus registry is passed, it will be used to report statistics about the
	/// service tasks.
	pub fn new(prometheus_registry: Option<&Registry>) -> Result<Self, PrometheusError> {
		let (signal, on_exit) = exit_future::signal();
		let (to_spawn_tx, to_spawn_rx) = tracing_unbounded("mpsc_task_manager");

		let metrics = prometheus_registry.map(Metrics::register).transpose()?;

		Ok(Self {
			on_exit,
			signal: Some(signal),
			to_spawn_tx,
			to_spawn_rx,
			metrics,
		})
	}

	/// Get spawn handle.
	///
	/// Tasks spawned through this handle will get scheduled once
	/// service is up and running.
	pub fn spawn_handle(&self) -> SpawnTaskHandle {
		SpawnTaskHandle {
			on_exit: self.on_exit.clone(),
			sender: self.to_spawn_tx.clone(),
			metrics: self.metrics.clone(),
		}
	}

	/// Convert into actual task manager from initial setup.
	pub(crate) fn into_task_manager(self, executor: ServiceTaskExecutor) -> TaskManager {
		let TaskManagerBuilder {
			on_exit,
			signal,
			to_spawn_rx,
			to_spawn_tx,
			metrics,
		} = self;
		TaskManager {
			on_exit,
			signal,
			to_spawn_tx,
			to_spawn_rx,
			executor,
			metrics,
		}
	}
}

/// An handle for spawning tasks in the service.
#[derive(Clone)]
pub struct SpawnTaskHandle {
	sender: TaskScheduler,
	on_exit: exit_future::Exit,
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
		let on_exit = self.on_exit.clone();
		let metrics = self.metrics.clone();

		// Note that we increase the started counter here and not within the future. This way,
		// we could properly visualize on Prometheus situations where the spawning doesn't work.
		if let Some(metrics) = &self.metrics {
			metrics.tasks_spawned.with_label_values(&[name]).inc();
			// We do a dummy increase in order for the task to show up in metrics.
			metrics.tasks_ended.with_label_values(&[name]).inc_by(0);
		}

		let future = async move {
			if let Some(metrics) = metrics {
				let poll_duration = metrics.poll_duration.with_label_values(&[name]);
				let poll_start = metrics.poll_start.with_label_values(&[name]);
				let task = prometheus_future::with_poll_durations(poll_duration, poll_start, task);
				futures::pin_mut!(task);
				let _ = select(on_exit, task).await;
				metrics.tasks_ended.with_label_values(&[name]).inc();
			} else {
				futures::pin_mut!(task);
				let _ = select(on_exit, task).await;
			}
		};

		if self.sender.unbounded_send(Box::pin(future)).is_err() {
			error!("Failed to send task to spawn over channel");
		}
	}
}

impl Spawn for SpawnTaskHandle {
	fn spawn_obj(&self, future: FutureObj<'static, ()>)
	-> Result<(), SpawnError> {
		self.spawn("unamed", future);
		Ok(())
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
	/// Sender for futures that must be spawned as background tasks.
	to_spawn_tx: TaskScheduler,
	/// Receiver for futures that must be spawned as background tasks.
	/// Note: please read comment on [`SpawnTaskHandle::spawn`] for why this is a `&'static str`.
	to_spawn_rx: TracingUnboundedReceiver<Pin<Box<dyn Future<Output = ()> + Send>>>,
	/// How to spawn background tasks.
	executor: ServiceTaskExecutor,
	/// Prometheus metric where to report the polling times.
	metrics: Option<Metrics>,
}

impl TaskManager {
	/// Spawn background/async task, which will be aware on exit signal.
	///
	/// See also the documentation of [`SpawnTaskHandler::spawn`].
	pub(super) fn spawn(&self, name: &'static str, task: impl Future<Output = ()> + Send + 'static) {
		self.spawn_handle().spawn(name, task)
	}

	pub(super) fn spawn_handle(&self) -> SpawnTaskHandle {
		SpawnTaskHandle {
			on_exit: self.on_exit.clone(),
			sender: self.to_spawn_tx.clone(),
			metrics: self.metrics.clone(),
		}
	}

	/// Process background task receiver.
	pub(super) fn process_receiver(&mut self, cx: &mut Context) {
		while let Poll::Ready(Some(task_to_spawn)) = Pin::new(&mut self.to_spawn_rx).poll_next(cx) {
			(self.executor)(task_to_spawn);
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
					"Total number of tasks for which Future::poll has returned Ready(())"
				),
				&["task_name"]
			)?, registry)?,
		})
	}
}
