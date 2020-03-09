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
	result::Result, sync::Arc,
	task::{Poll, Context},
	borrow::Cow, pin::Pin,
};
use exit_future::Signal;
use log::{debug, error};
use futures::{
	Future, FutureExt, Stream,
	future::select, channel::mpsc,
	compat::*,
	task::{Spawn, FutureObj, SpawnError},
};

/// Type alias for service task executor (usually runtime).
pub type ServiceTaskExecutor = Arc<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>) + Send + Sync>;

/// Type alias for the task scheduler.
pub type TaskScheduler = mpsc::UnboundedSender<(Pin<Box<dyn Future<Output = ()> + Send>>, Cow<'static, str>)>;

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
	to_spawn_rx: mpsc::UnboundedReceiver<(Pin<Box<dyn Future<Output = ()> + Send>>, Cow<'static, str>)>,
}

impl TaskManagerBuilder {
	/// New asynchronous task manager setup.
	pub fn new() -> Self {
		let (signal, on_exit) = exit_future::signal();
		let (to_spawn_tx, to_spawn_rx) = mpsc::unbounded();
		Self {
			on_exit,
			signal: Some(signal),
			to_spawn_tx,
			to_spawn_rx,
		}
	}

	/// Get spawn handle.
	///
	/// Tasks spawned through this handle will get scheduled once
	/// service is up and running.
	pub fn spawn_handle(&self) -> SpawnTaskHandle {
		SpawnTaskHandle {
			on_exit: self.on_exit.clone(),
			sender: self.to_spawn_tx.clone(),
		}
	}

	/// Convert into actual task manager from initial setup.
	pub(crate) fn into_task_manager(self, executor: ServiceTaskExecutor) -> TaskManager {
		let TaskManagerBuilder {
			on_exit,
			signal,
			to_spawn_rx,
			to_spawn_tx
		} = self;
		TaskManager {
			on_exit,
			signal,
			to_spawn_tx,
			to_spawn_rx,
			executor,
		}
	}
}

/// An handle for spawning tasks in the service.
#[derive(Clone)]
pub struct SpawnTaskHandle {
	sender: TaskScheduler,
	on_exit: exit_future::Exit,
}

impl SpawnTaskHandle {
	/// Spawns the given task with the given name.
	pub fn spawn(&self, name: impl Into<Cow<'static, str>>, task: impl Future<Output = ()> + Send + 'static) {
		let on_exit = self.on_exit.clone();
		let future = async move {
			futures::pin_mut!(task);
			let _ = select(on_exit, task).await;
		};
		if self.sender.unbounded_send((Box::pin(future), name.into())).is_err() {
			error!("Failed to send task to spawn over channel");
		}
	}
}

impl Spawn for SpawnTaskHandle {
	fn spawn_obj(&self, future: FutureObj<'static, ()>)
	-> Result<(), SpawnError> {
		let future = select(self.on_exit.clone(), future).map(drop);
		self.sender.unbounded_send((Box::pin(future), From::from("unnamed")))
			.map_err(|_| SpawnError::shutdown())
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
	to_spawn_rx: mpsc::UnboundedReceiver<(Pin<Box<dyn Future<Output = ()> + Send>>, Cow<'static, str>)>,
	/// How to spawn background tasks.
	executor: ServiceTaskExecutor,
}

impl TaskManager {
	/// Spawn background/async task, which will be aware on exit signal.
	pub(super) fn spawn(&self, name: impl Into<Cow<'static, str>>, task: impl Future<Output = ()> + Send + 'static) {
		let on_exit = self.on_exit.clone();
		let future = async move {
			futures::pin_mut!(task);
			let _ = select(on_exit, task).await;
		};
		if self.to_spawn_tx.unbounded_send((Box::pin(future), name.into())).is_err() {
			error!("Failed to send task to spawn over channel");
		}
	}

	pub(super) fn spawn_handle(&self) -> SpawnTaskHandle {
		SpawnTaskHandle {
			on_exit: self.on_exit.clone(),
			sender: self.to_spawn_tx.clone(),
		}
	}

	/// Get sender where background/async tasks can be sent.
	pub(super) fn scheduler(&self) -> TaskScheduler {
		self.to_spawn_tx.clone()
	}

	/// Process background task receiver.
	pub(super) fn process_receiver(&mut self, cx: &mut Context) {
		while let Poll::Ready(Some((task_to_spawn, name))) = Pin::new(&mut self.to_spawn_rx).poll_next(cx) {
			(self.executor)(Box::pin(futures_diagnose::diagnose(name, task_to_spawn)));
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
