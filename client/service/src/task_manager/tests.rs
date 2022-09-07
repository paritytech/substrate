// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use crate::config::TaskExecutor;
use crate::task_manager::TaskManager;
use futures::{future::FutureExt, pin_mut, select};
use parking_lot::Mutex;
use sc_telemetry::TelemetrySpan;
use std::{any::Any, env, sync::Arc, time::Duration};
use tracing::{event::Event, span::Id, subscriber::Subscriber};
use tracing_subscriber::{
	layer::{Context, SubscriberExt},
	registry::LookupSpan,
	Layer,
};

#[derive(Clone, Debug)]
struct DropTester(Arc<Mutex<usize>>);

struct DropTesterRef(DropTester);

impl DropTester {
	fn new() -> DropTester {
		DropTester(Arc::new(Mutex::new(0)))
	}

	fn new_ref(&self) -> DropTesterRef {
		*self.0.lock() += 1;
		DropTesterRef(self.clone())
	}
}

impl PartialEq<usize> for DropTester {
	fn eq(&self, other: &usize) -> bool {
		&*self.0.lock() == other
	}
}

impl Drop for DropTesterRef {
	fn drop(&mut self) {
		*(self.0).0.lock() -= 1;
	}
}

#[test]
fn ensure_drop_tester_working() {
	let drop_tester = DropTester::new();
	assert_eq!(drop_tester, 0);
	let drop_tester_ref_1 = drop_tester.new_ref();
	assert_eq!(drop_tester, 1);
	let drop_tester_ref_2 = drop_tester.new_ref();
	assert_eq!(drop_tester, 2);
	drop(drop_tester_ref_1);
	assert_eq!(drop_tester, 1);
	drop(drop_tester_ref_2);
	assert_eq!(drop_tester, 0);
}

async fn run_background_task(_keep_alive: impl Any) {
	loop {
		tokio::time::delay_for(Duration::from_secs(1)).await;
	}
}

async fn run_background_task_blocking(duration: Duration, _keep_alive: impl Any) {
	loop {
		// block for X sec (not interruptible)
		std::thread::sleep(duration);
		// await for 1 sec (interruptible)
		tokio::time::delay_for(Duration::from_secs(1)).await;
	}
}

fn new_task_manager(task_executor: TaskExecutor) -> TaskManager {
	TaskManager::new(task_executor, None).unwrap()
}

#[test]
fn ensure_tasks_are_awaited_on_shutdown() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let task_manager = new_task_manager(task_executor);
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn("task1", run_background_task(drop_tester.new_ref()));
	spawn_handle.spawn("task2", run_background_task(drop_tester.new_ref()));
	assert_eq!(drop_tester, 2);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 2);
	runtime.block_on(task_manager.clean_shutdown());
	assert_eq!(drop_tester, 0);
}

#[test]
fn ensure_keep_alive_during_shutdown() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let mut task_manager = new_task_manager(task_executor);
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	task_manager.keep_alive(drop_tester.new_ref());
	spawn_handle.spawn("task1", run_background_task(()));
	assert_eq!(drop_tester, 1);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 1);
	runtime.block_on(task_manager.clean_shutdown());
	assert_eq!(drop_tester, 0);
}

#[test]
fn ensure_blocking_futures_are_awaited_on_shutdown() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let task_manager = new_task_manager(task_executor);
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn(
		"task1",
		run_background_task_blocking(Duration::from_secs(3), drop_tester.new_ref()),
	);
	spawn_handle.spawn(
		"task2",
		run_background_task_blocking(Duration::from_secs(3), drop_tester.new_ref()),
	);
	assert_eq!(drop_tester, 2);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 2);
	runtime.block_on(task_manager.clean_shutdown());
	assert_eq!(drop_tester, 0);
}

#[test]
fn ensure_no_task_can_be_spawn_after_terminate() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let mut task_manager = new_task_manager(task_executor);
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn("task1", run_background_task(drop_tester.new_ref()));
	spawn_handle.spawn("task2", run_background_task(drop_tester.new_ref()));
	assert_eq!(drop_tester, 2);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 2);
	task_manager.terminate();
	spawn_handle.spawn("task3", run_background_task(drop_tester.new_ref()));
	runtime.block_on(task_manager.clean_shutdown());
	assert_eq!(drop_tester, 0);
}

#[test]
fn ensure_task_manager_future_ends_when_task_manager_terminated() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let mut task_manager = new_task_manager(task_executor);
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn("task1", run_background_task(drop_tester.new_ref()));
	spawn_handle.spawn("task2", run_background_task(drop_tester.new_ref()));
	assert_eq!(drop_tester, 2);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 2);
	task_manager.terminate();
	runtime.block_on(task_manager.future()).expect("future has ended without error");
	runtime.block_on(task_manager.clean_shutdown());
	assert_eq!(drop_tester, 0);
}

#[test]
fn ensure_task_manager_future_ends_with_error_when_essential_task_fails() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let mut task_manager = new_task_manager(task_executor);
	let spawn_handle = task_manager.spawn_handle();
	let spawn_essential_handle = task_manager.spawn_essential_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn("task1", run_background_task(drop_tester.new_ref()));
	spawn_handle.spawn("task2", run_background_task(drop_tester.new_ref()));
	assert_eq!(drop_tester, 2);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 2);
	spawn_essential_handle.spawn("task3", async { panic!("task failed") });
	runtime.block_on(task_manager.future()).expect_err("future()'s Result must be Err");
	assert_eq!(drop_tester, 2);
	runtime.block_on(task_manager.clean_shutdown());
	assert_eq!(drop_tester, 0);
}

#[test]
fn ensure_children_tasks_ends_when_task_manager_terminated() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let mut task_manager = new_task_manager(task_executor.clone());
	let child_1 = new_task_manager(task_executor.clone());
	let spawn_handle_child_1 = child_1.spawn_handle();
	let child_2 = new_task_manager(task_executor.clone());
	let spawn_handle_child_2 = child_2.spawn_handle();
	task_manager.add_child(child_1);
	task_manager.add_child(child_2);
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn("task1", run_background_task(drop_tester.new_ref()));
	spawn_handle.spawn("task2", run_background_task(drop_tester.new_ref()));
	spawn_handle_child_1.spawn("task3", run_background_task(drop_tester.new_ref()));
	spawn_handle_child_2.spawn("task4", run_background_task(drop_tester.new_ref()));
	assert_eq!(drop_tester, 4);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 4);
	task_manager.terminate();
	runtime.block_on(task_manager.future()).expect("future has ended without error");
	runtime.block_on(task_manager.clean_shutdown());
	assert_eq!(drop_tester, 0);
}

#[test]
fn ensure_task_manager_future_ends_with_error_when_childs_essential_task_fails() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let mut task_manager = new_task_manager(task_executor.clone());
	let child_1 = new_task_manager(task_executor.clone());
	let spawn_handle_child_1 = child_1.spawn_handle();
	let spawn_essential_handle_child_1 = child_1.spawn_essential_handle();
	let child_2 = new_task_manager(task_executor.clone());
	let spawn_handle_child_2 = child_2.spawn_handle();
	task_manager.add_child(child_1);
	task_manager.add_child(child_2);
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn("task1", run_background_task(drop_tester.new_ref()));
	spawn_handle.spawn("task2", run_background_task(drop_tester.new_ref()));
	spawn_handle_child_1.spawn("task3", run_background_task(drop_tester.new_ref()));
	spawn_handle_child_2.spawn("task4", run_background_task(drop_tester.new_ref()));
	assert_eq!(drop_tester, 4);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 4);
	spawn_essential_handle_child_1.spawn("task5", async { panic!("task failed") });
	runtime.block_on(task_manager.future()).expect_err("future()'s Result must be Err");
	assert_eq!(drop_tester, 4);
	runtime.block_on(task_manager.clean_shutdown());
	assert_eq!(drop_tester, 0);
}

#[test]
fn ensure_task_manager_future_continues_when_childs_not_essential_task_fails() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let mut task_manager = new_task_manager(task_executor.clone());
	let child_1 = new_task_manager(task_executor.clone());
	let spawn_handle_child_1 = child_1.spawn_handle();
	let child_2 = new_task_manager(task_executor.clone());
	let spawn_handle_child_2 = child_2.spawn_handle();
	task_manager.add_child(child_1);
	task_manager.add_child(child_2);
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn("task1", run_background_task(drop_tester.new_ref()));
	spawn_handle.spawn("task2", run_background_task(drop_tester.new_ref()));
	spawn_handle_child_1.spawn("task3", run_background_task(drop_tester.new_ref()));
	spawn_handle_child_2.spawn("task4", run_background_task(drop_tester.new_ref()));
	assert_eq!(drop_tester, 4);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 4);
	spawn_handle_child_1.spawn("task5", async { panic!("task failed") });
	runtime.block_on(async {
		let t1 = task_manager.future().fuse();
		let t2 = tokio::time::delay_for(Duration::from_secs(3)).fuse();

		pin_mut!(t1, t2);

		select! {
			res = t1 => panic!("task should not have stopped: {:?}", res),
			_ = t2 => {},
		}
	});
	assert_eq!(drop_tester, 4);
	runtime.block_on(task_manager.clean_shutdown());
	assert_eq!(drop_tester, 0);
}

struct TestLayer {
	spans_found: Arc<Mutex<Option<Vec<Id>>>>,
}

impl<S> Layer<S> for TestLayer
where
	S: Subscriber + for<'a> LookupSpan<'a>,
{
	fn on_event(&self, _: &Event<'_>, ctx: Context<S>) {
		let mut spans_found = self.spans_found.lock();

		if spans_found.is_some() {
			panic!("on_event called multiple times");
		}

		*spans_found = Some(ctx.scope().map(|x| x.id()).collect());
	}
}

fn setup_subscriber() -> (
	impl Subscriber + for<'a> LookupSpan<'a>,
	Arc<Mutex<Option<Vec<Id>>>>,
) {
	let spans_found = Arc::new(Mutex::new(Default::default()));
	let layer = TestLayer {
		spans_found: spans_found.clone(),
	};
	let subscriber = tracing_subscriber::fmt().finish().with(layer);
	(subscriber, spans_found)
}

/// This is not an actual test, it is used by the `telemetry_span_is_forwarded_to_task` test.
/// The given test will call the test executable and only execute this one test that
/// test that the telemetry span and the prefix span are forwarded correctly. This needs to be done
/// in a separate process to avoid interfering with the other tests.
#[test]
fn subprocess_telemetry_span_is_forwarded_to_task() {
	if env::var("SUBPROCESS_TEST").is_err() {
		return;
	}

	let (subscriber, spans_found) = setup_subscriber();
	tracing_log::LogTracer::init().unwrap();
	let _sub_guard = tracing::subscriber::set_global_default(subscriber);

	let mut runtime = tokio::runtime::Runtime::new().unwrap();

	let prefix_span = tracing::info_span!("prefix");
	let _enter_prefix_span = prefix_span.enter();

	let telemetry_span = TelemetrySpan::new();
	let _enter_telemetry_span = telemetry_span.enter();

	let handle = runtime.handle().clone();
	let task_executor = TaskExecutor::from(move |fut, _| handle.spawn(fut).map(|_| ()));
	let task_manager = new_task_manager(task_executor);

	let (sender, receiver) = futures::channel::oneshot::channel();

	task_manager.spawn_handle().spawn(
		"log-something",
		async move {
			log::info!("boo!");
			sender.send(()).unwrap();
		}
		.boxed(),
	);

	runtime.block_on(receiver).unwrap();
	runtime.block_on(task_manager.clean_shutdown());

	let spans = spans_found.lock().take().unwrap();
	assert_eq!(2, spans.len());

	assert_eq!(spans[0], prefix_span.id().unwrap());
	assert_eq!(spans[1], telemetry_span.span().id().unwrap());
}

#[test]
fn telemetry_span_is_forwarded_to_task() {
	let executable = env::current_exe().unwrap();
	let output = std::process::Command::new(executable)
		.env("SUBPROCESS_TEST", "1")
		.args(&["--nocapture", "subprocess_telemetry_span_is_forwarded_to_task"])
		.output()
		.unwrap();
	println!("{}", String::from_utf8(output.stdout).unwrap());
	eprintln!("{}", String::from_utf8(output.stderr).unwrap());
	assert!(output.status.success());
}
