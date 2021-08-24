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

use crate::{config::TaskExecutor, task_manager::TaskManager};
use futures::{future::FutureExt, pin_mut, select};
use parking_lot::Mutex;
use std::{any::Any, sync::Arc, time::Duration};

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

	fn wait_on_drop(&self) {
		while *self != 0 {
			std::thread::sleep(std::time::Duration::from_millis(10));
		}
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
		tokio::time::sleep(Duration::from_secs(1)).await;
	}
}

async fn run_background_task_blocking(duration: Duration, _keep_alive: impl Any) {
	loop {
		// block for X sec (not interruptible)
		std::thread::sleep(duration);
		// await for 1 sec (interruptible)
		tokio::time::sleep(Duration::from_secs(1)).await;
	}
}

fn new_task_manager(task_executor: TaskExecutor) -> TaskManager {
	TaskManager::new(task_executor, None).unwrap()
}

#[test]
fn ensure_tasks_are_awaited_on_shutdown() {
	let runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let task_manager = new_task_manager(task_executor);
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn("task1", run_background_task(drop_tester.new_ref()));
	spawn_handle.spawn("task2", run_background_task(drop_tester.new_ref()));
	assert_eq!(drop_tester, 2);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::sleep(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 2);
	runtime.block_on(task_manager.clean_shutdown());
	drop_tester.wait_on_drop();
}

#[test]
fn ensure_keep_alive_during_shutdown() {
	let runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let mut task_manager = new_task_manager(task_executor);
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	task_manager.keep_alive(drop_tester.new_ref());
	spawn_handle.spawn("task1", run_background_task(()));
	assert_eq!(drop_tester, 1);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::sleep(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 1);
	runtime.block_on(task_manager.clean_shutdown());
	drop_tester.wait_on_drop();
}

#[test]
fn ensure_blocking_futures_are_awaited_on_shutdown() {
	let runtime = tokio::runtime::Runtime::new().unwrap();
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
	runtime.block_on(async { tokio::time::sleep(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 2);
	runtime.block_on(task_manager.clean_shutdown());
	assert_eq!(drop_tester, 0);
}

#[test]
fn ensure_no_task_can_be_spawn_after_terminate() {
	let runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let mut task_manager = new_task_manager(task_executor);
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn("task1", run_background_task(drop_tester.new_ref()));
	spawn_handle.spawn("task2", run_background_task(drop_tester.new_ref()));
	assert_eq!(drop_tester, 2);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::sleep(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 2);
	task_manager.terminate();
	spawn_handle.spawn("task3", run_background_task(drop_tester.new_ref()));
	runtime.block_on(task_manager.clean_shutdown());
	drop_tester.wait_on_drop();
}

#[test]
fn ensure_task_manager_future_ends_when_task_manager_terminated() {
	let runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let mut task_manager = new_task_manager(task_executor);
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn("task1", run_background_task(drop_tester.new_ref()));
	spawn_handle.spawn("task2", run_background_task(drop_tester.new_ref()));
	assert_eq!(drop_tester, 2);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::sleep(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 2);
	task_manager.terminate();
	runtime.block_on(task_manager.future()).expect("future has ended without error");
	runtime.block_on(task_manager.clean_shutdown());
	assert_eq!(drop_tester, 0);
}

#[test]
fn ensure_task_manager_future_ends_with_error_when_essential_task_fails() {
	let runtime = tokio::runtime::Runtime::new().unwrap();
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
	runtime.block_on(async { tokio::time::sleep(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 2);
	spawn_essential_handle.spawn("task3", async { panic!("task failed") });
	runtime
		.block_on(task_manager.future())
		.expect_err("future()'s Result must be Err");
	assert_eq!(drop_tester, 2);
	runtime.block_on(task_manager.clean_shutdown());
	drop_tester.wait_on_drop();
}

#[test]
fn ensure_children_tasks_ends_when_task_manager_terminated() {
	let runtime = tokio::runtime::Runtime::new().unwrap();
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
	runtime.block_on(async { tokio::time::sleep(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 4);
	task_manager.terminate();
	runtime.block_on(task_manager.future()).expect("future has ended without error");
	runtime.block_on(task_manager.clean_shutdown());
	drop_tester.wait_on_drop();
}

#[test]
fn ensure_task_manager_future_ends_with_error_when_childs_essential_task_fails() {
	let runtime = tokio::runtime::Runtime::new().unwrap();
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
	runtime.block_on(async { tokio::time::sleep(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 4);
	spawn_essential_handle_child_1.spawn("task5", async { panic!("task failed") });
	runtime
		.block_on(task_manager.future())
		.expect_err("future()'s Result must be Err");
	assert_eq!(drop_tester, 4);
	runtime.block_on(task_manager.clean_shutdown());
	drop_tester.wait_on_drop();
}

#[test]
fn ensure_task_manager_future_continues_when_childs_not_essential_task_fails() {
	let runtime = tokio::runtime::Runtime::new().unwrap();
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
	runtime.block_on(async { tokio::time::sleep(Duration::from_secs(1)).await });
	assert_eq!(drop_tester, 4);
	spawn_handle_child_1.spawn("task5", async { panic!("task failed") });
	runtime.block_on(async {
		let t1 = task_manager.future().fuse();
		let t2 = tokio::time::sleep(Duration::from_secs(3)).fuse();

		pin_mut!(t1, t2);

		select! {
			res = t1 => panic!("task should not have stopped: {:?}", res),
			_ = t2 => {},
		}
	});
	assert_eq!(drop_tester, 4);
	runtime.block_on(task_manager.clean_shutdown());
	drop_tester.wait_on_drop();
}
