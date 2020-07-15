use crate::config::TaskExecutor;
use crate::task_manager::TaskManager;
use futures::future::FutureExt;
use parking_lot::Mutex;
use std::any::Any;
use std::sync::Arc;
use std::time::Duration;

#[derive(Clone)]
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

	fn assert_eq(&self, n: usize) {
		assert_eq!(*self.0.lock(), n, "unexpected value for drop tester");
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
	drop_tester.assert_eq(0);
	let drop_tester_ref_1 = drop_tester.new_ref();
	drop_tester.assert_eq(1);
	let drop_tester_ref_2 = drop_tester.new_ref();
	drop_tester.assert_eq(2);
	drop(drop_tester_ref_1);
	drop_tester.assert_eq(1);
	drop(drop_tester_ref_2);
	drop_tester.assert_eq(0);
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

#[test]
fn ensure_futures_are_awaited_on_shutdown() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let task_manager = TaskManager::new(task_executor, None).unwrap();
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn("task1", run_background_task(drop_tester.new_ref()));
	spawn_handle.spawn("task2", run_background_task(drop_tester.new_ref()));
	drop_tester.assert_eq(2);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	drop_tester.assert_eq(2);
	runtime.block_on(task_manager.clean_shutdown());
	drop_tester.assert_eq(0);
}

#[test]
fn ensure_keep_alive_during_shutdown() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let mut task_manager = TaskManager::new(task_executor, None).unwrap();
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	task_manager.keep_alive(drop_tester.new_ref());
	spawn_handle.spawn("task1", run_background_task(()));
	drop_tester.assert_eq(1);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	drop_tester.assert_eq(1);
	runtime.block_on(task_manager.clean_shutdown());
	drop_tester.assert_eq(0);
}

#[test]
fn ensure_blocking_futures_are_awaited_on_shutdown() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let task_manager = TaskManager::new(task_executor, None).unwrap();
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
	drop_tester.assert_eq(2);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	drop_tester.assert_eq(2);
	runtime.block_on(task_manager.clean_shutdown());
	drop_tester.assert_eq(0);
}

#[test]
fn ensure_no_task_can_be_spawn_after_terminate() {
	let mut runtime = tokio::runtime::Runtime::new().unwrap();
	let handle = runtime.handle().clone();
	let task_executor: TaskExecutor = (move |future, _| handle.spawn(future).map(|_| ())).into();

	let mut task_manager = TaskManager::new(task_executor, None).unwrap();
	let spawn_handle = task_manager.spawn_handle();
	let drop_tester = DropTester::new();
	spawn_handle.spawn("task1", run_background_task(drop_tester.new_ref()));
	spawn_handle.spawn("task2", run_background_task(drop_tester.new_ref()));
	drop_tester.assert_eq(2);
	// allow the tasks to even start
	runtime.block_on(async { tokio::time::delay_for(Duration::from_secs(1)).await });
	drop_tester.assert_eq(2);
	task_manager.terminate();
	spawn_handle.spawn("task3", run_background_task(drop_tester.new_ref()));
	// NOTE: task3 will not increase the count because it has been ignored
	drop_tester.assert_eq(2);
	runtime.block_on(task_manager.clean_shutdown());
	drop_tester.assert_eq(0);
}
