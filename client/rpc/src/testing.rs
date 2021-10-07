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

//! Testing utils used by the RPC tests.

use futures::{
	executor,
	task::{FutureObj, Spawn, SpawnError},
};
use jsonrpsee::types::{
	v2::{Response as RpcResponse, RpcError},
	DeserializeOwned,
};
use sp_core::traits::SpawnNamed;
use std::future::Future;

// Executor shared by all tests.
//
// This shared executor is used to prevent `Too many open files` errors
// on systems with a lot of cores.
lazy_static::lazy_static! {
	static ref EXECUTOR: executor::ThreadPool = executor::ThreadPool::new()
		.expect("Failed to create thread pool executor for tests");
}

/// Executor for use in testing
#[derive(Clone, Copy)]
pub struct TaskExecutor;
impl Spawn for TaskExecutor {
	fn spawn_obj(&self, future: FutureObj<'static, ()>) -> Result<(), SpawnError> {
		EXECUTOR.spawn_ok(future);
		Ok(())
	}

	fn status(&self) -> Result<(), SpawnError> {
		Ok(())
	}
}
impl SpawnNamed for TaskExecutor {
	fn spawn_blocking(&self, _name: &'static str, future: futures::future::BoxFuture<'static, ()>) {
		EXECUTOR.spawn_ok(future);
	}

	fn spawn(&self, _name: &'static str, future: futures::future::BoxFuture<'static, ()>) {
		EXECUTOR.spawn_ok(future);
	}
}

/// Wrap a future in a timeout a little more concisely
pub(crate) fn timeout_secs<I, F: Future<Output = I>>(s: u64, f: F) -> tokio::time::Timeout<F> {
	tokio::time::timeout(tokio::time::Duration::from_secs(s), f)
}

pub(crate) fn deser_call<T: DeserializeOwned>(raw: String) -> T {
	let out: RpcResponse<T> = serde_json::from_str(&raw).unwrap();
	out.result
}

pub(crate) fn deser_error<'a>(raw: &'a str) -> RpcError<'a> {
	serde_json::from_str(&raw).unwrap()
}
