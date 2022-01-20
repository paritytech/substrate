// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

// Executor shared by all tests.
//
// This shared executor is used to prevent `Too many open files` errors
// on systems with a lot of cores.
lazy_static::lazy_static! {
	static ref EXECUTOR: executor::ThreadPool = executor::ThreadPool::new()
		.expect("Failed to create thread pool executor for tests");
}

/// Executor for use in testing
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
