// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

use rpc::futures::future as future01;
use futures::{executor, compat::Future01CompatExt, FutureExt};

// Executor shared by all tests.
//
// This shared executor is used to prevent `Too many open files` errors
// on systems with a lot of cores.
lazy_static::lazy_static! {
	static ref EXECUTOR: executor::ThreadPool = executor::ThreadPool::new()
		.expect("Failed to create thread pool executor for tests");
}

type Boxed01Future01 = Box<dyn future01::Future<Item = (), Error = ()> + Send + 'static>;

/// Executor for use in testing
pub struct TaskExecutor;
impl future01::Executor<Boxed01Future01> for TaskExecutor {
	fn execute(
		&self,
		future: Boxed01Future01,
	) -> std::result::Result<(), future01::ExecuteError<Boxed01Future01>>{
		EXECUTOR.spawn_ok(future.compat().map(drop));
		Ok(())
	}
}
