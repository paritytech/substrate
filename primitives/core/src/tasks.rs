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

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Module for low-level asynchronous processing.

use crate::traits::CloneableSpawn;
use futures::{executor, task};

/// Simple task executor.
///
/// Uses single thread for scheduling tasks. Can be cloned and used in
/// runtime host (implements `CloneableSpawn`).
#[derive(Debug, Clone)]
pub struct Executor {
	pool: executor::ThreadPool,
}

impl Executor {
	fn new() -> Self {
		Self {
			pool: executor::ThreadPool::builder().pool_size(1).create()
				.expect("Failed to create task executor")
		}
	}
}

impl task::Spawn for Executor {
	fn spawn_obj(&self, future: task::FutureObj<'static, ()>)
	-> Result<(), task::SpawnError> {
		self.pool.spawn_obj(future)
	}
}

impl CloneableSpawn for Executor {
	fn clone(&self) -> Box<dyn CloneableSpawn> {
		Box::new(Clone::clone(self))
	}
}

/// Create tasks executor.
pub fn executor() -> Box<dyn CloneableSpawn> {
	Box::new(Executor::new())
}