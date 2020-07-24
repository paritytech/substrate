// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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
