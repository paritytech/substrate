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

//! Light client components.

use sp_runtime::traits::{Block as BlockT, HashFor};
use std::sync::Arc;
use sp_core::traits::{CodeExecutor, SpawnNamed};

pub mod backend;
pub mod blockchain;
pub mod call_executor;
pub mod fetcher;

pub use {backend::*, blockchain::*, call_executor::*, fetcher::*};

/// Create an instance of fetch data checker.
pub fn new_fetch_checker<E, B: BlockT, S: BlockchainStorage<B>>(
	blockchain: Arc<Blockchain<S>>,
	executor: E,
	spawn_handle: Box<dyn SpawnNamed>,
) -> LightDataChecker<E, HashFor<B>, B, S>
	where
		E: CodeExecutor,
{
	LightDataChecker::new(blockchain, executor, spawn_handle)
}

/// Create an instance of light client blockchain backend.
pub fn new_light_blockchain<B: BlockT, S: BlockchainStorage<B>>(storage: S) -> Arc<Blockchain<S>> {
	Arc::new(Blockchain::new(storage))
}

/// Create an instance of light client backend.
pub fn new_light_backend<B, S>(blockchain: Arc<Blockchain<S>>) -> Arc<Backend<S, HashFor<B>>>
	where
		B: BlockT,
		S: BlockchainStorage<B>,
{
	Arc::new(Backend::new(blockchain))
}
