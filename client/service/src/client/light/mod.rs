// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Light client components.

pub mod backend;
pub mod blockchain;
pub mod call_executor;
pub mod fetcher;

use std::sync::Arc;

use sc_executor::RuntimeInfo;
use sp_core::traits::CodeExecutor;
use sp_runtime::BuildStorage;
use sp_runtime::traits::{Block as BlockT, HashFor};
use sp_blockchain::Result as ClientResult;
use prometheus_endpoint::Registry;

use super::call_executor::LocalCallExecutor;
use super::client::{Client,ClientConfig};
use sc_client_api::{
	light::Storage as BlockchainStorage, CloneableSpawn,
};
use self::backend::Backend;
use self::blockchain::Blockchain;
use self::call_executor::GenesisCallExecutor;
use self::fetcher::LightDataChecker;

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

/// Create an instance of light client.
pub fn new_light<B, S, RA, E>(
	backend: Arc<Backend<S, HashFor<B>>>,
	genesis_storage: &dyn BuildStorage,
	code_executor: E,
	spawn_handle: Box<dyn CloneableSpawn>,
	prometheus_registry: Option<Registry>,
) -> ClientResult<
		Client<
			Backend<S, HashFor<B>>,
			GenesisCallExecutor<
				Backend<S, HashFor<B>>,
				LocalCallExecutor<Backend<S, HashFor<B>>, E>
			>,
			B,
			RA
		>
	>
	where
		B: BlockT,
		S: BlockchainStorage<B> + 'static,
		E: CodeExecutor + RuntimeInfo + Clone + 'static,
{
	let local_executor = LocalCallExecutor::new(backend.clone(), code_executor, spawn_handle.clone(), ClientConfig::default());
	let executor = GenesisCallExecutor::new(backend.clone(), local_executor);
	Client::new(
		backend,
		executor,
		genesis_storage,
		Default::default(),
		Default::default(),
		Default::default(),
		prometheus_registry,
		ClientConfig::default(),
	)
}

/// Create an instance of fetch data checker.
pub fn new_fetch_checker<E, B: BlockT, S: BlockchainStorage<B>>(
	blockchain: Arc<Blockchain<S>>,
	executor: E,
	spawn_handle: Box<dyn CloneableSpawn>,
) -> LightDataChecker<E, HashFor<B>, B, S>
	where
		E: CodeExecutor,
{
	LightDataChecker::new(blockchain, executor, spawn_handle)
}
