// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Light client components.

pub mod backend;
pub mod blockchain;
pub mod call_executor;
pub mod fetcher;

use std::sync::Arc;

use state_machine::CodeExecutor;

use backend::Backend as ClientBackend;
use client::{Client, GenesisBuilder};
use error::Result as ClientResult;
use light::backend::Backend;
use light::blockchain::Blockchain;
use light::call_executor::RemoteCallExecutor;
use light::fetcher::{Fetcher, LightDataChecker};

/// Create an instance of light client blockchain backend.
pub fn new_light_blockchain<B: ClientBackend, F>(storage: B) -> Arc<Blockchain<B, F>> {
	Arc::new(Blockchain::new(storage))
}

/// Create an instance of light client backend.
pub fn new_light_backend<B: ClientBackend, F>(blockchain: Arc<Blockchain<B, F>>, fetcher: Arc<F>) -> Arc<Backend<B, F>> {
	blockchain.set_fetcher(Arc::downgrade(&fetcher));
	Arc::new(Backend::new(blockchain))
}

/// Create an instance of light client.
pub fn new_light<B, F, GB>(
	backend: Arc<Backend<B, F>>,
	fetcher: Arc<F>,
	genesis_builder: GB,
) -> ClientResult<Client<Backend<B, F>, RemoteCallExecutor<Blockchain<B, F>, F>>>
	where
		B: ClientBackend,
		F: Fetcher,
		GB: GenesisBuilder,
{
	let executor = RemoteCallExecutor::new(backend.blockchain().clone(), fetcher);
	Client::new(backend, executor, genesis_builder)
}

/// Create an instance of fetch data checker.
pub fn new_fetch_checker<B, E, F>(
	blockchain: Arc<Blockchain<B, F>>,
	executor: E,
) -> LightDataChecker<B, E, F>
	where
		B: ClientBackend,
		E: CodeExecutor,
{
	LightDataChecker::new(blockchain, executor)
}
