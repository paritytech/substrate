// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

use executor::RuntimeInfo;
use primitives::{H256, Blake2Hasher, traits::CodeExecutor};
use sp_runtime::BuildStorage;
use sp_runtime::traits::Block as BlockT;
use sp_blockchain::Result as ClientResult;

use crate::call_executor::LocalCallExecutor;
use crate::client::Client;
use client_api::{
	light::Storage as BlockchainStorage,
};
use crate::light::backend::Backend;
use crate::light::blockchain::Blockchain;
use crate::light::call_executor::GenesisCallExecutor;
use crate::light::fetcher::LightDataChecker;

/// Create an instance of light client blockchain backend.
pub fn new_light_blockchain<B: BlockT, S: BlockchainStorage<B>>(storage: S) -> Arc<Blockchain<S>> {
	Arc::new(Blockchain::new(storage))
}

/// Create an instance of light client backend.
pub fn new_light_backend<B, S>(blockchain: Arc<Blockchain<S>>) -> Arc<Backend<S, Blake2Hasher>>
	where
		B: BlockT,
		S: BlockchainStorage<B>,
{
	Arc::new(Backend::new(blockchain))
}

/// Create an instance of light client.
pub fn new_light<B, S, GS, RA, E>(
	backend: Arc<Backend<S, Blake2Hasher>>,
	genesis_storage: GS,
	code_executor: E,
) -> ClientResult<Client<Backend<S, Blake2Hasher>, GenesisCallExecutor<
	Backend<S, Blake2Hasher>,
	LocalCallExecutor<Backend<S, Blake2Hasher>, E>
>, B, RA>>
	where
		B: BlockT<Hash=H256>,
		S: BlockchainStorage<B> + 'static,
		GS: BuildStorage,
		E: CodeExecutor + RuntimeInfo,
{
	let local_executor = LocalCallExecutor::new(backend.clone(), code_executor);
	let executor = GenesisCallExecutor::new(backend.clone(), local_executor);
	Client::new(backend, executor, genesis_storage, Default::default(), Default::default())
}

/// Create an instance of fetch data checker.
pub fn new_fetch_checker<E, B: BlockT, S: BlockchainStorage<B>>(
	blockchain: Arc<Blockchain<S>>,
	executor: E,
) -> LightDataChecker<E, Blake2Hasher, B, S>
	where
		E: CodeExecutor,
{
	LightDataChecker::new(blockchain, executor)
}
