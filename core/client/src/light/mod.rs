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
use primitives::{H256, Blake2Hasher};
use runtime_primitives::BuildStorage;
use runtime_primitives::traits::Block as BlockT;
use state_machine::CodeExecutor;

use crate::call_executor::LocalCallExecutor;
use crate::client::Client;
use crate::error::Result as ClientResult;
use crate::light::backend::Backend;
use crate::light::blockchain::{Blockchain, Storage as BlockchainStorage};
use crate::light::call_executor::{RemoteCallExecutor, RemoteOrLocalCallExecutor};
use crate::light::fetcher::{Fetcher, LightDataChecker};

/// Create an instance of light client blockchain backend.
pub fn new_light_blockchain<B: BlockT, S: BlockchainStorage<B>, F>(storage: S) -> Arc<Blockchain<S, F>> {
	Arc::new(Blockchain::new(storage))
}

/// Create an instance of light client backend.
pub fn new_light_backend<B, S, F>(blockchain: Arc<Blockchain<S, F>>, fetcher: Arc<F>) -> Arc<Backend<S, F, Blake2Hasher>>
	where
		B: BlockT,
		S: BlockchainStorage<B>,
		F: Fetcher<B>,
{
	blockchain.set_fetcher(Arc::downgrade(&fetcher));
	Arc::new(Backend::new(blockchain))
}

/// Create an instance of light client.
pub fn new_light<B, S, F, GS, RA, E>(
	backend: Arc<Backend<S, F, Blake2Hasher>>,
	fetcher: Arc<F>,
	genesis_storage: GS,
	code_executor: E,
) -> ClientResult<Client<Backend<S, F, Blake2Hasher>, RemoteOrLocalCallExecutor<
	B,
	Backend<S, F, Blake2Hasher>,
	RemoteCallExecutor<Blockchain<S, F>, F>,
	LocalCallExecutor<Backend<S, F, Blake2Hasher>, E>
>, B, RA>>
	where
		B: BlockT<Hash=H256>,
		S: BlockchainStorage<B>,
		F: Fetcher<B>,
		GS: BuildStorage,
		E: CodeExecutor<Blake2Hasher> + RuntimeInfo,
{
	let remote_executor = RemoteCallExecutor::new(backend.blockchain().clone(), fetcher);
	let local_executor = LocalCallExecutor::new(backend.clone(), code_executor);
	let executor = RemoteOrLocalCallExecutor::new(backend.clone(), remote_executor, local_executor);
	Client::new(backend, executor, genesis_storage, Default::default())
}

/// Create an instance of fetch data checker.
pub fn new_fetch_checker<E, B: BlockT, S: BlockchainStorage<B>, F>(
	blockchain: Arc<Blockchain<S, F>>,
	executor: E,
) -> LightDataChecker<E, Blake2Hasher, B, S, F>
	where
		E: CodeExecutor<Blake2Hasher>,
{
	LightDataChecker::new(blockchain, executor)
}
