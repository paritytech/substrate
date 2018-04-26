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

//! Polkadot clients -> service adapter.

use std::sync::Arc;
use parking_lot::Mutex;
use client::{self, BlockchainEvents, ChainHead, ChainData, StateData, ContractCaller};
use client::in_mem::Backend as InMemory;
use codec::{self, Slicable};
use error::Error;
use light_client;
use network::{Service as NetworkService, ConsensusService as NetworkConsensusService,
	Params as NetworkParams, TransactionPool as NetworkTransactionPool};
use polkadot_api::PolkadotApi;
use polkadot_executor::Executor as LocalDispatch;
use primitives::block::{Id as BlockId, Extrinsic, ExtrinsicHash, HeaderHash};
use primitives::hashing;
use substrate_executor::NativeExecutor;
use transaction_pool::{self, TransactionPool};

type FullClient = client::Client<InMemory, NativeExecutor<LocalDispatch>>;
type LightClient = light_client::LightClient;

/// Clients adapter.
#[derive(Clone)]
pub enum Client {
	/// Working with full client.
	Full(Arc<FullClient>),
	/// Working with light client.
	Light(Arc<LightClient>),
}

/// Transaction pool adapter to use with full client.
struct FullTransactionPoolAdapter {
	pool: Arc<Mutex<TransactionPool>>,
	client: Arc<FullClient>,
}

/// Transaction pool adapter to use with light client.
struct LighTransactionsPoolAdapter;

impl Client {
	/// Get shared blockchain events instance.
	pub fn chain_events(&self) -> Arc<BlockchainEvents> {
		match *self {
			Client::Full(ref c) => c.clone(),
			Client::Light(ref c) => c.clone(),
		}
	}

	/// Get shared chain head instance.
	pub fn chain_head(&self) -> Arc<ChainHead> {
		match *self {
			Client::Full(ref c) => c.clone(),
			Client::Light(ref c) => c.clone(),
		}
	}

	/// Get shared chain data instance.
	pub fn chain_data(&self) -> Arc<ChainData> {
		match *self {
			Client::Full(ref c) => c.clone(),
			Client::Light(ref c) => c.clone(),
		}
	}

	/// Get shared state data instance.
	pub fn state_data(&self) -> Arc<StateData> {
		match *self {
			Client::Full(ref c) => c.clone(),
			Client::Light(ref c) => c.clone(),
		}
	}

	/// Get shared contract caller instance.
	pub fn contract_caller(&self) -> Arc<ContractCaller> {
		match *self {
			Client::Full(ref c) => c.clone(),
			Client::Light(ref c) => c.clone(),
		}
	}

	/// Create transaction pool adapter to use with network.
	pub fn create_transaction_pool_adapter(&self, pool: Arc<Mutex<TransactionPool>>) -> Arc<NetworkTransactionPool> {
		match *self {
			Client::Full(ref client) => Arc::new(FullTransactionPoolAdapter {
				pool: pool.clone(),
				client: client.clone(),
			}),
			Client::Light(_) => Arc::new(LighTransactionsPoolAdapter),
		}
	}

	/// Create network service to use with current client.
	pub fn create_network_service(&self, params: NetworkParams) -> Result<(Arc<NetworkService>, Option<Arc<NetworkConsensusService>>), Error> {
		match *self {
			Client::Full(ref client) => NetworkService::new_full(client.clone(), params)
				.map(|(n, nc)| (n, Some(nc)))
				.map_err(Into::into),
			Client::Light(ref client) => NetworkService::new_light(client.clone(), params)
				.map(|n| (n, None))
				.map_err(Into::into),
		}
	}

	/// Prune imported transactions from pool.
	pub fn prune_imported(&self, pool: &Mutex<TransactionPool>, hash: HeaderHash) {
		match *self {
			Client::Full(ref client) => prune_imported(&*client, pool, hash),
			Client::Light(_) => (),
		}
	}
}

impl NetworkTransactionPool for FullTransactionPoolAdapter {
	fn transactions(&self) -> Vec<(ExtrinsicHash, Vec<u8>)> {
		let best_block = match self.client.info() {
			Ok(info) => info.chain.best_hash,
			Err(e) => {
				debug!("Error getting best block: {:?}", e);
				return Vec::new();
			}
		};
		let id = self.client.check_id(BlockId::Hash(best_block)).expect("Best block is always valid; qed.");
		let ready = transaction_pool::Ready::create(id, &*self.client);
		self.pool.lock().pending(ready).map(|t| {
			let hash = ::primitives::Hash::from(&t.hash()[..]);
			let tx = codec::Slicable::encode(t.as_transaction());
			(hash, tx)
		}).collect()
	}

	fn import(&self, transaction: &[u8]) -> Option<ExtrinsicHash> {
		if let Some(tx) = codec::Slicable::decode(&mut &transaction[..]) {
			match self.pool.lock().import(tx) {
				Ok(t) => Some(t.hash()[..].into()),
				Err(e) => match *e.kind() {
					transaction_pool::ErrorKind::AlreadyImported(hash) => Some(hash[..].into()),
					_ => {
						debug!("Error adding transaction to the pool: {:?}", e);
						None
					},
				}
			}
		} else {
			debug!("Error decoding transaction");
			None
		}
	}
}

impl NetworkTransactionPool for LighTransactionsPoolAdapter {
	fn transactions(&self) -> Vec<(ExtrinsicHash, Vec<u8>)> {
		Vec::new() // TODO [light]: implement me
	}

	fn import(&self, _transaction: &[u8]) -> Option<ExtrinsicHash> {
		None // TODO [light]: implement me
	}
}

fn prune_transactions(pool: &mut TransactionPool, extrinsics: &[Extrinsic]) {
	for extrinsic in extrinsics {
		let hash: _ = hashing::blake2_256(&extrinsic.encode()).into();
		pool.remove(&hash, true);
	}
}

/// Produce a task which prunes any finalized transactions from the pool.
fn prune_imported(client: &FullClient, pool: &Mutex<TransactionPool>, hash: HeaderHash) {
	let id = BlockId::Hash(hash);
	match client.body(&id) {
		Ok(Some(body)) => prune_transactions(&mut *pool.lock(), &body[..]),
		Ok(None) => warn!("Missing imported block {:?}", hash),
		Err(e) => warn!("Failed to fetch block: {:?}", e),
	}
}
