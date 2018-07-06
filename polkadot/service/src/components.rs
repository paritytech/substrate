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
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

//! Polkadot service components.

use std::collections::HashMap;
use std::sync::Arc;
use chain_spec::ChainSpec;
use client_db;
use client::{self, Client};
use codec::{self, Slicable};
use consensus;
use error;
use keystore::Store as Keystore;
use network::{self, OnDemand};
use polkadot_api;
use polkadot_executor::Executor as LocalDispatch;
use polkadot_network::NetworkService;
use polkadot_primitives::{Block, BlockId, Hash};
use state_machine;
use substrate_executor::NativeExecutor;
use transaction_pool::{self, TransactionPool};
use tokio::runtime::TaskExecutor;

/// Code executor.
pub type CodeExecutor = NativeExecutor<LocalDispatch>;

/// Polkadot service components.
pub trait Components {
	/// Client backend type.
	type Backend: 'static + client::backend::Backend<Block>;

	/// Polkadot API type.
	type Api: 'static + polkadot_api::PolkadotApi + Send + Sync;

	/// Code executor type.
	type Executor: 'static + client::CallExecutor<Block> + Send + Sync;

	/// Create client.
	fn build_client(&self, settings: client_db::DatabaseSettings, executor: CodeExecutor, chain_spec: &ChainSpec)
		-> Result<(Arc<Client<Self::Backend, Self::Executor, Block>>, Option<Arc<OnDemand<Block, NetworkService>>>), error::Error>;

	/// Create api.
	fn build_api(&self, client: Arc<Client<Self::Backend, Self::Executor, Block>>) -> Arc<Self::Api>;

	/// Create network transaction pool adapter.
	fn build_network_tx_pool(&self, client: Arc<client::Client<Self::Backend, Self::Executor, Block>>, tx_pool: Arc<TransactionPool<Self::Api>>)
		-> Arc<network::TransactionPool<Block>>;

	/// Create consensus service.
	fn build_consensus(
		&self,
		client: Arc<Client<Self::Backend, Self::Executor, Block>>,
		network: Arc<NetworkService>,
		tx_pool: Arc<TransactionPool<Self::Api>>,
		keystore: &Keystore,
		task_executor: TaskExecutor,
	)
		-> Result<Option<consensus::Service>, error::Error>;
}

/// Components for full Polkadot service.
pub struct FullComponents {
	/// Is this a validator node?
	pub is_validator: bool,
}

impl Components for FullComponents {
	type Backend = client_db::Backend<Block>;
	type Api = Client<Self::Backend, Self::Executor, Block>;
	type Executor = client::LocalCallExecutor<client_db::Backend<Block>, NativeExecutor<LocalDispatch>>;

	fn build_client(&self, db_settings: client_db::DatabaseSettings, executor: CodeExecutor, chain_spec: &ChainSpec)
		-> Result<(Arc<client::Client<Self::Backend, Self::Executor, Block>>, Option<Arc<OnDemand<Block, NetworkService>>>), error::Error> {
		Ok((Arc::new(client_db::new_client(db_settings, executor, chain_spec)?), None))
	}

	fn build_api(&self, client: Arc<client::Client<Self::Backend, Self::Executor, Block>>) -> Arc<Self::Api> {
		client
	}

	fn build_network_tx_pool(&self, client: Arc<client::Client<Self::Backend, Self::Executor, Block>>, pool: Arc<TransactionPool<Self::Api>>)
		-> Arc<network::TransactionPool<Block>> {
		Arc::new(TransactionPoolAdapter {
			imports_external_transactions: true,
			pool,
			client,
		})
	}

	fn build_consensus(
		&self,
		client: Arc<client::Client<Self::Backend, Self::Executor, Block>>,
		network: Arc<NetworkService>,
		tx_pool: Arc<TransactionPool<Self::Api>>,
		keystore: &Keystore,
		task_executor: TaskExecutor,
	)
		-> Result<Option<consensus::Service>, error::Error>
	{
		if !self.is_validator {
			return Ok(None);
		}

		// Load the first available key
		let key = keystore.load(&keystore.contents()?[0], "")?;
		info!("Using authority key {}", key.public());

		let consensus_net = ::polkadot_network::consensus::ConsensusNetwork::new(network, client.clone());
		Ok(Some(consensus::Service::new(
			client.clone(),
			client.clone(),
			consensus_net,
			tx_pool.clone(),
			task_executor,
			::std::time::Duration::from_millis(4000), // TODO: dynamic
			key,
		)))
	}
}

/// Components for light Polkadot service.
pub struct LightComponents;

impl Components for LightComponents {
	type Backend = client::light::backend::Backend<client_db::light::LightStorage<Block>, network::OnDemand<Block, NetworkService>>;
	type Api = polkadot_api::light::RemotePolkadotApiWrapper<Self::Backend, Self::Executor>;
	type Executor = client::light::call_executor::RemoteCallExecutor<
		client::light::blockchain::Blockchain<client_db::light::LightStorage<Block>, network::OnDemand<Block, NetworkService>>,
		network::OnDemand<Block, NetworkService>>;

	fn build_client(&self, db_settings: client_db::DatabaseSettings, executor: CodeExecutor, spec: &ChainSpec)
		-> Result<(Arc<client::Client<Self::Backend, Self::Executor, Block>>, Option<Arc<OnDemand<Block, NetworkService>>>), error::Error> {
		let db_storage = client_db::light::LightStorage::new(db_settings)?;
		let light_blockchain = client::light::new_light_blockchain(db_storage);
		let fetch_checker = Arc::new(client::light::new_fetch_checker(light_blockchain.clone(), executor));
		let fetcher = Arc::new(network::OnDemand::new(fetch_checker));
		let client_backend = client::light::new_light_backend(light_blockchain, fetcher.clone());
		let client = client::light::new_light(client_backend, fetcher.clone(), spec)?;
		Ok((Arc::new(client), Some(fetcher)))
	}

	fn build_api(&self, client: Arc<client::Client<Self::Backend, Self::Executor, Block>>) -> Arc<Self::Api> {
		Arc::new(polkadot_api::light::RemotePolkadotApiWrapper(client.clone()))
	}

	fn build_network_tx_pool(&self, client: Arc<client::Client<Self::Backend, Self::Executor, Block>>, pool: Arc<TransactionPool<Self::Api>>)
		-> Arc<network::TransactionPool<Block>> {
		Arc::new(TransactionPoolAdapter {
			imports_external_transactions: false,
			pool,
			client,
		})
	}

	fn build_consensus(
		&self,
		_client: Arc<client::Client<Self::Backend, Self::Executor, Block>>,
		_network: Arc<NetworkService>,
		_tx_pool: Arc<TransactionPool<Self::Api>>,
		_keystore: &Keystore,
		_task_executor: TaskExecutor,
	)
		-> Result<Option<consensus::Service>, error::Error>
	{
		Ok(None)
	}
}

/// Transaction pool adapter.
pub struct TransactionPoolAdapter<B, E, A> where A: Send + Sync, E: Send + Sync {
	imports_external_transactions: bool,
	pool: Arc<TransactionPool<A>>,
	client: Arc<Client<B, E, Block>>,
}

impl<B, E, A> TransactionPoolAdapter<B, E, A>
	where
		A: Send + Sync,
		B: client::backend::Backend<Block> + Send + Sync,
		E: client::CallExecutor<Block> + Send + Sync,
		client::error::Error: From<<<B as client::backend::Backend<Block>>::State as state_machine::backend::Backend>::Error>,
{
	fn best_block_id(&self) -> Option<BlockId> {
		self.client.info()
			.map(|info| BlockId::hash(info.chain.best_hash))
			.map_err(|e| {
				debug!("Error getting best block: {:?}", e);
			})
			.ok()
	}
}

impl<B, E, A> network::TransactionPool<Block> for TransactionPoolAdapter<B, E, A>
	where
		B: client::backend::Backend<Block> + Send + Sync,
		E: client::CallExecutor<Block> + Send + Sync,
		client::error::Error: From<<<B as client::backend::Backend<Block>>::State as state_machine::backend::Backend>::Error>,
		A: polkadot_api::PolkadotApi + Send + Sync,
{
	fn transactions(&self) -> Vec<(Hash, Vec<u8>)> {
		let best_block_id = match self.best_block_id() {
			Some(id) => id,
			None => return vec![],
		};
		self.pool.cull_and_get_pending(best_block_id, |pending| pending
			.map(|t| {
				let hash = t.hash().clone();
				(hash, t.primitive_extrinsic())
			})
			.collect()
		).unwrap_or_else(|e| {
			warn!("Error retrieving pending set: {}", e);
			vec![]
		})
	}

	fn import(&self, transaction: &Vec<u8>) -> Option<Hash> {
		if !self.imports_external_transactions {
			return None;
		}

		let encoded = transaction.encode();
		if let Some(uxt) = codec::Slicable::decode(&mut &encoded[..]) {
			let best_block_id = self.best_block_id()?;
			match self.pool.import_unchecked_extrinsic(best_block_id, uxt) {
				Ok(xt) => Some(*xt.hash()),
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

	fn on_broadcasted(&self, propagations: HashMap<Hash, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}
}
