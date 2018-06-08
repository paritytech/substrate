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
use client::{self, genesis, Client};
use client_db;
use codec::{self, Slicable};
use consensus;
use keystore::Store as Keystore;
use network;
use primitives;
use polkadot_api;
use polkadot_executor::Executor as LocalDispatch;
use polkadot_runtime::{GenesisConfig, BuildExternalities};
use primitives::block::{Id as BlockId, ExtrinsicHash, Header};
use state_machine;
use substrate_executor::NativeExecutor;
use transaction_pool::{self, TransactionPool};
use error;

/// Code executor.
pub type CodeExecutor = NativeExecutor<LocalDispatch>;

/// Polkadot service components.
pub trait Components {
	/// Client backend type.
	type Backend: 'static + client::backend::Backend;

	/// Polkadot API type.
	type Api: 'static + polkadot_api::PolkadotApi + Send + Sync;

	/// Code executor type.
	type Executor: 'static + client::CallExecutor + Send + Sync;

	/// Create client.
	fn build_client(&self, settings: client_db::DatabaseSettings, executor: CodeExecutor, genesis: GenesisBuilder)
		-> Result<(Arc<Client<Self::Backend, Self::Executor>>, Option<Arc<network::OnDemand<network::Service>>>), error::Error>;

	/// Create api.
	fn build_api(&self, client: Arc<Client<Self::Backend, Self::Executor>>) -> Arc<Self::Api>;

	/// Create network transaction pool adapter.
	fn build_network_tx_pool(&self, client: Arc<client::Client<Self::Backend, Self::Executor>>, api: Arc<Self::Api>, tx_pool: Arc<TransactionPool>)
		-> Arc<network::TransactionPool>;

	/// Create consensus service.
	fn build_consensus(&self, client: Arc<Client<Self::Backend, Self::Executor>>, network: Arc<network::Service>, tx_pool: Arc<TransactionPool>, keystore: &Keystore)
		-> Result<Option<consensus::Service>, error::Error>;
}

/// Genesis block builder.
pub struct GenesisBuilder {
	pub config: GenesisConfig,
}

impl client::GenesisBuilder for GenesisBuilder {
	fn build(self) -> (Header, Vec<(Vec<u8>, Vec<u8>)>) {
		let storage = self.config.build_externalities();
		let block = genesis::construct_genesis_block(&storage);
		(primitives::block::Header::decode(&mut block.header.encode().as_ref()).expect("to_vec() always gives a valid serialisation; qed"), storage.into_iter().collect())
	}
}

/// Components for full Polkadot service.
pub struct FullComponents {
	/// Is this a validator node?
	pub is_validator: bool,
}

impl Components for FullComponents {
	type Backend = client_db::Backend;
	type Api = Client<Self::Backend, Self::Executor>;
	type Executor = client::LocalCallExecutor<client_db::Backend, NativeExecutor<LocalDispatch>>;

	fn build_client(&self, db_settings: client_db::DatabaseSettings, executor: CodeExecutor, genesis: GenesisBuilder)
		-> Result<(Arc<client::Client<Self::Backend, Self::Executor>>, Option<Arc<network::OnDemand<network::Service>>>), error::Error> {
		let backend = client_db::new_backend(db_settings)?;
		Ok((Arc::new(client_db::new_client(backend, executor, genesis)?), None))
	}

	fn build_api(&self, client: Arc<client::Client<Self::Backend, Self::Executor>>) -> Arc<Self::Api> {
		client
	}

	fn build_network_tx_pool(&self, client: Arc<client::Client<Self::Backend, Self::Executor>>, api: Arc<Self::Api>, pool: Arc<TransactionPool>)
		-> Arc<network::TransactionPool> {
		Arc::new(TransactionPoolAdapter {
			imports_external_transactions: true,
			pool,
			client,
			api,
		})
	}

	fn build_consensus(&self, client: Arc<client::Client<Self::Backend, Self::Executor>>, network: Arc<network::Service>, tx_pool: Arc<TransactionPool>, keystore: &Keystore)
		-> Result<Option<consensus::Service>, error::Error> {
		if !self.is_validator {
			return Ok(None);
		}

		// Load the first available key
		let key = keystore.load(&keystore.contents()?[0], "")?;
		info!("Using authority key {:?}", key.public());
		Ok(Some(consensus::Service::new(
			client.clone(),
			client.clone(),
			network.clone(),
			tx_pool.clone(),
			::std::time::Duration::from_millis(4000), // TODO: dynamic
			key,
		)))
	}
}

/// Components for light Polkadot service.
pub struct LightComponents;

impl Components for LightComponents {
	type Backend = client::light::Backend<client_db::Backend, network::OnDemand<network::Service>>;
	type Api = polkadot_api::light::RemotePolkadotApiWrapper<Self::Backend, Self::Executor>;
	type Executor = client::RemoteCallExecutor<client::light::Blockchain<client_db::Backend, network::OnDemand<network::Service>>,
		network::OnDemand<network::Service>>;

	fn build_client(&self, db_settings: client_db::DatabaseSettings, executor: CodeExecutor, genesis: GenesisBuilder)
		-> Result<(Arc<client::Client<Self::Backend, Self::Executor>>, Option<Arc<network::OnDemand<network::Service>>>), error::Error> {
		let db_backend = client_db::new_backend(db_settings)?;
		let light_blockchain = client::light::new_light_blockchain(db_backend);
		let fetch_checker = Arc::new(client::light::new_fetch_checker(light_blockchain.clone(), executor));
		let fetcher = Arc::new(network::OnDemand::new(fetch_checker));
		let client_backend = client::light::new_light_backend(light_blockchain, fetcher.clone());
		let client = client::light::new_light(client_backend, fetcher.clone(), genesis)?;
		Ok((Arc::new(client), Some(fetcher)))
	}

	fn build_api(&self, client: Arc<client::Client<Self::Backend, Self::Executor>>) -> Arc<Self::Api> {
		Arc::new(polkadot_api::light::RemotePolkadotApiWrapper(client.clone()))
	}

	fn build_network_tx_pool(&self, client: Arc<client::Client<Self::Backend, Self::Executor>>, api: Arc<Self::Api>, pool: Arc<TransactionPool>)
		-> Arc<network::TransactionPool> {
		Arc::new(TransactionPoolAdapter {
			imports_external_transactions: false,
			pool,
			client,
			api,
		})
	}

	fn build_consensus(&self, _client: Arc<client::Client<Self::Backend, Self::Executor>>, _network: Arc<network::Service>, _tx_pool: Arc<TransactionPool>, _keystore: &Keystore)
		-> Result<Option<consensus::Service>, error::Error> {
		Ok(None)
	}
}

/// Transaction pool adapter.
pub struct TransactionPoolAdapter<B, E, A> where A: Send + Sync, E: Send + Sync {
	imports_external_transactions: bool,
	pool: Arc<TransactionPool>,
	client: Arc<Client<B, E>>,
	api: Arc<A>,
}

impl<B, E, A> network::TransactionPool for TransactionPoolAdapter<B, E, A>
	where
		B: client::backend::Backend + Send + Sync,
		E: client::CallExecutor + Send + Sync,
		client::error::Error: From<<<B as client::backend::Backend>::State as state_machine::backend::Backend>::Error>,
		A: polkadot_api::PolkadotApi + Send + Sync,
{
	fn transactions(&self) -> Vec<(ExtrinsicHash, Vec<u8>)> {
		let best_block = match self.client.info() {
			Ok(info) => info.chain.best_hash,
			Err(e) => {
				debug!("Error getting best block: {:?}", e);
				return Vec::new();
			}
		};

		let id = self.api.check_id(BlockId::Hash(best_block)).expect("Best block is always valid; qed.");
		let ready = transaction_pool::Ready::create(id, &*self.api);

		self.pool.cull_and_get_pending(ready, |pending| pending
			.map(|t| {
				let hash = ::primitives::Hash::from(&t.hash()[..]);
				let tx = codec::Slicable::encode(t.as_transaction());
				(hash, tx)
			})
			.collect()
		)
	}

	fn import(&self, transaction: &[u8]) -> Option<ExtrinsicHash> {
		if !self.imports_external_transactions {
			return None;
		}

		if let Some(uxt) = codec::Slicable::decode(&mut &transaction[..]) {
			match self.pool.import_unchecked_extrinsic(uxt) {
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

	fn on_broadcasted(&self, propagations: HashMap<ExtrinsicHash, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}
}
