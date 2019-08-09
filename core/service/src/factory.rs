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

use crate::{NewService, NetworkStatus, NetworkState, error::Error, DEFAULT_PROTOCOL_ID};
use crate::{SpawnTaskHandle, start_rpc_servers, build_network_future, components::maintain_transaction_pool};
use crate::{components, TransactionPoolAdapter};
use crate::config::{Configuration, Roles};
use client::{BlockchainEvents, Client, runtime_api};
use consensus_common::import_queue::ImportQueue;
use futures::{prelude::*, sync::mpsc};
use futures03::{StreamExt as _, TryStreamExt as _};
use keystore::Store as Keystore;
use log::{info, warn};
use network::{FinalityProofProvider, OnDemand, NetworkService, NetworkStateInfo};
use network::{config::BoxFinalityProofRequestBuilder, specialization::NetworkSpecialization};
use parking_lot::{Mutex, RwLock};
use primitives::{Blake2Hasher, H256, Hasher};
use sr_primitives::{BuildStorage, generic::BlockId};
use sr_primitives::traits::{Block as BlockT, ProvideRuntimeApi, Header, SaturatedConversion};
use substrate_executor::{NativeExecutor, NativeExecutionDispatch};
use serde::{Serialize, de::DeserializeOwned};
use std::{marker::PhantomData, sync::Arc};
use sysinfo::{get_current_pid, ProcessExt, System, SystemExt};
use tel::{telemetry, SUBSTRATE_INFO};
use transaction_pool::txpool::{ChainApi, Pool as TransactionPool};

/// Aggregator for the components required to build a service.
///
/// # Usage
///
/// Call [`ServiceBuilder::new_full`] or [`ServiceBuilder::new_light`], then call the various
/// `with_` methods to add the required components that you built yourself:
///
/// - [`with_select_chain`](ServiceBuilder::with_select_chain)
/// - [`with_import_queue`](ServiceBuilder::with_import_queue)
/// - [`with_network_protocol`](ServiceBuilder::with_network_protocol)
/// - [`with_finality_proof_provider`](ServiceBuilder::with_finality_proof_provider)
/// - [`with_transaction_pool`](ServiceBuilder::with_transaction_pool)
///
/// After this is done, call [`build`](ServiceBuilder::build) to construct the service.
///
/// The order in which the `with_*` methods are called doesn't matter, as the correct binding of
/// generics is done when you call `build`.
///
pub struct ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCl, TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool> {
	config: Configuration<TCfg, TGen>,
	client: Arc<TCl>,
	keystore: Arc<RwLock<Keystore>>,
	fetcher: Option<TFchr>,
	select_chain: Option<TSc>,
	import_queue: TImpQu,
	finality_proof_request_builder: Option<TFprb>,
	finality_proof_provider: Option<TFpp>,
	network_protocol: TNetP,
	transaction_pool: TExPool,
	marker: PhantomData<(TBl, TRtApi)>,
}

impl<TCfg, TGen> ServiceBuilder<(), (), TCfg, TGen, (), (), (), (), (), (), (), ()>
where TGen: Serialize + DeserializeOwned + BuildStorage {
	/// Start the service builder with a configuration.
	pub fn new_full<TBl: BlockT<Hash=H256>, TRtApi, TExecDisp: NativeExecutionDispatch>(
		config: Configuration<TCfg, TGen>
	) -> Result<ServiceBuilder<
		TBl,
		TRtApi,
		TCfg,
		TGen,
		Client<
			client_db::Backend<TBl>,
			client::LocalCallExecutor<client_db::Backend<TBl>, NativeExecutor<TExecDisp>>,
			TBl,
			TRtApi
		>,
		Arc<OnDemand<TBl>>,
		(),
		(),
		BoxFinalityProofRequestBuilder<TBl>,
		(),
		(),
		()
	>, Error> {
		let keystore = Keystore::open(config.keystore_path.clone(), config.keystore_password.clone())?;

		let db_settings = client_db::DatabaseSettings {
			cache_size: None,
			state_cache_size: config.state_cache_size,
			state_cache_child_ratio:
				config.state_cache_child_ratio.map(|v| (v, 100)),
			path: config.database_path.clone(),
			pruning: config.pruning.clone(),
		};

		let executor = NativeExecutor::<TExecDisp>::new(config.default_heap_pages);

		let client = Arc::new(client_db::new_client(
			db_settings,
			executor,
			&config.chain_spec,
			config.execution_strategies.clone(),
			Some(keystore.clone()),
		)?);

		Ok(ServiceBuilder {
			config,
			client,
			keystore,
			fetcher: None,
			select_chain: None,
			import_queue: (),
			finality_proof_request_builder: None,
			finality_proof_provider: None,
			network_protocol: (),
			transaction_pool: (),
			marker: PhantomData,
		})
	}

	/// Start the service builder with a configuration.
	pub fn new_light<TBl: BlockT<Hash=H256>, TRtApi, TExecDisp: NativeExecutionDispatch + 'static>(
		config: Configuration<TCfg, TGen>
	) -> Result<ServiceBuilder<
		TBl,
		TRtApi,
		TCfg,
		TGen,
		Client<
			client::light::backend::Backend<client_db::light::LightStorage<TBl>, network::OnDemand<TBl>, Blake2Hasher>,
			client::light::call_executor::RemoteOrLocalCallExecutor<
				TBl,
				client::light::backend::Backend<
					client_db::light::LightStorage<TBl>,
					network::OnDemand<TBl>,
					Blake2Hasher
				>,
				client::light::call_executor::RemoteCallExecutor<
					client::light::blockchain::Blockchain<
						client_db::light::LightStorage<TBl>,
						network::OnDemand<TBl>
					>,
					network::OnDemand<TBl>,
				>,
				client::LocalCallExecutor<
					client::light::backend::Backend<
						client_db::light::LightStorage<TBl>,
						network::OnDemand<TBl>,
						Blake2Hasher
					>,
					NativeExecutor<TExecDisp>
				>
			>,
			TBl,
			TRtApi
		>,
		Arc<OnDemand<TBl>>,
		(),
		(),
		BoxFinalityProofRequestBuilder<TBl>,
		(),
		(),
		()
	>, Error> {
		let keystore = Keystore::open(config.keystore_path.clone(), config.keystore_password.clone())?;

		let db_settings = client_db::DatabaseSettings {
			cache_size: config.database_cache_size.map(|u| u as usize),
			state_cache_size: config.state_cache_size,
			state_cache_child_ratio:
				config.state_cache_child_ratio.map(|v| (v, 100)),
			path: config.database_path.clone(),
			pruning: config.pruning.clone(),
		};

		let executor = NativeExecutor::<TExecDisp>::new(config.default_heap_pages);

		let db_storage = client_db::light::LightStorage::new(db_settings)?;
		let light_blockchain = client::light::new_light_blockchain(db_storage);
		let fetch_checker = Arc::new(client::light::new_fetch_checker(light_blockchain.clone(), executor.clone()));
		let fetcher = Arc::new(network::OnDemand::new(fetch_checker));
		let client_backend = client::light::new_light_backend(light_blockchain, fetcher.clone());
		let client = client::light::new_light(client_backend, fetcher.clone(), &config.chain_spec, executor)?;

		Ok(ServiceBuilder {
			config,
			client: Arc::new(client),
			keystore,
			fetcher: Some(fetcher),
			select_chain: None,
			import_queue: (),
			finality_proof_request_builder: None,
			finality_proof_provider: None,
			network_protocol: (),
			transaction_pool: (),
			marker: PhantomData,
		})
	}
}

impl<TBl, TRtApi, TCfg, TGen, TCl, TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool>
	ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCl, TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, TExPool> {

	/// Defines which head-of-chain strategy to use.
	pub fn with_opt_select_chain<USc>(
		mut self,
		select_chain_builder: impl FnOnce(&mut Configuration<TCfg, TGen>, Arc<TCl>) -> Result<Option<USc>, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCl, TFchr, USc, TImpQu, TFprb, TFpp, TNetP, TExPool>, Error> {
		let select_chain = select_chain_builder(&mut self.config, self.client.clone())?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			network_protocol: self.network_protocol,
			transaction_pool: self.transaction_pool,
			marker: self.marker,
		})
	}

	/// Defines which head-of-chain strategy to use.
	pub fn with_select_chain<USc>(
		self,
		builder: impl FnOnce(&mut Configuration<TCfg, TGen>, Arc<TCl>) -> Result<USc, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCl, TFchr, USc, TImpQu, TFprb, TFpp, TNetP, TExPool>, Error> {
		self.with_opt_select_chain(|cfg, cl| builder(cfg, cl).map(Option::Some))
	}

	/// Defines which import queue to use.
	pub fn with_import_queue<UImpQu>(
		mut self,
		builder: impl FnOnce(&mut Configuration<TCfg, TGen>, Arc<TCl>, Option<TSc>) -> Result<UImpQu, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCl, TFchr, TSc, UImpQu, TFprb, TFpp, TNetP, TExPool>, Error>
	where TSc: Clone {
		let import_queue = builder(&mut self.config, self.client.clone(), self.select_chain.clone())?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			network_protocol: self.network_protocol,
			transaction_pool: self.transaction_pool,
			marker: self.marker,
		})
	}

	/// Defines which network specialization protocol to use.
	pub fn with_network_protocol<UNetP>(
		self,
		network_protocol_builder: impl FnOnce(&Configuration<TCfg, TGen>) -> Result<UNetP, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCl, TFchr, TSc, TImpQu, TFprb, TFpp, UNetP, TExPool>, Error> {
		let network_protocol = network_protocol_builder(&self.config)?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			network_protocol,
			transaction_pool: self.transaction_pool,
			marker: self.marker,
		})
	}

	/// Defines which strategy to use for providing finality proofs.
	pub fn with_opt_finality_proof_provider(
		self,
		builder: impl FnOnce(Arc<TCl>) -> Result<Option<Arc<FinalityProofProvider<TBl>>>, Error>
	) -> Result<ServiceBuilder<
		TBl,
		TRtApi,
		TCfg,
		TGen,
		TCl,
		TFchr,
		TSc,
		TImpQu,
		TFprb,
		Arc<FinalityProofProvider<TBl>>,
		TNetP,
		TExPool
	>, Error> {
		let finality_proof_provider = builder(self.client.clone())?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider,
			network_protocol: self.network_protocol,
			transaction_pool: self.transaction_pool,
			marker: self.marker,
		})
	}

	/// Defines which strategy to use for providing finality proofs.
	pub fn with_finality_proof_provider(
		self,
		build: impl FnOnce(Arc<TCl>) -> Result<Arc<FinalityProofProvider<TBl>>, Error>
	) -> Result<ServiceBuilder<
		TBl,
		TRtApi,
		TCfg,
		TGen,
		TCl,
		TFchr,
		TSc,
		TImpQu,
		TFprb,
		Arc<FinalityProofProvider<TBl>>,
		TNetP,
		TExPool
	>, Error> {
		self.with_opt_finality_proof_provider(|client| build(client).map(Option::Some))
	}

	/// Defines which import queue to use.
	pub fn with_import_queue_and_opt_fprb<UImpQu, UFprb>(
		mut self,
		builder: impl FnOnce(&mut Configuration<TCfg, TGen>, Arc<TCl>, Option<TSc>)
			-> Result<(UImpQu, Option<UFprb>), Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCl, TFchr, TSc, UImpQu, UFprb, TFpp, TNetP, TExPool>, Error>
	where TSc: Clone {
		let (import_queue, fprb) = builder(&mut self.config, self.client.clone(), self.select_chain.clone())?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue,
			finality_proof_request_builder: fprb,
			finality_proof_provider: self.finality_proof_provider,
			network_protocol: self.network_protocol,
			transaction_pool: self.transaction_pool,
			marker: self.marker,
		})
	}

	/// Defines which import queue to use.
	pub fn with_import_queue_and_fprb<UImpQu, UFprb>(
		self,
		builder: impl FnOnce(&mut Configuration<TCfg, TGen>, Arc<TCl>, Option<TSc>) -> Result<(UImpQu, UFprb), Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCl, TFchr, TSc, UImpQu, UFprb, TFpp, TNetP, TExPool>, Error>
	where TSc: Clone {
		self.with_import_queue_and_opt_fprb(|cfg, cl, sc| builder(cfg, cl, sc).map(|(q, f)| (q, Some(f))))
	}

	/// Defines which transaction pool to use.
	pub fn with_transaction_pool<UExPool>(
		self,
		transaction_pool_builder: impl FnOnce(transaction_pool::txpool::Options, Arc<TCl>) -> Result<UExPool, Error>
	) -> Result<ServiceBuilder<TBl, TRtApi, TCfg, TGen, TCl, TFchr, TSc, TImpQu, TFprb, TFpp, TNetP, UExPool>, Error> {
		let transaction_pool = transaction_pool_builder(self.config.transaction_pool.clone(), self.client.clone())?;

		Ok(ServiceBuilder {
			config: self.config,
			client: self.client,
			keystore: self.keystore,
			fetcher: self.fetcher,
			select_chain: self.select_chain,
			import_queue: self.import_queue,
			finality_proof_request_builder: self.finality_proof_request_builder,
			finality_proof_provider: self.finality_proof_provider,
			network_protocol: self.network_protocol,
			transaction_pool,
			marker: self.marker,
		})
	}
}

impl<TBl, TRtApi, TCfg, TGen, TBackend, TExec, TSc, TImpQu, TNetP, TExPoolApi>
ServiceBuilder<
	TBl,
	TRtApi,
	TCfg,
	TGen,
	Client<TBackend, TExec, TBl, TRtApi>,
	Arc<OnDemand<TBl>>,
	TSc,
	TImpQu,
	BoxFinalityProofRequestBuilder<TBl>,
	Arc<FinalityProofProvider<TBl>>,
	TNetP,
	TransactionPool<TExPoolApi>
> where
	Client<TBackend, TExec, TBl, TRtApi>: ProvideRuntimeApi,
	<Client<TBackend, TExec, TBl, TRtApi> as ProvideRuntimeApi>::Api:
		runtime_api::Metadata<TBl> + offchain::OffchainWorkerApi<TBl> + runtime_api::TaggedTransactionQueue<TBl> + session::SessionKeys<TBl>,
	TBl: BlockT<Hash = <Blake2Hasher as Hasher>::Out>,
	TRtApi: 'static + Send + Sync,
	TCfg: Default,
	TGen: Serialize + DeserializeOwned + BuildStorage,
	TBackend: 'static + client::backend::Backend<TBl, Blake2Hasher> + Send,
	TExec: 'static + client::CallExecutor<TBl, Blake2Hasher> + Send + Sync + Clone,
	TSc: Clone,
	TImpQu: 'static + ImportQueue<TBl>,
	TNetP: NetworkSpecialization<TBl>,
	TExPoolApi: 'static + ChainApi<Block = TBl, Hash = <TBl as BlockT>::Hash>,
{
	/// Builds the service.
	pub fn build(self) -> Result<NewService<
		Configuration<TCfg, TGen>,
		TBl,
		Client<TBackend, TExec, TBl, TRtApi>,
		TSc,
		NetworkStatus<TBl>,
		NetworkService<TBl, TNetP, <TBl as BlockT>::Hash>,
		TransactionPool<TExPoolApi>,
		offchain::OffchainWorkers<
			Client<TBackend, TExec, TBl, TRtApi>,
			TBackend::OffchainStorage,
			TBl
		>,
	>, Error> {
		let mut config = self.config;
		session::generate_initial_session_keys(
			self.client.clone(),
			config.dev_key_seed.clone().map(|s| vec![s]).unwrap_or_default()
		)?;
		let (
			client,
			fetcher,
			keystore,
			select_chain,
			import_queue,
			finality_proof_request_builder,
			finality_proof_provider,
			network_protocol,
			transaction_pool
		) = (
			self.client,
			self.fetcher,
			self.keystore,
			self.select_chain,
			self.import_queue,
			self.finality_proof_request_builder,
			self.finality_proof_provider,
			self.network_protocol,
			self.transaction_pool
		);

		new_impl!(
			TBl,
			config,
			move |_| -> Result<_, Error> {
				Ok((
					client,
					fetcher,
					keystore,
					select_chain,
					import_queue,
					finality_proof_request_builder,
					finality_proof_provider,
					network_protocol,
					transaction_pool
				))
			},
			|h, c, tx| maintain_transaction_pool(h, c, tx),
			|n, o, p, ns, v| components::offchain_workers(n, o, p, ns, v),
			|c, ssb, si, te, tp, ks| components::start_rpc(c, ssb, si, te, tp, ks),
		)
	}
}
