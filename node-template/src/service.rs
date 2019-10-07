//! Service and ServiceFactory implementation. Specialized wrapper over substrate service.

use std::sync::Arc;
use std::time::Duration;
use substrate_client::LongestChain;
use babe;
use grandpa::{self, FinalityProofProvider as GrandpaFinalityProofProvider};
use futures::prelude::*;
use node_template_runtime::{self, GenesisConfig, opaque::Block, RuntimeApi};
use substrate_service::{error::{Error as ServiceError}, AbstractService, Configuration, ServiceBuilder};
use transaction_pool::{self, txpool::{Pool as TransactionPool}};
use inherents::InherentDataProviders;
use network::construct_simple_protocol;
use substrate_executor::native_executor_instance;
pub use substrate_executor::NativeExecutor;

// Our native executor instance.
native_executor_instance!(
	pub Executor,
	node_template_runtime::api::dispatch,
	node_template_runtime::native_version,
);

construct_simple_protocol! {
	/// Demo protocol attachment for substrate.
	pub struct NodeProtocol where Block = Block { }
}

/// Starts a `ServiceBuilder` for a full service.
///
/// Use this macro if you don't actually need the full service, but just the builder in order to
/// be able to perform chain operations.
macro_rules! new_full_start {
	($config:expr) => {{
		let mut import_setup = None;
		let inherent_data_providers = inherents::InherentDataProviders::new();

		let builder = substrate_service::ServiceBuilder::new_full::<
			node_template_runtime::opaque::Block, node_template_runtime::RuntimeApi, crate::service::Executor
		>($config)?
			.with_select_chain(|_config, backend| {
				Ok(substrate_client::LongestChain::new(backend.clone()))
			})?
			.with_transaction_pool(|config, client|
				Ok(transaction_pool::txpool::Pool::new(config, transaction_pool::FullChainApi::new(client)))
			)?
			.with_import_queue(|_config, client, mut select_chain, _transaction_pool| {
				let select_chain = select_chain.take()
					.ok_or_else(|| substrate_service::Error::SelectChainRequired)?;
				let (grandpa_block_import, grandpa_link) =
					grandpa::block_import::<_, _, _, node_template_runtime::RuntimeApi, _, _>(
						client.clone(), &*client, select_chain
					)?;
				let justification_import = grandpa_block_import.clone();

				let (babe_block_import, babe_link) = babe::block_import(
					babe::Config::get_or_compute(&*client)?,
					grandpa_block_import,
					client.clone(),
					client.clone(),
				)?;

				let import_queue = babe::import_queue(
					babe_link.clone(),
					babe_block_import.clone(),
					Some(Box::new(justification_import)),
					None,
					client.clone(),
					client,
					inherent_data_providers.clone(),
				)?;

				import_setup = Some((babe_block_import, grandpa_link, babe_link));

				Ok(import_queue)
			})?;

		(builder, import_setup, inherent_data_providers)
	}}
}

/// Builds a new service for a full client.
pub fn new_full<C: Send + Default + 'static>(config: Configuration<C, GenesisConfig>)
	-> Result<impl AbstractService, ServiceError>
{

	let is_authority = config.roles.is_authority();
	let name = config.name.clone();
	let disable_grandpa = config.disable_grandpa;
	let force_authoring = config.force_authoring;

	let (builder, mut import_setup, inherent_data_providers) = new_full_start!(config);

	let service = builder.with_network_protocol(|_| Ok(NodeProtocol::new()))?
		.with_finality_proof_provider(|client, backend|
			Ok(Arc::new(GrandpaFinalityProofProvider::new(backend, client)) as _)
		)?
		.build()?;

	let (block_import, grandpa_link, babe_link) =
		import_setup.take()
			.expect("Link Half and Block Import are present for Full Services or setup failed before. qed");

	if is_authority {
		let proposer = basic_authorship::ProposerFactory {
			client: service.client(),
			transaction_pool: service.transaction_pool(),
		};

		let client = service.client();
		let select_chain = service.select_chain()
			.ok_or(ServiceError::SelectChainRequired)?;

		let babe_config = babe::BabeParams {
			keystore: service.keystore(),
			client,
			select_chain,
			env: proposer,
			block_import,
			sync_oracle: service.network(),
			inherent_data_providers: inherent_data_providers.clone(),
			force_authoring,
			babe_link,
		};

		let babe = babe::start_babe(babe_config)?;
		let select = babe.select(service.on_exit()).then(|_| Ok(()));

		// the BABE authoring task is considered infallible, i.e. if it
		// fails we take down the service with it.
		service.spawn_essential_task(select);
	}

	let grandpa_config = grandpa::Config {
		// FIXME #1578 make this available through chainspec
		gossip_duration: Duration::from_millis(333),
		justification_period: 512,
		name: Some(name),
		keystore: Some(service.keystore()),
	};

	match (is_authority, disable_grandpa) {
		(false, false) => {
			// start the lightweight GRANDPA observer
			service.spawn_task(Box::new(grandpa::run_grandpa_observer(
				grandpa_config,
				grandpa_link,
				service.network(),
				service.on_exit(),
			)?));
		},
		(true, false) => {
			// start the full GRANDPA voter
			let voter_config = grandpa::GrandpaParams {
				config: grandpa_config,
				link: grandpa_link,
				network: service.network(),
				inherent_data_providers: inherent_data_providers.clone(),
				on_exit: service.on_exit(),
				telemetry_on_connect: Some(service.telemetry_on_connect_stream()),
			};

			// the GRANDPA voter task is considered infallible, i.e.
			// if it fails we take down the service with it.
			service.spawn_essential_task(grandpa::run_grandpa_voter(voter_config)?);
		},
		(_, true) => {
			grandpa::setup_disabled_grandpa(
				service.client(),
				&inherent_data_providers,
				service.network(),
			)?;
		},
	}

	Ok(service)
}

/// Builds a new service for a light client.
pub fn new_light<C: Send + Default + 'static>(config: Configuration<C, GenesisConfig>)
	-> Result<impl AbstractService, ServiceError>
{
	let inherent_data_providers = InherentDataProviders::new();

	ServiceBuilder::new_light::<Block, RuntimeApi, Executor>(config)?
		.with_select_chain(|_config, backend| {
			Ok(LongestChain::new(backend.clone()))
		})?
		.with_transaction_pool(|config, client|
			Ok(TransactionPool::new(config, transaction_pool::FullChainApi::new(client)))
		)?
		.with_import_queue_and_fprb(|_config, client, backend, fetcher, _select_chain, _tx_pool| {
			let fetch_checker = fetcher
				.map(|fetcher| fetcher.checker().clone())
				.ok_or_else(|| "Trying to start light import queue without active fetch checker")?;
			let grandpa_block_import = grandpa::light_block_import::<_, _, _, RuntimeApi, _>(
				client.clone(), backend, Arc::new(fetch_checker), client.clone()
			)?;

			let finality_proof_import = grandpa_block_import.clone();
			let finality_proof_request_builder =
				finality_proof_import.create_finality_proof_request_builder();

			let (babe_block_import, babe_link) = babe::block_import(
				babe::Config::get_or_compute(&*client)?,
				grandpa_block_import,
				client.clone(),
				client.clone(),
			)?;

			let import_queue = babe::import_queue(
				babe_link.clone(),
				babe_block_import,
				None,
				Some(Box::new(finality_proof_import)),
				client.clone(),
				client,
				inherent_data_providers.clone(),
			)?;

			Ok((import_queue, finality_proof_request_builder))
		})?
		.with_network_protocol(|_| Ok(NodeProtocol::new()))?
		.with_finality_proof_provider(|client, backend|
			Ok(Arc::new(GrandpaFinalityProofProvider::new(backend, client)) as _)
		)?
		.build()
}
