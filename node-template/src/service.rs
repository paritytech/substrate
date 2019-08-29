//! Service and ServiceFactory implementation. Specialized wrapper over substrate service.

use std::sync::Arc;
use std::time::Duration;
use substrate_client::LongestChain;
use babe::{import_queue, start_babe, Config};
use grandpa::{self, FinalityProofProvider as GrandpaFinalityProofProvider};
use futures::prelude::*;
use node_template_runtime::{self, GenesisConfig, opaque::Block, RuntimeApi, WASM_BINARY};
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
	node_template_runtime::native_version
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
		let mut tasks_to_spawn = None;

		let builder = substrate_service::ServiceBuilder::new_full::<
			node_template_runtime::opaque::Block, node_template_runtime::RuntimeApi, crate::service::Executor
		>($config)?
			.with_select_chain(|_config, client| {
				#[allow(deprecated)]
				Ok(substrate_client::LongestChain::new(client.backend().clone()))
			})?
			.with_transaction_pool(|config, client|
				Ok(transaction_pool::txpool::Pool::new(config, transaction_pool::ChainApi::new(client)))
			)?
			.with_import_queue(|_config, client, mut select_chain, transaction_pool| {
				let select_chain = select_chain.take()
					.ok_or_else(|| substrate_service::Error::SelectChainRequired)?;
				let (block_import, link_half) =
					grandpa::block_import::<_, _, _, node_template_runtime::RuntimeApi, _, _>(
						client.clone(), client.clone(), select_chain
					)?;
				let justification_import = block_import.clone();

				let (import_queue, babe_link, babe_block_import, pruning_task) = babe::import_queue(
					babe::Config::get_or_compute(&*client)?,
					block_import,
					Some(Box::new(justification_import)),
					None,
					client.clone(),
					client,
					inherent_data_providers.clone(),
					Some(transaction_pool)
				)?;

				import_setup = Some((babe_block_import.clone(), link_half, babe_link));
				tasks_to_spawn = Some(vec![Box::new(pruning_task)]);

				Ok(import_queue)
			})?;

		(builder, import_setup, inherent_data_providers, tasks_to_spawn)
	}}
}

/// Builds a new service for a full client.
pub fn new_full<C: Send + Default + 'static>(config: Configuration<C, GenesisConfig>)
	-> Result<impl AbstractService, ServiceError>
{

	let (builder, mut import_setup, inherent_data_providers, mut tasks_to_spawn) = new_full_start!(config);

	let service = builder.with_network_protocol(|_| Ok(NodeProtocol::new()))?
		.with_finality_proof_provider(|client|
			Ok(Arc::new(GrandpaFinalityProofProvider::new(client.clone(), client)) as _)
		)?
		.build()?;

	let (block_import, link_half, babe_link) =
		import_setup.take()
			.expect("Link Half and Block Import are present for Full Services or setup failed before. qed");

	// spawn any futures that were created in the previous setup steps
	if let Some(tasks) = tasks_to_spawn.take() {
		for task in tasks {
			service.spawn_task(
				task.select(service.on_exit())
					.map(|_| ())
					.map_err(|_| ())
			);
		}
	}

	if service.config().roles.is_authority() {
		let proposer = basic_authorship::ProposerFactory {
			client: service.client(),
			transaction_pool: service.transaction_pool(),
		};

		let client = service.client();
		let select_chain = service.select_chain()
			.ok_or(ServiceError::SelectChainRequired)?;

		let babe_config = babe::BabeParams {
			config: Config::get_or_compute(&*client)?,
			keystore: service.keystore(),
			client,
			select_chain,
			block_import,
			env: proposer,
			sync_oracle: service.network(),
			inherent_data_providers: inherent_data_providers.clone(),
			force_authoring: service.config().force_authoring,
			time_source: babe_link,
		};

		let babe = start_babe(babe_config)?;
		let select = babe.select(service.on_exit()).then(|_| Ok(()));

		// the BABE authoring task is considered infallible, i.e. if it
		// fails we take down the service with it.
		service.spawn_essential_task(select);
	}

	let config = grandpa::Config {
		// FIXME #1578 make this available through chainspec
		gossip_duration: Duration::from_millis(333),
		justification_period: 4096,
		name: Some(service.config().name.clone()),
		keystore: Some(service.keystore()),
	};

	match (service.config().roles.is_authority(), service.config().disable_grandpa) {
		(false, false) => {
			// start the lightweight GRANDPA observer
			service.spawn_task(Box::new(grandpa::run_grandpa_observer(
				config,
				link_half,
				service.network(),
				service.on_exit(),
			)?));
		},
		(true, false) => {
			// start the full GRANDPA voter
			let grandpa_config = grandpa::GrandpaParams {
				config: config,
				link: link_half,
				network: service.network(),
				inherent_data_providers: inherent_data_providers.clone(),
				on_exit: service.on_exit(),
				telemetry_on_connect: Some(service.telemetry_on_connect_stream()),
			};

			// the GRANDPA voter task is considered infallible, i.e.
			// if it fails we take down the service with it.
			service.spawn_essential_task(grandpa::run_grandpa_voter(grandpa_config)?);
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
		.with_select_chain(|_config, client| {
			#[allow(deprecated)]
			Ok(LongestChain::new(client.backend().clone()))
		})?
		.with_transaction_pool(|config, client|
			Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client)))
		)?
		.with_import_queue_and_fprb(|_config, client, _select_chain, transaction_pool| {
			#[allow(deprecated)]
			let fetch_checker = client.backend().blockchain().fetcher()
				.upgrade()
				.map(|fetcher| fetcher.checker().clone())
				.ok_or_else(|| "Trying to start light import queue without active fetch checker")?;
			let block_import = grandpa::light_block_import::<_, _, _, RuntimeApi, _>(
				client.clone(), Arc::new(fetch_checker), client.clone()
			)?;

			let finality_proof_import = block_import.clone();
			let finality_proof_request_builder =
				finality_proof_import.create_finality_proof_request_builder();

			// FIXME: pruning task isn't started since light client doesn't do `AuthoritySetup`.
			let (import_queue, ..) = import_queue(
				Config::get_or_compute(&*client)?,
				block_import,
				None,
				Some(Box::new(finality_proof_import)),
				client.clone(),
				client,
				inherent_data_providers.clone(),
				Some(transaction_pool)
			)?;

			Ok((import_queue, finality_proof_request_builder))
		})?
		.with_network_protocol(|_| Ok(NodeProtocol::new()))?
		.with_finality_proof_provider(|client|
			Ok(Arc::new(GrandpaFinalityProofProvider::new(client.clone(), client)) as _)
		)?
		.build()
}
