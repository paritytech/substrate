//! Service and ServiceFactory implementation. Specialized wrapper over substrate service.

use std::sync::Arc;
use std::time::Duration;
use sc_client::LongestChain;
use node_template_runtime::{self, GenesisConfig, opaque::Block, RuntimeApi};
use sc_service::{error::{Error as ServiceError}, AbstractService, Configuration, ServiceBuilder};
use sp_inherents::InherentDataProviders;
use sc_network::{construct_simple_protocol};
use sc_executor::native_executor_instance;
pub use sc_executor::NativeExecutor;
use sp_consensus_aura::sr25519::{AuthorityPair as AuraPair};
use grandpa::{self, FinalityProofProvider as GrandpaFinalityProofProvider};
use sc_basic_authority;

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
		let inherent_data_providers = sp_inherents::InherentDataProviders::new();

		let builder = sc_service::ServiceBuilder::new_full::<
			node_template_runtime::opaque::Block, node_template_runtime::RuntimeApi, crate::service::Executor
		>($config)?
			.with_select_chain(|_config, backend| {
				Ok(sc_client::LongestChain::new(backend.clone()))
			})?
			.with_transaction_pool(|config, client, _fetcher| {
				let pool_api = sc_transaction_pool::FullChainApi::new(client.clone());
				let pool = sc_transaction_pool::BasicPool::new(config, pool_api);
				let maintainer = sc_transaction_pool::FullBasicPoolMaintainer::new(pool.pool().clone(), client);
				let maintainable_pool = sp_transaction_pool::MaintainableTransactionPool::new(pool, maintainer);
				Ok(maintainable_pool)
			})?
			.with_import_queue(|_config, client, mut select_chain, transaction_pool| {
				let select_chain = select_chain.take()
					.ok_or_else(|| sc_service::Error::SelectChainRequired)?;

				let (grandpa_block_import, grandpa_link) =
					grandpa::block_import::<_, _, _, node_template_runtime::RuntimeApi, _>(
						client.clone(), &*client, select_chain
					)?;

				let aura_block_import = sc_consensus_aura::AuraBlockImport::<_, _, _, AuraPair>::new(
					grandpa_block_import.clone(), client.clone(),
				);

				let import_queue = sc_consensus_aura::import_queue::<_, _, _, AuraPair, _>(
					sc_consensus_aura::SlotDuration::get_or_compute(&*client)?,
					aura_block_import,
					Some(Box::new(grandpa_block_import.clone())),
					None,
					client,
					inherent_data_providers.clone(),
					Some(transaction_pool),
				)?;

				import_setup = Some((grandpa_block_import, grandpa_link));

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
	let force_authoring = config.force_authoring;
	let name = config.name.clone();
	let disable_grandpa = config.disable_grandpa;

	// sentry nodes announce themselves as authorities to the network
	// and should run the same protocols authorities do, but it should
	// never actively participate in any consensus process.
	let participates_in_consensus = is_authority && !config.sentry_mode;

	let (builder, mut import_setup, inherent_data_providers) = new_full_start!(config);

	let (block_import, grandpa_link) =
		import_setup.take()
			.expect("Link Half and Block Import are present for Full Services or setup failed before. qed");

	let service = builder.with_network_protocol(|_| Ok(NodeProtocol::new()))?
		.with_finality_proof_provider(|client, backend|
			Ok(Arc::new(GrandpaFinalityProofProvider::new(backend, client)) as _)
		)?
		.build()?;

	if participates_in_consensus {
		let proposer = sc_basic_authority::ProposerFactory {
			client: service.client(),
			transaction_pool: service.transaction_pool(),
		};

		let client = service.client();
		let select_chain = service.select_chain()
			.ok_or(ServiceError::SelectChainRequired)?;

		let can_author_with =
			sp_consensus::CanAuthorWithNativeVersion::new(client.executor().clone());

		let aura = sc_consensus_aura::start_aura::<_, _, _, _, _, AuraPair, _, _, _, _>(
			sc_consensus_aura::SlotDuration::get_or_compute(&*client)?,
			client,
			select_chain,
			block_import,
			proposer,
			service.network(),
			inherent_data_providers.clone(),
			force_authoring,
			service.keystore(),
			can_author_with,
		)?;

		// the AURA authoring task is considered essential, i.e. if it
		// fails we take down the service with it.
		service.spawn_essential_task(aura);
	}

	// if the node isn't actively participating in consensus then it doesn't
	// need a keystore, regardless of which protocol we use below.
	let keystore = if participates_in_consensus {
		Some(service.keystore())
	} else {
		None
	};

	let grandpa_config = grandpa::Config {
		// FIXME #1578 make this available through chainspec
		gossip_duration: Duration::from_millis(333),
		justification_period: 512,
		name: Some(name),
		observer_enabled: true,
		keystore,
		is_authority,
	};

	match (is_authority, disable_grandpa) {
		(false, false) => {
			// start the lightweight GRANDPA observer
			service.spawn_task(grandpa::run_grandpa_observer(
				grandpa_config,
				grandpa_link,
				service.network(),
				service.on_exit(),
				service.spawn_task_handle(),
			)?);
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
				voting_rule: grandpa::VotingRulesBuilder::default().build(),
				executor: service.spawn_task_handle(),
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
		.with_transaction_pool(|config, client, fetcher| {
			let fetcher = fetcher
				.ok_or_else(|| "Trying to start light transaction pool without active fetcher")?;
			let pool_api = sc_transaction_pool::LightChainApi::new(client.clone(), fetcher.clone());
			let pool = sc_transaction_pool::BasicPool::new(config, pool_api);
			let maintainer = sc_transaction_pool::LightBasicPoolMaintainer::with_defaults(pool.pool().clone(), client, fetcher);
			let maintainable_pool = sp_transaction_pool::MaintainableTransactionPool::new(pool, maintainer);
			Ok(maintainable_pool)
		})?
		.with_import_queue_and_fprb(|_config, client, backend, fetcher, _select_chain, _tx_pool| {
			let fetch_checker = fetcher
				.map(|fetcher| fetcher.checker().clone())
				.ok_or_else(|| "Trying to start light import queue without active fetch checker")?;
			let grandpa_block_import = grandpa::light_block_import::<_, _, _, RuntimeApi>(
				client.clone(), backend, &*client.clone(), Arc::new(fetch_checker),
			)?;
			let finality_proof_import = grandpa_block_import.clone();
			let finality_proof_request_builder =
				finality_proof_import.create_finality_proof_request_builder();

			let import_queue = sc_consensus_aura::import_queue::<_, _, _, AuraPair, ()>(
				sc_consensus_aura::SlotDuration::get_or_compute(&*client)?,
				grandpa_block_import,
				None,
				Some(Box::new(finality_proof_import)),
				client,
				inherent_data_providers.clone(),
				None,
			)?;

			Ok((import_queue, finality_proof_request_builder))
		})?
		.with_network_protocol(|_| Ok(NodeProtocol::new()))?
		.with_finality_proof_provider(|client, backend|
			Ok(Arc::new(GrandpaFinalityProofProvider::new(backend, client)) as _)
		)?
		.build()
}
