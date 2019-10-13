//! Service and ServiceFactory implementation. Specialized wrapper over substrate service.

use substrate_client::LongestChain;
use futures::prelude::*;
use node_template_runtime::{self, GenesisConfig, opaque::Block, RuntimeApi};
use substrate_service::{error::{Error as ServiceError}, AbstractService, Configuration, ServiceBuilder};
use transaction_pool::{self, txpool::{Pool as TransactionPool}};
use inherents::InherentDataProviders;
use network::{construct_simple_protocol, config::DummyFinalityProofRequestBuilder};
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
			.with_import_queue(|_config, client, _select_chain, transaction_pool| {
				aura::import_queue::<_, _, aura_primitives::sr25519::AuthorityPair, _>(
					aura::SlotDuration::get_or_compute(&*client)?,
					Box::new(client.clone()),
					None,
					None,
					client,
					inherent_data_providers.clone(),
					Some(transaction_pool),
				).map_err(Into::into)
			})?;

		(builder, inherent_data_providers)
	}}
}

/// Builds a new service for a full client.
pub fn new_full<C: Send + Default + 'static>(config: Configuration<C, GenesisConfig>)
	-> Result<impl AbstractService, ServiceError>
{
	let is_authority = config.roles.is_authority();
	let force_authoring = config.force_authoring;

	let (builder, inherent_data_providers) = new_full_start!(config);

	let service = builder.with_network_protocol(|_| Ok(NodeProtocol::new()))?
		.with_opt_finality_proof_provider(|_, _| Ok(None))?
		.build()?;

	if is_authority {
		let proposer = basic_authorship::ProposerFactory {
			client: service.client(),
			transaction_pool: service.transaction_pool(),
		};

		let client = service.client();
		let select_chain = service.select_chain()
			.ok_or(ServiceError::SelectChainRequired)?;

		let aura = aura::start_aura::<_, _, _, _, _, aura_primitives::sr25519::AuthorityPair, _, _, _>(
			aura::SlotDuration::get_or_compute(&*client)?,
			client.clone(),
			select_chain,
			client,
			proposer,
			service.network(),
			inherent_data_providers.clone(),
			force_authoring,
			service.keystore(),
		)?;

		let select = aura.select(service.on_exit()).then(|_| Ok(()));

		// the AURA authoring task is considered essential, i.e. if it
		// fails we take down the service with it.
		service.spawn_essential_task(select);
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
		.with_import_queue_and_fprb(|_config, client, _backend, _fetcher, _select_chain, _tx_pool| {
			let finality_proof_request_builder = Box::new(DummyFinalityProofRequestBuilder::default()) as Box<_>;
			let import_queue = aura::import_queue::<_, _, AuraPair, ()>(
				aura::SlotDuration::get_or_compute(&*client)?,
				Box::new(client.clone()),
				None,
				None,
				client,
				inherent_data_providers.clone(),
				None,
			)?;

			Ok((import_queue, finality_proof_request_builder))
		})?
		.with_network_protocol(|_| Ok(NodeProtocol::new()))?
		.with_opt_finality_proof_provider(|_client, _backend|
			Ok(None)
		)?
		.build()
}
