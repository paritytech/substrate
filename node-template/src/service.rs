//! Service and ServiceFactory implementation. Specialized wrapper over Substrate service.

#![warn(unused_extern_crates)]

use transaction_pool::{self, txpool::{Pool as TransactionPool}};
use node_template_runtime::{self, GenesisConfig, opaque::Block, WASM_BINARY};
use substrate_service::{
	Configuration, error::{Error as ServiceError}, AbstractService,
};
use basic_authorship::ProposerFactory;
use consensus::{import_queue, start_aura, SlotDuration};
use futures::prelude::*;
use substrate_client as client;
use inherents::InherentDataProviders;
use network::construct_simple_protocol;
use substrate_executor::native_executor_instance;
use aura_primitives::sr25519::AuthorityPair as AuraAuthorityPair;

pub use substrate_executor::NativeExecutor;
// Our native executor instance.
native_executor_instance!(
	pub Executor,
	node_template_runtime::api::dispatch,
	node_template_runtime::native_version,
	WASM_BINARY
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
			.with_select_chain(|_config, client| {
				#[allow(deprecated)]
				Ok(substrate_client::LongestChain::new(client.backend().clone()))
			})?
			.with_transaction_pool(|config, client|
				Ok(transaction_pool::txpool::Pool::new(config, transaction_pool::ChainApi::new(client)))
			)?
			.with_import_queue(|_config, client, _select_chain, transaction_pool| {
				Ok(consensus::import_queue::<_, _, aura_primitives::sr25519::AuthorityPair, _>(
					consensus::SlotDuration::get_or_compute(&*client)?,
					Box::new(client.clone()),
					None,
					None,
					client,
					inherent_data_providers.clone(),
					Some(transaction_pool),
				)?)
			})?;
		(builder, inherent_data_providers)
	}}
}

/// Builds a new service for a full client.
pub fn new_full<C: Send + Default + 'static>(config: Configuration<C, GenesisConfig>)
-> Result<impl AbstractService, ServiceError> {

	let (builder, inherent_data_providers) = new_full_start!(config);
	let service = builder
		.with_opt_finality_proof_provider(|_| Ok(None))?
		.with_network_protocol(|_| Ok(NodeProtocol::new()))?
		.build()?;

	if service.config().roles.is_authority() {
		let proposer = ProposerFactory {
			client: service.client(),
			transaction_pool: service.transaction_pool(),
		};
		let client = service.client();
		let select_chain = service.select_chain()
			.ok_or_else(|| ServiceError::SelectChainRequired)?;
		let aura = start_aura::<_, _, _, _, _, AuraAuthorityPair, _, _, _>(
			SlotDuration::get_or_compute(&*client)?,
			client.clone(),
			select_chain,
			client,
			proposer,
			service.network(),
			inherent_data_providers.clone(),
			service.config().force_authoring,
			Some(service.keystore()),
		)?;
		service.spawn_task(Box::new(aura.select(service.on_exit()).then(|_| Ok(()))));
	}

	Ok(service)
}

/// Builds a new service for a light client.
pub fn new_light<C: Send + Default + 'static>(config: Configuration<C, GenesisConfig>)
-> Result<impl AbstractService, ServiceError> {
	let inherent_data_providers = InherentDataProviders::new();
	Ok(substrate_service::ServiceBuilder::new_light::<
		node_template_runtime::opaque::Block, node_template_runtime::RuntimeApi, Executor
	>(config)?
		.with_select_chain(|_config, client| {
			#[allow(deprecated)]
			Ok(client::LongestChain::new(client.backend().clone()))
		})?
		.with_transaction_pool(|config, client|
			Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client)))
		)?
		.with_import_queue(|_config, client, _select_chain, transaction_pool| {
			Ok(import_queue::<_, _, aura_primitives::sr25519::AuthorityPair, _>(
				SlotDuration::get_or_compute(&*client)?,
				Box::new(client.clone()),
				None,
				None,
				client,
				inherent_data_providers.clone(),
				Some(transaction_pool)
			)?)
		})?
		.with_opt_finality_proof_provider(|_| Ok(None))?
		.with_network_protocol(|_| Ok(NodeProtocol::new()))?
		.build()?)
}
