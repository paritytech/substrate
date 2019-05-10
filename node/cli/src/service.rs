// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

#![warn(unused_extern_crates)]

//! Service and ServiceFactory implementation. Specialized wrapper over substrate service.

use std::sync::Arc;
use std::time::Duration;

use client;
use consensus::{import_queue, start_aura, AuraImportQueue, SlotDuration, NothingExtra};
use grandpa;
use node_executor;
use primitives::{Pair as PairT, ed25519};
use node_primitives::Block;
use node_runtime::{GenesisConfig, RuntimeApi};
use substrate_service::{
	FactoryFullConfiguration, LightComponents, FullComponents, FullBackend,
	FullClient, LightClient, LightBackend, FullExecutor, LightExecutor, TaskExecutor,
};
use transaction_pool::{self, txpool::{Pool as TransactionPool}};
use inherents::InherentDataProviders;
use network::construct_simple_protocol;
use substrate_service::construct_service_factory;
use log::info;
use substrate_service::TelemetryOnConnect;

construct_simple_protocol! {
	/// Demo protocol attachment for substrate.
	pub struct NodeProtocol where Block = Block { }
}

/// Intermediate Setup State
///
/// Background:
/// - The current components infrastructure decouples parts of the system. The node macro assembles many layers
/// of indirection in between, which are hard to penetrate. An intermediate setup state is required for all components,
/// including GRANDPA, to wire up properly. The interim solution that was used to provide this intermediate state was
/// inefficient, and involves storing `grandpa_import_setup` on `NodeConfig`.
///
/// Solution:
/// - Add a custom/generic intermediate state struct/type for "configuration" in the node-cli package's service setup for use
/// in the service setup.
/// - Set the default value of the "configuration" to be empty `()`.
/// - Allow the "configuration" state to be mutated (i.e. &mut) by each specific factory (i.e.
/// `construct_service_factory` to provide state so we may store/retrieve (i.e. the `LinkHalf`)
/// (instead of every specific implementation supplying it so it may be passed around to the service setup functions,
/// but without allowing it to be mutated or its latest state to be retrieved).
/// `LinkHalf` is a specific feature the GRANDPA consensus mechanism needs to pass from one setup stage to another
/// so they can be "linked up" properly. At the moment, we do that through a clone of what's stored in `NodeConfig`
/// but instead we want it designed to ensure that it is only ever being connected once.
/// - Pass around the "configuration" state to all setup functions that are called from the core-service package to
/// allow different systems that are setup to have direct access to a "configuration" state that they can rely on
/// and so they may communicate it amongst each other. This requires incorporating the "configuration" state into
/// `FullImportQueue` of the `construct_service_factory!` macro that's defined in node/cli/src/service.rs and
/// core/service/src/lib.rs.
/// - Allow the "configuration" state to be discarded after setup of the systems.
///
/// Glossary:
/// - `ImportQueue` is the object that receives blocks from the network and checks them.
/// - `LinkHalf` is provided when we create `ImportQueue`. It is the communication channel and the main object
/// we need to hold onto during setup as both the `ImportQueue` and `AuthoritySetup` are otherwise totally
/// disconnected from each other. In the specific consensus algorithm (GRANDPA) it informs the consensus making
/// engine about blocks it imported. GRANDPA needs access to `LinkHalf` that was created during `import_queue`
/// setup in order for the active consensus to run.
pub struct SetupState<F: substrate_service::ServiceFactory> {
	/// GRANDPA connection to import block
	///
	/// It may be filled by the `ImportQueue`
	grandpa_import_setup: &mut Option<(Arc<grandpa::BlockImportForService<F>>, grandpa::LinkHalfForService<F>)>,
}

impl<F> Default for SetupState<F> {
	fn default() -> SetupState<F> {
		SetupState {
			grandpa_import_setup: (),
		}
	}

	// // Set the configuration state, which includes discarding it after the systems are setup
	// fn set_setup(&mut self, mut setup) {
	// 	// TODO
	// }

	// /// Allow the configuration to be taken by `AuthoritySetup` using `take()`
	// fn get_setup(&mut self) -> Option<(Arc<grandpa::BlockImportForService<F>>, grandpa::LinkHalfForService<F>)> {
	// 	// FIXME
	// 	self.grandpa_import_setup.take()
	// }
}


/// Node specific configuration
///
/// Note that we can only use `[derive(Default)]` if all fields implement
/// Default themselves, however previously we were using `Option<Arc<...`,
/// which does not, so the derive macro would fail and we had to implement
/// the `Default` trait manually below.
///
/// Inherents may be attached by the runtime to blocks that are produced
///
/// References:
///   https://doc.rust-lang.org/std/default/trait.Default.html#derivable
///   https://doc.rust-lang.org/std/default/trait.Default.html
#[derive(Default)]
pub struct NodeConfig<F: substrate_service::ServiceFactory> {
	inherent_data_providers: InherentDataProviders::new,
}

construct_service_factory! {
	struct Factory {
		Block = Block,
		RuntimeApi = RuntimeApi,
		NetworkProtocol = NodeProtocol { |config| Ok(NodeProtocol::new()) },
		RuntimeDispatch = node_executor::Executor,
		FullTransactionPoolApi = transaction_pool::ChainApi<client::Client<FullBackend<Self>, FullExecutor<Self>, Block, RuntimeApi>, Block>
			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
		LightTransactionPoolApi = transaction_pool::ChainApi<client::Client<LightBackend<Self>, LightExecutor<Self>, Block, RuntimeApi>, Block>
			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
		Genesis = GenesisConfig,
		Configuration = NodeConfig<Self>,
		FullService = FullComponents<Self>
			{ |config: FactoryFullConfiguration<Self>, executor: TaskExecutor|
				FullComponents::<Factory>::new(config, executor) },
		AuthoritySetup = {
			|mut service: Self::FullService, executor: TaskExecutor, local_key: Option<Arc<ed25519::Pair>>| {
				let (block_import, link_half) = service.config.custom.grandpa_import_setup.take()
					.expect("Link Half and Block Import are present for Full Services or setup failed before. qed");

				if let Some(ref key) = local_key {
					info!("Using authority key {}", key.public());
					let proposer = Arc::new(substrate_basic_authorship::ProposerFactory {
						client: service.client(),
						transaction_pool: service.transaction_pool(),
						inherents_pool: service.inherents_pool(),
					});

					let client = service.client();
					executor.spawn(start_aura(
						SlotDuration::get_or_compute(&*client)?,
						key.clone(),
						client,
						block_import.clone(),
						proposer,
						service.network(),
						service.on_exit(),
						service.config.custom.inherent_data_providers.clone(),
						service.config.force_authoring,
					)?);

					info!("Running Grandpa session as Authority {}", key.public());
				}

				let local_key = if service.config.disable_grandpa {
					None
				} else {
					local_key
				};

				let config = grandpa::Config {
					local_key,
					// FIXME #1578 make this available through chainspec
					gossip_duration: Duration::from_millis(333),
					justification_period: 4096,
					name: Some(service.config.name.clone())
				};

				match config.local_key {
					None => {
						executor.spawn(grandpa::run_grandpa_observer(
							config,
							link_half,
							service.network(),
							service.on_exit(),
						)?);
					},
					Some(_) => {
						let telemetry_on_connect = TelemetryOnConnect {
						  on_exit: Box::new(service.on_exit()),
						  telemetry_connection_sinks: service.telemetry_on_connect_stream(),
						  executor: &executor,
						};
						let grandpa_config = grandpa::GrandpaParams {
						  config: config,
						  link: link_half,
						  network: service.network(),
						  inherent_data_providers: service.config.custom.inherent_data_providers.clone(),
						  on_exit: service.on_exit(),
						  telemetry_on_connect: Some(telemetry_on_connect),
						};
						executor.spawn(grandpa::run_grandpa_voter(grandpa_config)?);
					},
				}

				Ok(service)
			}
		},
		LightService = LightComponents<Self>
			{ |config, executor| <LightComponents<Factory>>::new(config, executor) },
		FullImportQueue = AuraImportQueue<Self::Block>
			{ |config: &mut FactoryFullConfiguration<Self> , client: Arc<FullClient<Self>>| {
				let slot_duration = SlotDuration::get_or_compute(&*client)?;
				let (block_import, link_half) =
					grandpa::block_import::<_, _, _, RuntimeApi, FullClient<Self>>(
						client.clone(), client.clone()
					)?;
				let block_import = Arc::new(block_import);
				let justification_import = block_import.clone();

				config.custom.grandpa_import_setup = Some((block_import.clone(), link_half));

				import_queue::<_, _, _, ed25519::Pair>(
					slot_duration,
					block_import,
					Some(justification_import),
					client,
					NothingExtra,
					config.custom.inherent_data_providers.clone(),
				).map_err(Into::into)
			}},
		LightImportQueue = AuraImportQueue<Self::Block>
			{ |config: &FactoryFullConfiguration<Self>, client: Arc<LightClient<Self>>| {
				import_queue::<_, _, _, ed25519::Pair>(
					SlotDuration::get_or_compute(&*client)?,
					client.clone(),
					None,
					client,
					NothingExtra,
					config.custom.inherent_data_providers.clone(),
				).map_err(Into::into)
			}
		},
	}
}


#[cfg(test)]
mod tests {
	#[cfg(feature = "rhd")]
	fn test_sync() {
		use {service_test, Factory};
		use client::{ImportBlock, BlockOrigin};

		let alice: Arc<ed25519::Pair> = Arc::new(Keyring::Alice.into());
		let bob: Arc<ed25519::Pair> = Arc::new(Keyring::Bob.into());
		let validators = vec![alice.public().0.into(), bob.public().0.into()];
		let keys: Vec<&ed25519::Pair> = vec![&*alice, &*bob];
		let dummy_runtime = ::tokio::runtime::Runtime::new().unwrap();
		let block_factory = |service: &<Factory as service::ServiceFactory>::FullService| {
			let block_id = BlockId::number(service.client().info().unwrap().chain.best_number);
			let parent_header = service.client().header(&block_id).unwrap().unwrap();
			let consensus_net = ConsensusNetwork::new(service.network(), service.client().clone());
			let proposer_factory = consensus::ProposerFactory {
				client: service.client().clone(),
				transaction_pool: service.transaction_pool().clone(),
				network: consensus_net,
				force_delay: 0,
				handle: dummy_runtime.executor(),
			};
			let (proposer, _, _) = proposer_factory.init(&parent_header, &validators, alice.clone()).unwrap();
			let block = proposer.propose().expect("Error making test block");
			ImportBlock {
				origin: BlockOrigin::File,
				justification: Vec::new(),
				internal_justification: Vec::new(),
				finalized: true,
				body: Some(block.extrinsics),
				header: block.header,
				auxiliary: Vec::new(),
			}
		};
		let extrinsic_factory = |service: &<Factory as service::ServiceFactory>::FullService| {
			let payload = (0, Call::Balances(BalancesCall::transfer(RawAddress::Id(bob.public().0.into()), 69.into())), Era::immortal(), service.client().genesis_hash());
			let signature = alice.sign(&payload.encode()).into();
			let id = alice.public().0.into();
			let xt = UncheckedExtrinsic {
				signature: Some((RawAddress::Id(id), signature, payload.0, Era::immortal())),
				function: payload.1,
			}.encode();
			let v: Vec<u8> = Decode::decode(&mut xt.as_slice()).unwrap();
			OpaqueExtrinsic(v)
		};
		service_test::sync::<Factory, _, _>(chain_spec::integration_test_config(), block_factory, extrinsic_factory);
	}

}
