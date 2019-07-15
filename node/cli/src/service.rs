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

use aura::{import_queue, start_aura, AuraImportQueue, SlotDuration};
use client::{self, LongestChain};
use grandpa::{self, FinalityProofProvider as GrandpaFinalityProofProvider};
use node_executor;
use primitives::Pair;
use futures::prelude::*;
use node_primitives::{AuraPair, Block};
use node_runtime::{GenesisConfig, RuntimeApi};
use substrate_service::{
	FactoryFullConfiguration, LightComponents, FullComponents, FullBackend,
	FullClient, LightClient, LightBackend, FullExecutor, LightExecutor,
	error::{Error as ServiceError},
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

/// Node specific configuration
pub struct NodeConfig<F: substrate_service::ServiceFactory> {
	/// grandpa connection to import block
	// FIXME #1134 rather than putting this on the config, let's have an actual intermediate setup state
	pub grandpa_import_setup: Option<(grandpa::BlockImportForService<F>, grandpa::LinkHalfForService<F>)>,
	inherent_data_providers: InherentDataProviders,
}

impl<F> Default for NodeConfig<F> where F: substrate_service::ServiceFactory {
	fn default() -> NodeConfig<F> {
		NodeConfig {
			grandpa_import_setup: None,
			inherent_data_providers: InherentDataProviders::new(),
		}
	}
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
			{ |config: FactoryFullConfiguration<Self>|
				FullComponents::<Factory>::new(config) },
		AuthoritySetup = {
			|mut service: Self::FullService| {
				let (block_import, link_half) = service.config.custom.grandpa_import_setup.take()
					.expect("Link Half and Block Import are present for Full Services or setup failed before. qed");

				if let Some(aura_key) = service.authority_key::<AuraPair>() {
					info!("Using aura key {}", aura_key.public());

					let proposer = Arc::new(substrate_basic_authorship::ProposerFactory {
						client: service.client(),
						transaction_pool: service.transaction_pool(),
					});

					let client = service.client();
					let select_chain = service.select_chain()
						.ok_or(ServiceError::SelectChainRequired)?;

					let aura = start_aura(
						SlotDuration::get_or_compute(&*client)?,
						Arc::new(aura_key),
						client,
						select_chain,
						block_import,
						proposer,
						service.network(),
						service.config.custom.inherent_data_providers.clone(),
						service.config.force_authoring,
					)?;
					let select = aura.select(service.on_exit()).then(|_| Ok(()));
					service.spawn_task(Box::new(select));
				}

				let grandpa_key = if service.config.disable_grandpa {
					None
				} else {
					service.authority_key::<grandpa_primitives::AuthorityPair>()
				};

				let config = grandpa::Config {
					local_key: grandpa_key.map(Arc::new),
					// FIXME #1578 make this available through chainspec
					gossip_duration: Duration::from_millis(333),
					justification_period: 4096,
					name: Some(service.config.name.clone())
				};

				match config.local_key {
					None if !service.config.grandpa_voter => {
						service.spawn_task(Box::new(grandpa::run_grandpa_observer(
							config,
							link_half,
							service.network(),
							service.on_exit(),
						)?));
					},
					// Either config.local_key is set, or user forced voter service via `--grandpa-voter` flag.
					_ => {
						let telemetry_on_connect = TelemetryOnConnect {
							telemetry_connection_sinks: service.telemetry_on_connect_stream(),
						};
						let grandpa_config = grandpa::GrandpaParams {
							config: config,
							link: link_half,
							network: service.network(),
							inherent_data_providers: service.config.custom.inherent_data_providers.clone(),
							on_exit: service.on_exit(),
							telemetry_on_connect: Some(telemetry_on_connect),
						};
						service.spawn_task(Box::new(grandpa::run_grandpa_voter(grandpa_config)?));
					},
				}

				Ok(service)
			}
		},
		LightService = LightComponents<Self>
			{ |config| <LightComponents<Factory>>::new(config) },
		FullImportQueue = AuraImportQueue<Self::Block>
			{ |config: &mut FactoryFullConfiguration<Self> , client: Arc<FullClient<Self>>, select_chain: Self::SelectChain| {
				let slot_duration = SlotDuration::get_or_compute(&*client)?;
				let (block_import, link_half) =
					grandpa::block_import::<_, _, _, RuntimeApi, FullClient<Self>, _>(
						client.clone(), client.clone(), select_chain
					)?;
				let justification_import = block_import.clone();

				config.custom.grandpa_import_setup = Some((block_import.clone(), link_half));

				import_queue::<_, _, AuraPair>(
					slot_duration,
					Box::new(block_import),
					Some(Box::new(justification_import)),
					None,
					client,
					config.custom.inherent_data_providers.clone(),
				).map_err(Into::into)
			}},
		LightImportQueue = AuraImportQueue<Self::Block>
			{ |config: &FactoryFullConfiguration<Self>, client: Arc<LightClient<Self>>| {
				#[allow(deprecated)]
				let fetch_checker = client.backend().blockchain().fetcher()
					.upgrade()
					.map(|fetcher| fetcher.checker().clone())
					.ok_or_else(|| "Trying to start light import queue without active fetch checker")?;
				let block_import = grandpa::light_block_import::<_, _, _, RuntimeApi, LightClient<Self>>(
					client.clone(), Arc::new(fetch_checker), client.clone()
				)?;
				let finality_proof_import = block_import.clone();
				let finality_proof_request_builder = finality_proof_import.create_finality_proof_request_builder();

				import_queue::<_, _, AuraPair>(
					SlotDuration::get_or_compute(&*client)?,
					Box::new(block_import),
					None,
					Some(Box::new(finality_proof_import)),
					client,
					config.custom.inherent_data_providers.clone(),
				).map(|q| (q, finality_proof_request_builder)).map_err(Into::into)
			}},
		SelectChain = LongestChain<FullBackend<Self>, Self::Block>
			{ |config: &FactoryFullConfiguration<Self>, client: Arc<FullClient<Self>>| {
				#[allow(deprecated)]
				Ok(LongestChain::new(client.backend().clone()))
			}
		},
		FinalityProofProvider = { |client: Arc<FullClient<Self>>| {
			Ok(Some(Arc::new(GrandpaFinalityProofProvider::new(client.clone(), client)) as _))
		}},
	}
}


#[cfg(test)]
mod tests {
	use std::sync::Arc;
	use aura::CompatibleDigestItem;
	use consensus_common::{Environment, Proposer, ImportBlock, BlockOrigin, ForkChoiceStrategy};
	use node_primitives::DigestItem;
	use node_runtime::{BalancesCall, Call, CENTS, SECS_PER_BLOCK, UncheckedExtrinsic};
	use parity_codec::{Compact, Encode, Decode};
	use primitives::{
		crypto::Pair as CryptoPair, ed25519::Pair, blake2_256,
		sr25519::Public as AddressPublic, H256,
	};
	use sr_primitives::{generic::{BlockId, Era, Digest}, traits::Block, OpaqueExtrinsic};
	use timestamp;
	use finality_tracker;
	use keyring::{ed25519::Keyring as AuthorityKeyring, sr25519::Keyring as AccountKeyring};
	use substrate_service::ServiceFactory;
	use service_test::SyncService;
	use crate::service::Factory;

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
			let block_id = BlockId::number(service.client().info().chain.best_number);
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
		let extrinsic_factory = |service: &SyncService<<Factory as service::ServiceFactory>::FullService>| {
			let payload = (
				0,
				Call::Balances(BalancesCall::transfer(RawAddress::Id(bob.public().0.into()), 69.into())),
				Era::immortal(),
				service.client().genesis_hash()
			);
			let signature = alice.sign(&payload.encode()).into();
			let id = alice.public().0.into();
			let xt = UncheckedExtrinsic {
				signature: Some((RawAddress::Id(id), signature, payload.0, Era::immortal())),
				function: payload.1,
			}.encode();
			let v: Vec<u8> = Decode::decode(&mut xt.as_slice()).unwrap();
			OpaqueExtrinsic(v)
		};
		service_test::sync::<Factory, _, _>(
			chain_spec::integration_test_config(),
			block_factory,
			extrinsic_factory,
		);
	}

	#[test]
	#[ignore]
	fn test_sync() {
		let chain_spec = crate::chain_spec::tests::integration_test_config_with_single_authority();

		let alice = Arc::new(AuthorityKeyring::Alice.pair());
		let mut slot_num = 1u64;
		let block_factory = |service: &SyncService<<Factory as ServiceFactory>::FullService>| {
			let service = service.get();
			let mut inherent_data = service
				.config
				.custom
				.inherent_data_providers
				.create_inherent_data()
				.expect("Creates inherent data.");
			inherent_data.replace_data(finality_tracker::INHERENT_IDENTIFIER, &1u64);
			inherent_data.replace_data(timestamp::INHERENT_IDENTIFIER, &(slot_num * SECS_PER_BLOCK));

			let parent_id = BlockId::number(service.client().info().chain.best_number);
			let parent_header = service.client().header(&parent_id).unwrap().unwrap();
			let proposer_factory = Arc::new(substrate_basic_authorship::ProposerFactory {
				client: service.client(),
				transaction_pool: service.transaction_pool(),
			});

			let mut digest = Digest::<H256>::default();
			digest.push(<DigestItem as CompatibleDigestItem<Pair>>::aura_pre_digest(slot_num));
			let proposer = proposer_factory.init(&parent_header).unwrap();
			let new_block = proposer.propose(
				inherent_data,
				digest,
				std::time::Duration::from_secs(1),
			).expect("Error making test block");

			let (new_header, new_body) = new_block.deconstruct();
			let pre_hash = new_header.hash();
			// sign the pre-sealed hash of the block and then
			// add it to a digest item.
			let to_sign = pre_hash.encode();
			let signature = alice.sign(&to_sign[..]);
			let item = <DigestItem as CompatibleDigestItem<Pair>>::aura_seal(
				signature,
			);
			slot_num += 1;

			ImportBlock {
				origin: BlockOrigin::File,
				header: new_header,
				justification: None,
				post_digests: vec![item],
				body: Some(new_body),
				finalized: true,
				auxiliary: Vec::new(),
				fork_choice: ForkChoiceStrategy::LongestChain,
			}
		};

		let bob = Arc::new(AccountKeyring::Bob.pair());
		let charlie = Arc::new(AccountKeyring::Charlie.pair());

		let mut index = 0;
		let extrinsic_factory = |service: &SyncService<<Factory as ServiceFactory>::FullService>| {
			let amount = 5 * CENTS;
			let to = AddressPublic::from_raw(bob.public().0);
			let from = AddressPublic::from_raw(charlie.public().0);
			let genesis_hash = service.get().client().block_hash(0).unwrap().unwrap();
			let signer = charlie.clone();

			let function = Call::Balances(BalancesCall::transfer(to.into(), amount));
			let era = Era::immortal();
			let raw_payload = (Compact(index), function, era, genesis_hash);
			let signature = raw_payload.using_encoded(|payload| if payload.len() > 256 {
				signer.sign(&blake2_256(payload)[..])
			} else {
				signer.sign(payload)
			});
			let xt = UncheckedExtrinsic::new_signed(
				index,
				raw_payload.1,
				from.into(),
				signature.into(),
				era,
			).encode();
			let v: Vec<u8> = Decode::decode(&mut xt.as_slice()).unwrap();

			index += 1;
			OpaqueExtrinsic(v)
		};

		service_test::sync::<Factory, _, _>(
			chain_spec,
			block_factory,
			extrinsic_factory,
		);
	}

	#[test]
	#[ignore]
	fn test_consensus() {
		use super::Factory;

		service_test::consensus::<Factory>(
			crate::chain_spec::tests::integration_test_config_with_two_authorities(),
			vec![
				"//Alice".into(),
				"//Bob".into(),
			],
		)
	}
}
