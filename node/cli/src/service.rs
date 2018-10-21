// Copyright 2018 Parity Technologies (UK) Ltd.
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
use transaction_pool::{self, txpool::{Pool as TransactionPool}};
use node_primitives::Block;
use node_runtime::GenesisConfig;
use substrate_service::{
	FactoryFullConfiguration, LightComponents, FullComponents, FullBackend,
	FullClient, LightClient, LightBackend, FullExecutor, LightExecutor,
	Roles, TaskExecutor,
};
use node_executor;
use consensus::{import_queue, start_aura, Config as AuraConfig, AuraImportQueue};

const AURA_SLOT_DURATION: u64 = 6;

construct_simple_protocol! {
	/// Demo protocol attachment for substrate.
	pub struct NodeProtocol where Block = Block { }
}

construct_simple_service!(Service);

construct_service_factory! {
	struct Factory {
		Block = Block,
		NetworkProtocol = NodeProtocol { |config| Ok(NodeProtocol::new()) },
		RuntimeDispatch = node_executor::Executor,
		FullTransactionPoolApi = transaction_pool::ChainApi<FullBackend<Self>, FullExecutor<Self>, Block>
			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
		LightTransactionPoolApi = transaction_pool::ChainApi<LightBackend<Self>, LightExecutor<Self>, Block>
			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
		Genesis = GenesisConfig,
		Configuration = (),
		FullService = Service<FullComponents<Self>>
			{ |config: FactoryFullConfiguration<Self>, executor: TaskExecutor| {
				let is_auth = config.roles == Roles::AUTHORITY;
				Service::<FullComponents<Factory>>::new(config, executor.clone()).map(move |service|{
					if is_auth {
						if let Ok(Some(Ok(key))) = service.keystore().contents()
							.map(|keys| keys.get(0).map(|k| service.keystore().load(k, "")))
						{
							info!("Using authority key {}", key.public());
							let task = start_aura(
								AuraConfig {
									local_key:  Some(Arc::new(key)),
									slot_duration: AURA_SLOT_DURATION,
								},
								service.client(),
								service.proposer(),
								service.network(),
							);

							executor.spawn(task);
						}
					}

					service
				})
			}
		},
		LightService = Service<LightComponents<Self>>
			{ |config, executor| Service::<LightComponents<Factory>>::new(config, executor) },
		FullImportQueue = AuraImportQueue<Self::Block, FullClient<Self>>
			{ |config, client| Ok(import_queue(AuraConfig {
						local_key: None,
						slot_duration: 5
					}, client)) },
		LightImportQueue = AuraImportQueue<Self::Block, LightClient<Self>>
			{ |config, client| Ok(import_queue(AuraConfig {
						local_key: None,
						slot_duration: 5
					}, client)) },
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
		let offline = Arc::new(RwLock::new(OfflineTracker::new()));
		let dummy_runtime = ::tokio::runtime::Runtime::new().unwrap();
		let block_factory = |service: &<Factory as service::ServiceFactory>::FullService| {
			let block_id = BlockId::number(service.client().info().unwrap().chain.best_number);
			let parent_header = service.client().header(&block_id).unwrap().unwrap();
			let consensus_net = ConsensusNetwork::new(service.network(), service.client().clone());
			let proposer_factory = consensus::ProposerFactory {
				client: service.client().clone(),
				transaction_pool: service.transaction_pool().clone(),
				network: consensus_net,
				offline: offline.clone(),
				force_delay: 0,
				handle: dummy_runtime.executor(),
			};
			let (proposer, _, _) = proposer_factory.init(&parent_header, &validators, alice.clone()).unwrap();
			let block = proposer.propose().expect("Error making test block");
			ImportBlock {
				origin: BlockOrigin::File,
				external_justification: Vec::new(),
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
