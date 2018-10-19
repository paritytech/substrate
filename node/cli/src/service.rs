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
use node_network::Protocol as DemoProtocol;
use substrate_service::{
	FactoryFullConfiguration, LightComponents, FullComponents, FullBackend,
	LightBackend, FullExecutor, LightExecutor
};
use network::import_queue::{BasicQueue, BlockOrigin, ImportBlock, Verifier};
use runtime_primitives::{traits::Block as BlockT};
use primitives::AuthorityId;
use node_executor;

// TODO: Remove me, when we have a functional consensus.
/// A verifier that doesn't actually do any checks
pub struct NoneVerifier;
/// This Verifiyer accepts all data as valid
impl<B: BlockT> Verifier<B> for NoneVerifier {
	fn verify(
		&self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Vec<u8>,
		body: Option<Vec<B::Extrinsic>>
	) -> Result<(ImportBlock<B>, Option<Vec<AuthorityId>>), String> {
		Ok((ImportBlock {
			origin,
			header,
			body,
			finalized: true,
			external_justification: justification,
			internal_justification: vec![],
			auxiliary: Vec::new(),
		}, None))
	}
}

construct_simple_service!(Service);

construct_service_factory! {
	struct Factory {
		Block = Block,
		NetworkProtocol = DemoProtocol { |config| Ok(DemoProtocol::new()) },
		RuntimeDispatch = node_executor::Executor,
		FullTransactionPoolApi = transaction_pool::ChainApi<FullBackend<Self>, FullExecutor<Self>, Block>
			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
		LightTransactionPoolApi = transaction_pool::ChainApi<LightBackend<Self>, LightExecutor<Self>, Block>
			{ |config, client| Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client))) },
		Genesis = GenesisConfig,
		Configuration = (),
		FullService = Service<FullComponents<Self>>
			{ |config, executor| Service::<FullComponents<Factory>>::new(config, executor) },
		LightService = Service<LightComponents<Self>>
			{ |config, executor| Service::<LightComponents<Factory>>::new(config, executor) },
		ImportQueue = BasicQueue<Block, NoneVerifier>
			{ |_, _| Ok(BasicQueue::new(Arc::new(NoneVerifier {}))) }
			{ |_, _| Ok(BasicQueue::new(Arc::new(NoneVerifier {}))) },
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
