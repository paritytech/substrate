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

//! Service implementation. Specialized wrapper over substrate service.

use std::sync::Arc;

use babe;
use client::{self, LongestChain};
use grandpa::{self, FinalityProofProvider as GrandpaFinalityProofProvider};
use node_executor;
use node_primitives::Block;
use node_runtime::{GenesisConfig, RuntimeApi};
use substrate_service::{
	AbstractService, ServiceBuilder, config::Configuration, error::{Error as ServiceError},
};
use transaction_pool::{self, txpool::{Pool as TransactionPool}};
use inherents::InherentDataProviders;
use network::construct_simple_protocol;

use substrate_service::{NewService, NetworkStatus};
use client::{Client, LocalCallExecutor};
use client_db::Backend;
use sr_primitives::traits::Block as BlockT;
use node_executor::NativeExecutor;
use network::NetworkService;
use offchain::OffchainWorkers;
use primitives::Blake2Hasher;

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
		type RpcExtension = jsonrpc_core::IoHandler<substrate_rpc::Metadata>;
		let mut import_setup = None;
		let inherent_data_providers = inherents::InherentDataProviders::new();

		let builder = substrate_service::ServiceBuilder::new_full::<
			node_primitives::Block, node_runtime::RuntimeApi, node_executor::Executor
		>($config)?
			.with_select_chain(|_config, backend| {
				Ok(client::LongestChain::new(backend.clone()))
			})?
			.with_transaction_pool(|config, client|
				Ok(transaction_pool::txpool::Pool::new(config, transaction_pool::FullChainApi::new(client)))
			)?
			.with_import_queue(|_config, client, mut select_chain, _transaction_pool| {
				let select_chain = select_chain.take()
					.ok_or_else(|| substrate_service::Error::SelectChainRequired)?;
				let (grandpa_block_import, grandpa_link) =
					grandpa::block_import::<_, _, _, node_runtime::RuntimeApi, _, _>(
						client.clone(), &*client, select_chain
					)?;
				let justification_import = grandpa_block_import.clone();

				let (block_import, babe_link) = babe::block_import(
					babe::Config::get_or_compute(&*client)?,
					grandpa_block_import,
					client.clone(),
					client.clone(),
				)?;

				let import_queue = babe::import_queue(
					babe_link.clone(),
					block_import.clone(),
					Some(Box::new(justification_import)),
					None,
					client.clone(),
					client,
					inherent_data_providers.clone(),
				)?;

				import_setup = Some((block_import, grandpa_link, babe_link));
				Ok(import_queue)
			})?
			.with_rpc_extensions(|client, pool| -> RpcExtension {
				node_rpc::create(client, pool)
			})?;

		(builder, import_setup, inherent_data_providers)
	}}
}

/// Creates a full service from the configuration.
///
/// We need to use a macro because the test suit doesn't work with an opaque service. It expects
/// concrete types instead.
macro_rules! new_full {
	($config:expr, $with_startup_data: expr) => {{
		use futures::sync::mpsc;
		use network::DhtEvent;

		let (
			is_authority,
			force_authoring,
			name,
			disable_grandpa
		) = (
			$config.roles.is_authority(),
			$config.force_authoring,
			$config.name.clone(),
			$config.disable_grandpa
		);

		let (builder, mut import_setup, inherent_data_providers) = new_full_start!($config);

		// Dht event channel from the network to the authority discovery module. Use bounded channel to ensure
		// back-pressure. Authority discovery is triggering one event per authority within the current authority set.
		// This estimates the authority set size to be somewhere below 10 000 thereby setting the channel buffer size to
		// 10 000.
		let (dht_event_tx, dht_event_rx) =
			mpsc::channel::<DhtEvent>(10000);

		let service = builder.with_network_protocol(|_| Ok(crate::service::NodeProtocol::new()))?
			.with_finality_proof_provider(|client, backend|
				Ok(Arc::new(grandpa::FinalityProofProvider::new(backend, client)) as _)
			)?
			.with_dht_event_tx(dht_event_tx)?
			.build()?;

		let (block_import, grandpa_link, babe_link) = import_setup.take()
				.expect("Link Half and Block Import are present for Full Services or setup failed before. qed");

		($with_startup_data)(&block_import, &babe_link);

		if is_authority {
			let proposer = substrate_basic_authorship::ProposerFactory {
				client: service.client(),
				transaction_pool: service.transaction_pool(),
			};

			let client = service.client();
			let select_chain = service.select_chain()
				.ok_or(substrate_service::Error::SelectChainRequired)?;

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
			service.spawn_essential_task(babe);

			let authority_discovery = authority_discovery::AuthorityDiscovery::new(
				service.client(),
				service.network(),
				dht_event_rx,
			);
			service.spawn_task(authority_discovery);
		}

		let config = grandpa::Config {
			// FIXME #1578 make this available through chainspec
			gossip_duration: std::time::Duration::from_millis(333),
			justification_period: 512,
			name: Some(name),
			keystore: Some(service.keystore()),
		};

		match (is_authority, disable_grandpa) {
			(false, false) => {
				// start the lightweight GRANDPA observer
				service.spawn_task(Box::new(grandpa::run_grandpa_observer(
					config,
					grandpa_link,
					service.network(),
					service.on_exit(),
				)?));
			},
			(true, false) => {
				// start the full GRANDPA voter
				let grandpa_config = grandpa::GrandpaParams {
					config: config,
					link: grandpa_link,
					network: service.network(),
					inherent_data_providers: inherent_data_providers.clone(),
					on_exit: service.on_exit(),
					telemetry_on_connect: Some(service.telemetry_on_connect_stream()),
				};
				service.spawn_task(Box::new(grandpa::run_grandpa_voter(grandpa_config)?));
			},
			(_, true) => {
				grandpa::setup_disabled_grandpa(
					service.client(),
					&inherent_data_providers,
					service.network(),
				)?;
			},
		}

		Ok((service, inherent_data_providers))
	}};
	($config:expr) => {{
		new_full!($config, |_, _| {})
	}}
}

#[allow(dead_code)]
type ConcreteBlock = node_primitives::Block;
#[allow(dead_code)]
type ConcreteClient =
	Client<
		Backend<ConcreteBlock>,
		LocalCallExecutor<Backend<ConcreteBlock>,
		NativeExecutor<node_executor::Executor>>,
		ConcreteBlock,
		node_runtime::RuntimeApi
	>;
#[allow(dead_code)]
type ConcreteBackend = Backend<ConcreteBlock>;

/// A specialized configuration object for setting up the node..
pub type NodeConfiguration<C> = Configuration<C, GenesisConfig, crate::chain_spec::Extensions>;

/// Builds a new service for a full client.
pub fn new_full<C: Send + Default + 'static>(config: NodeConfiguration<C>)
-> Result<
	NewService<
		ConcreteBlock,
		ConcreteClient,
		LongestChain<ConcreteBackend, ConcreteBlock>,
		NetworkStatus<ConcreteBlock>,
		NetworkService<ConcreteBlock, crate::service::NodeProtocol, <ConcreteBlock as BlockT>::Hash>,
		TransactionPool<transaction_pool::FullChainApi<ConcreteClient, ConcreteBlock>>,
		OffchainWorkers<
			ConcreteClient,
			<ConcreteBackend as client::backend::Backend<Block, Blake2Hasher>>::OffchainStorage,
			ConcreteBlock,
		>
	>,
	ServiceError,
>
{
	new_full!(config).map(|(service, _)| service)
}

/// Builds a new service for a light client.
pub fn new_light<C: Send + Default + 'static>(config: NodeConfiguration<C>)
-> Result<impl AbstractService, ServiceError> {
	type RpcExtension = jsonrpc_core::IoHandler<substrate_rpc::Metadata>;
	let inherent_data_providers = InherentDataProviders::new();

	let service = ServiceBuilder::new_light::<Block, RuntimeApi, node_executor::Executor>(config)?
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
				babe_link,
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
		.with_rpc_extensions(|client, pool| -> RpcExtension {
			node_rpc::create(client, pool)
		})?
		.build()?;

	Ok(service)
}

#[cfg(test)]
mod tests {
	use std::sync::Arc;
	use babe::CompatibleDigestItem;
	use consensus_common::{
		Environment, Proposer, BlockImportParams, BlockOrigin, ForkChoiceStrategy, BlockImport,
	};
	use node_primitives::{Block, DigestItem};
	use node_runtime::{BalancesCall, Call, UncheckedExtrinsic};
	use node_runtime::constants::{currency::CENTS, time::SLOT_DURATION};
	use codec::{Encode, Decode};
	use primitives::{
		crypto::Pair as CryptoPair,
		sr25519::Public as AddressPublic, H256,
	};
	use sr_primitives::{
		generic::{BlockId, Era, Digest, SignedPayload},
		traits::Block as BlockT,
		OpaqueExtrinsic,
	};
	use timestamp;
	use finality_tracker;
	use keyring::AccountKeyring;
	use substrate_service::{AbstractService, Roles};
	use crate::service::new_full;

	#[cfg(feature = "rhd")]
	fn test_sync() {
		use primitives::ed25519::Pair;

		use {service_test, Factory};
		use client::{BlockImportParams, BlockOrigin};

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
			BlockImportParams {
				origin: BlockOrigin::File,
				justification: Vec::new(),
				internal_justification: Vec::new(),
				finalized: true,
				body: Some(block.extrinsics),
				header: block.header,
				auxiliary: Vec::new(),
			}
		};
		let extrinsic_factory =
			|service: &SyncService<<Factory as service::ServiceFactory>::FullService>|
		{
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
		service_test::sync(
			chain_spec::integration_test_config(),
			|config| new_full(config),
			|mut config| {
				// light nodes are unsupported
				config.roles = Roles::FULL;
				new_full(config)
			},
			block_factory,
			extrinsic_factory,
		);
	}

	#[test]
	#[ignore]
	fn test_sync() {
		let keystore_path = tempfile::tempdir().expect("Creates keystore path");
		let keystore = keystore::Store::open(keystore_path.path(), None)
			.expect("Creates keystore");
		let alice = keystore.write().insert_ephemeral_from_seed::<babe::AuthorityPair>("//Alice")
			.expect("Creates authority pair");

		let chain_spec = crate::chain_spec::tests::integration_test_config_with_single_authority();

		// For the block factory
		let mut slot_num = 1u64;

		// For the extrinsics factory
		let bob = Arc::new(AccountKeyring::Bob.pair());
		let charlie = Arc::new(AccountKeyring::Charlie.pair());
		let mut index = 0;

		service_test::sync(
			chain_spec,
			|config| {
				let mut setup_handles = None;
				new_full!(config, |
					block_import: &babe::BabeBlockImport<_, _, Block, _, _, _>,
					babe_link: &babe::BabeLink<Block>,
				| {
					setup_handles = Some((block_import.clone(), babe_link.clone()));
				}).map(move |(node, x)| (node, (x, setup_handles.unwrap())))
			},
			|mut config| {
				// light nodes are unsupported
				config.roles = Roles::FULL;
				new_full(config)
			},
			|service, &mut (ref inherent_data_providers, (ref mut block_import, ref babe_link))| {
				let mut inherent_data = inherent_data_providers
					.create_inherent_data()
					.expect("Creates inherent data.");
				inherent_data.replace_data(finality_tracker::INHERENT_IDENTIFIER, &1u64);

				let parent_id = BlockId::number(service.client().info().chain.best_number);
				let parent_header = service.client().header(&parent_id).unwrap().unwrap();
				let mut proposer_factory = substrate_basic_authorship::ProposerFactory {
					client: service.client(),
					transaction_pool: service.transaction_pool(),
				};

				let mut digest = Digest::<H256>::default();

				// even though there's only one authority some slots might be empty,
				// so we must keep trying the next slots until we can claim one.
				let babe_pre_digest = loop {
					inherent_data.replace_data(timestamp::INHERENT_IDENTIFIER, &(slot_num * SLOT_DURATION));
					if let Some(babe_pre_digest) = babe::test_helpers::claim_slot(
						slot_num,
						&parent_header,
						&*service.client(),
						&keystore,
						&babe_link,
					) {
						break babe_pre_digest;
					}

					slot_num += 1;
				};

				digest.push(<DigestItem as CompatibleDigestItem>::babe_pre_digest(babe_pre_digest));

				let mut proposer = proposer_factory.init(&parent_header).unwrap();
				let new_block = futures03::executor::block_on(proposer.propose(
					inherent_data,
					digest,
					std::time::Duration::from_secs(1),
				)).expect("Error making test block");

				let (new_header, new_body) = new_block.deconstruct();
				let pre_hash = new_header.hash();
				// sign the pre-sealed hash of the block and then
				// add it to a digest item.
				let to_sign = pre_hash.encode();
				let signature = alice.sign(&to_sign[..]);
				let item = <DigestItem as CompatibleDigestItem>::babe_seal(
					signature.into(),
				);
				slot_num += 1;

				let params = BlockImportParams {
					origin: BlockOrigin::File,
					header: new_header,
					justification: None,
					post_digests: vec![item],
					body: Some(new_body),
					finalized: true,
					auxiliary: Vec::new(),
					fork_choice: ForkChoiceStrategy::LongestChain,
				};

				block_import.import_block(params, Default::default())
					.expect("error importing test block");
			},
			|service, _| {
				let amount = 5 * CENTS;
				let to = AddressPublic::from_raw(bob.public().0);
				let from = AddressPublic::from_raw(charlie.public().0);
				let genesis_hash = service.client().block_hash(0).unwrap().unwrap();
				let best_block_id = BlockId::number(service.client().info().chain.best_number);
				let version = service.client().runtime_version_at(&best_block_id).unwrap().spec_version;
				let signer = charlie.clone();

				let function = Call::Balances(BalancesCall::transfer(to.into(), amount));

				let check_version = system::CheckVersion::new();
				let check_genesis = system::CheckGenesis::new();
				let check_era = system::CheckEra::from(Era::Immortal);
				let check_nonce = system::CheckNonce::from(index);
				let check_weight = system::CheckWeight::new();
				let take_fees = balances::TakeFees::from(0);
				let extra = (
					check_version,
					check_genesis,
					check_era,
					check_nonce,
					check_weight,
					take_fees,
					Default::default(),
				);
				let raw_payload = SignedPayload::from_raw(
					function,
					extra,
					(version, genesis_hash, genesis_hash, (), (), (), ())
				);
				let signature = raw_payload.using_encoded(|payload|	{
					signer.sign(payload)
				});
				let (function, extra, _) = raw_payload.deconstruct();
				let xt = UncheckedExtrinsic::new_signed(
					function,
					from.into(),
					signature.into(),
					extra,
				).encode();
				let v: Vec<u8> = Decode::decode(&mut xt.as_slice()).unwrap();

				index += 1;
				OpaqueExtrinsic(v)
			},
		);
	}

	#[test]
	#[ignore]
	fn test_consensus() {
		service_test::consensus(
			crate::chain_spec::tests::integration_test_config_with_two_authorities(),
			|config| new_full(config),
			|mut config| {
				// light nodes are unsupported
				config.roles = Roles::FULL;
				new_full(config)
			},
			vec![
				"//Alice".into(),
				"//Bob".into(),
			],
		)
	}
}
