// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use sc_consensus_babe;
use sc_client::{self, LongestChain};
use grandpa::{self, FinalityProofProvider as GrandpaFinalityProofProvider};
use node_executor;
use node_primitives::Block;
use node_runtime::{GenesisConfig, RuntimeApi};
use sc_service::{
	AbstractService, ServiceBuilder, config::Configuration, error::{Error as ServiceError},
};
use sp_inherents::InherentDataProviders;

use sc_service::{Service, NetworkStatus};
use sc_client::{Client, LocalCallExecutor};
use sc_client_db::Backend;
use sp_runtime::traits::Block as BlockT;
use node_executor::NativeExecutor;
use sc_network::NetworkService;
use sc_offchain::OffchainWorkers;

/// Starts a `ServiceBuilder` for a full service.
///
/// Use this macro if you don't actually need the full service, but just the builder in order to
/// be able to perform chain operations.
macro_rules! new_full_start {
	($config:expr) => {{
		type RpcExtension = jsonrpc_core::IoHandler<sc_rpc::Metadata>;
		let mut import_setup = None;
		let inherent_data_providers = sp_inherents::InherentDataProviders::new();

		let builder = sc_service::ServiceBuilder::new_full::<
			node_primitives::Block, node_runtime::RuntimeApi, node_executor::Executor
		>($config)?
			.with_select_chain(|_config, backend| {
				Ok(sc_client::LongestChain::new(backend.clone()))
			})?
			.with_transaction_pool(|config, client, _fetcher| {
				let pool_api = sc_transaction_pool::FullChainApi::new(client.clone());
				Ok(sc_transaction_pool::BasicPool::new(config, std::sync::Arc::new(pool_api)))
			})?
			.with_import_queue(|_config, client, mut select_chain, _transaction_pool| {
				let select_chain = select_chain.take()
					.ok_or_else(|| sc_service::Error::SelectChainRequired)?;
				let (grandpa_block_import, grandpa_link) = grandpa::block_import(
					client.clone(),
					&*client,
					select_chain,
				)?;
				let justification_import = grandpa_block_import.clone();

				let (block_import, babe_link) = sc_consensus_babe::block_import(
					sc_consensus_babe::Config::get_or_compute(&*client)?,
					grandpa_block_import,
					client.clone(),
				)?;

				let import_queue = sc_consensus_babe::import_queue(
					babe_link.clone(),
					block_import.clone(),
					Some(Box::new(justification_import)),
					None,
					client,
					inherent_data_providers.clone(),
				)?;

				import_setup = Some((block_import, grandpa_link, babe_link));
				Ok(import_queue)
			})?
			.with_rpc_extensions(|builder| -> Result<RpcExtension, _> {
				let babe_link = import_setup.as_ref().map(|s| &s.2)
					.expect("BabeLink is present for full services or set up failed; qed.");
				let deps = node_rpc::FullDeps {
					client: builder.client().clone(),
					pool: builder.pool(),
					select_chain: builder.select_chain().cloned()
						.expect("SelectChain is present for full services or set up failed; qed."),
					babe: node_rpc::BabeDeps {
						keystore: builder.keystore(),
						babe_config: sc_consensus_babe::BabeLink::config(babe_link).clone(),
						shared_epoch_changes: sc_consensus_babe::BabeLink::epoch_changes(babe_link).clone()
					}
				};
				Ok(node_rpc::create_full(deps))
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
		use futures::prelude::*;
		use sc_network::Event;

		let (
			is_authority,
			force_authoring,
			name,
			disable_grandpa,
			sentry_nodes,
		) = (
			$config.roles.is_authority(),
			$config.force_authoring,
			$config.name.clone(),
			$config.disable_grandpa,
			$config.network.sentry_nodes.clone(),
		);

		// sentry nodes announce themselves as authorities to the network
		// and should run the same protocols authorities do, but it should
		// never actively participate in any consensus process.
		let participates_in_consensus = is_authority && !$config.sentry_mode;

		let (builder, mut import_setup, inherent_data_providers) = new_full_start!($config);

		let service = builder
			.with_finality_proof_provider(|client, backend|
				Ok(Arc::new(grandpa::FinalityProofProvider::new(backend, client)) as _)
			)?
			.build()?;

		let (block_import, grandpa_link, babe_link) = import_setup.take()
				.expect("Link Half and Block Import are present for Full Services or setup failed before. qed");

		($with_startup_data)(&block_import, &babe_link);

		if participates_in_consensus {
			let proposer = sc_basic_authorship::ProposerFactory {
				client: service.client(),
				transaction_pool: service.transaction_pool(),
			};

			let client = service.client();
			let select_chain = service.select_chain()
				.ok_or(sc_service::Error::SelectChainRequired)?;

			let can_author_with =
				sp_consensus::CanAuthorWithNativeVersion::new(client.executor().clone());

			let babe_config = sc_consensus_babe::BabeParams {
				keystore: service.keystore(),
				client,
				select_chain,
				env: proposer,
				block_import,
				sync_oracle: service.network(),
				inherent_data_providers: inherent_data_providers.clone(),
				force_authoring,
				babe_link,
				can_author_with,
			};

			let babe = sc_consensus_babe::start_babe(babe_config)?;
			service.spawn_essential_task("babe-proposer", babe);

			let network = service.network();
			let dht_event_stream = network.event_stream().filter_map(|e| async move { match e {
				Event::Dht(e) => Some(e),
				_ => None,
			}}).boxed();
			let authority_discovery = sc_authority_discovery::AuthorityDiscovery::new(
				service.client(),
				network,
				sentry_nodes,
				service.keystore(),
				dht_event_stream,
			);

			service.spawn_task("authority-discovery", authority_discovery);
		}

		// if the node isn't actively participating in consensus then it doesn't
		// need a keystore, regardless of which protocol we use below.
		let keystore = if participates_in_consensus {
			Some(service.keystore())
		} else {
			None
		};

		let config = grandpa::Config {
			// FIXME #1578 make this available through chainspec
			gossip_duration: std::time::Duration::from_millis(333),
			justification_period: 512,
			name: Some(name),
			observer_enabled: false,
			keystore,
			is_authority,
		};

		let enable_grandpa = !disable_grandpa;
		if enable_grandpa {
			// start the full GRANDPA voter
			// NOTE: non-authorities could run the GRANDPA observer protocol, but at
			// this point the full voter should provide better guarantees of block
			// and vote data availability than the observer. The observer has not
			// been tested extensively yet and having most nodes in a network run it
			// could lead to finality stalls.
			let grandpa_config = grandpa::GrandpaParams {
				config,
				link: grandpa_link,
				network: service.network(),
				inherent_data_providers: inherent_data_providers.clone(),
				on_exit: service.on_exit(),
				telemetry_on_connect: Some(service.telemetry_on_connect_stream()),
				voting_rule: grandpa::VotingRulesBuilder::default().build(),
			};

			// the GRANDPA voter task is considered infallible, i.e.
			// if it fails we take down the service with it.
			service.spawn_essential_task(
				"grandpa-voter",
				grandpa::run_grandpa_voter(grandpa_config)?
			);
		} else {
			grandpa::setup_disabled_grandpa(
				service.client(),
				&inherent_data_providers,
				service.network(),
			)?;
		}

		Ok((service, inherent_data_providers))
	}};
	($config:expr) => {{
		new_full!($config, |_, _| {})
	}}
}

type ConcreteBlock = node_primitives::Block;
type ConcreteClient =
	Client<
		Backend<ConcreteBlock>,
		LocalCallExecutor<Backend<ConcreteBlock>,
		NativeExecutor<node_executor::Executor>>,
		ConcreteBlock,
		node_runtime::RuntimeApi
	>;
type ConcreteBackend = Backend<ConcreteBlock>;
type ConcreteTransactionPool = sc_transaction_pool::BasicPool<
	sc_transaction_pool::FullChainApi<ConcreteClient, ConcreteBlock>,
	ConcreteBlock
>;

/// A specialized configuration object for setting up the node..
pub type NodeConfiguration = Configuration<GenesisConfig, crate::chain_spec::Extensions>;

/// Builds a new service for a full client.
pub fn new_full(config: NodeConfiguration)
-> Result<
	Service<
		ConcreteBlock,
		ConcreteClient,
		LongestChain<ConcreteBackend, ConcreteBlock>,
		NetworkStatus<ConcreteBlock>,
		NetworkService<ConcreteBlock, <ConcreteBlock as BlockT>::Hash>,
		ConcreteTransactionPool,
		OffchainWorkers<
			ConcreteClient,
			<ConcreteBackend as sc_client_api::backend::Backend<Block>>::OffchainStorage,
			ConcreteBlock,
		>
	>,
	ServiceError,
>
{
	new_full!(config).map(|(service, _)| service)
}

/// Builds a new service for a light client.
pub fn new_light(config: NodeConfiguration)
-> Result<impl AbstractService, ServiceError> {
	type RpcExtension = jsonrpc_core::IoHandler<sc_rpc::Metadata>;
	let inherent_data_providers = InherentDataProviders::new();

	let service = ServiceBuilder::new_light::<Block, RuntimeApi, node_executor::Executor>(config)?
		.with_select_chain(|_config, backend| {
			Ok(LongestChain::new(backend.clone()))
		})?
		.with_transaction_pool(|config, client, fetcher| {
			let fetcher = fetcher
				.ok_or_else(|| "Trying to start light transaction pool without active fetcher")?;
			let pool_api = sc_transaction_pool::LightChainApi::new(client.clone(), fetcher.clone());
			let pool = sc_transaction_pool::BasicPool::with_revalidation_type(
				config, Arc::new(pool_api), sc_transaction_pool::RevalidationType::Light,
			);
			Ok(pool)
		})?
		.with_import_queue_and_fprb(|_config, client, backend, fetcher, _select_chain, _tx_pool| {
			let fetch_checker = fetcher
				.map(|fetcher| fetcher.checker().clone())
				.ok_or_else(|| "Trying to start light import queue without active fetch checker")?;
			let grandpa_block_import = grandpa::light_block_import(
				client.clone(),
				backend,
				&*client,
				Arc::new(fetch_checker),
			)?;

			let finality_proof_import = grandpa_block_import.clone();
			let finality_proof_request_builder =
				finality_proof_import.create_finality_proof_request_builder();

			let (babe_block_import, babe_link) = sc_consensus_babe::block_import(
				sc_consensus_babe::Config::get_or_compute(&*client)?,
				grandpa_block_import,
				client.clone(),
			)?;

			let import_queue = sc_consensus_babe::import_queue(
				babe_link,
				babe_block_import,
				None,
				Some(Box::new(finality_proof_import)),
				client.clone(),
				inherent_data_providers.clone(),
			)?;

			Ok((import_queue, finality_proof_request_builder))
		})?
		.with_finality_proof_provider(|client, backend|
			Ok(Arc::new(GrandpaFinalityProofProvider::new(backend, client)) as _)
		)?
		.with_rpc_extensions(|builder,| ->
			Result<RpcExtension, _>
		{
			let fetcher = builder.fetcher()
				.ok_or_else(|| "Trying to start node RPC without active fetcher")?;
			let remote_blockchain = builder.remote_backend()
				.ok_or_else(|| "Trying to start node RPC without active remote blockchain")?;

			let light_deps = node_rpc::LightDeps {
				remote_blockchain,
				fetcher,
				client: builder.client().clone(),
				pool: builder.pool(),
			};
			Ok(node_rpc::create_light(light_deps))
		})?
		.build()?;

	Ok(service)
}

#[cfg(test)]
mod tests {
	use std::{sync::Arc, borrow::Cow, any::Any};
	use sc_consensus_babe::{
		CompatibleDigestItem, BabeIntermediate, INTERMEDIATE_KEY
	};
	use sc_consensus_epochs::descendent_query;
	use sp_consensus::{
		Environment, Proposer, BlockImportParams, BlockOrigin, ForkChoiceStrategy, BlockImport,
		RecordProof,
	};
	use node_primitives::{Block, DigestItem, Signature};
	use node_runtime::{BalancesCall, Call, UncheckedExtrinsic, Address};
	use node_runtime::constants::{currency::CENTS, time::SLOT_DURATION};
	use codec::{Encode, Decode};
	use sp_core::{crypto::Pair as CryptoPair, H256};
	use sp_runtime::{
		generic::{BlockId, Era, Digest, SignedPayload},
		traits::{Block as BlockT, Header as HeaderT},
		traits::Verify,
		OpaqueExtrinsic,
	};
	use sp_timestamp;
	use sp_finality_tracker;
	use sp_keyring::AccountKeyring;
	use sc_service::AbstractService;
	use crate::service::{new_full, new_light};
	use sp_runtime::traits::IdentifyAccount;

	type AccountPublic = <Signature as Verify>::Signer;

	#[cfg(feature = "rhd")]
	fn test_sync() {
		use sp_core::ed25519::Pair;

		use {service_test, Factory};
		use sc_client::{BlockImportParams, BlockOrigin};

		let alice: Arc<ed25519::Pair> = Arc::new(Keyring::Alice.into());
		let bob: Arc<ed25519::Pair> = Arc::new(Keyring::Bob.into());
		let validators = vec![alice.public().0.into(), bob.public().0.into()];
		let keys: Vec<&ed25519::Pair> = vec![&*alice, &*bob];
		let dummy_runtime = ::tokio::runtime::Runtime::new().unwrap();
		let block_factory = |service: &<Factory as service::ServiceFactory>::FullService| {
			let block_id = BlockId::number(service.client().chain_info().best_number);
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
				finalized: false,
				body: Some(block.extrinsics),
				storage_changes: None,
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
		sc_service_test::sync(
			sc_chain_spec::integration_test_config(),
			|config| new_full(config),
			|mut config| new_light(config),
			block_factory,
			extrinsic_factory,
		);
	}

	#[test]
	#[ignore]
	fn test_sync() {
		let keystore_path = tempfile::tempdir().expect("Creates keystore path");
		let keystore = sc_keystore::Store::open(keystore_path.path(), None)
			.expect("Creates keystore");
		let alice = keystore.write().insert_ephemeral_from_seed::<sc_consensus_babe::AuthorityPair>("//Alice")
			.expect("Creates authority pair");

		let chain_spec = crate::chain_spec::tests::integration_test_config_with_single_authority();

		// For the block factory
		let mut slot_num = 1u64;

		// For the extrinsics factory
		let bob = Arc::new(AccountKeyring::Bob.pair());
		let charlie = Arc::new(AccountKeyring::Charlie.pair());
		let mut index = 0;

		sc_service_test::sync(
			chain_spec,
			|config| {
				let mut setup_handles = None;
				new_full!(config, |
					block_import: &sc_consensus_babe::BabeBlockImport<Block, _, _>,
					babe_link: &sc_consensus_babe::BabeLink<Block>,
				| {
					setup_handles = Some((block_import.clone(), babe_link.clone()));
				}).map(move |(node, x)| (node, (x, setup_handles.unwrap())))
			},
			|config| new_light(config),
			|service, &mut (ref inherent_data_providers, (ref mut block_import, ref babe_link))| {
				let mut inherent_data = inherent_data_providers
					.create_inherent_data()
					.expect("Creates inherent data.");
				inherent_data.replace_data(sp_finality_tracker::INHERENT_IDENTIFIER, &1u64);

				let parent_id = BlockId::number(service.client().chain_info().best_number);
				let parent_header = service.client().header(&parent_id).unwrap().unwrap();
				let parent_hash = parent_header.hash();
				let parent_number = *parent_header.number();
				let mut proposer_factory = sc_basic_authorship::ProposerFactory {
					client: service.client(),
					transaction_pool: service.transaction_pool(),
				};

				let epoch = babe_link.epoch_changes().lock().epoch_for_child_of(
					descendent_query(&*service.client()),
					&parent_hash,
					parent_number,
					slot_num,
					|slot| babe_link.config().genesis_epoch(slot)
				).unwrap().unwrap();

				let mut digest = Digest::<H256>::default();

				// even though there's only one authority some slots might be empty,
				// so we must keep trying the next slots until we can claim one.
				let babe_pre_digest = loop {
					inherent_data.replace_data(sp_timestamp::INHERENT_IDENTIFIER, &(slot_num * SLOT_DURATION));
					if let Some(babe_pre_digest) = sc_consensus_babe::test_helpers::claim_slot(
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

				let new_block = futures::executor::block_on(async move {
					let proposer = proposer_factory.init(&parent_header).await;
					proposer.unwrap().propose(
						inherent_data,
						digest,
						std::time::Duration::from_secs(1),
						RecordProof::Yes,
					).await
				}).expect("Error making test block").block;

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

				let mut params = BlockImportParams::new(BlockOrigin::File, new_header);
				params.post_digests.push(item);
				params.body = Some(new_body);
				params.intermediates.insert(
					Cow::from(INTERMEDIATE_KEY),
					Box::new(BabeIntermediate { epoch }) as Box<dyn Any>,
				);
				params.fork_choice = Some(ForkChoiceStrategy::LongestChain);

				block_import.import_block(params, Default::default())
					.expect("error importing test block");
			},
			|service, _| {
				let amount = 5 * CENTS;
				let to: Address = AccountPublic::from(bob.public()).into_account().into();
				let from: Address = AccountPublic::from(charlie.public()).into_account().into();
				let genesis_hash = service.client().block_hash(0).unwrap().unwrap();
				let best_block_id = BlockId::number(service.client().chain_info().best_number);
				let version = service.client().runtime_version_at(&best_block_id).unwrap().spec_version;
				let signer = charlie.clone();

				let function = Call::Balances(BalancesCall::transfer(to.into(), amount));

				let check_version = frame_system::CheckVersion::new();
				let check_genesis = frame_system::CheckGenesis::new();
				let check_era = frame_system::CheckEra::from(Era::Immortal);
				let check_nonce = frame_system::CheckNonce::from(index);
				let check_weight = frame_system::CheckWeight::new();
				let payment = pallet_transaction_payment::ChargeTransactionPayment::from(0);
				let extra = (
					check_version,
					check_genesis,
					check_era,
					check_nonce,
					check_weight,
					payment,
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
		sc_service_test::consensus(
			crate::chain_spec::tests::integration_test_config_with_two_authorities(),
			|config| new_full(config),
			|config| new_light(config),
			vec![
				"//Alice".into(),
				"//Bob".into(),
			],
		)
	}
}
