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

use babe::{import_queue, Config};
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
		let mut tasks_to_spawn = Vec::new();

		let builder = substrate_service::ServiceBuilder::new_full::<
			node_primitives::Block, node_runtime::RuntimeApi, node_executor::Executor
		>($config)?
			.with_select_chain(|_config, backend| {
				Ok(client::LongestChain::new(backend.clone()))
			})?
			.with_transaction_pool(|config, client|
				Ok(transaction_pool::txpool::Pool::new(config, transaction_pool::ChainApi::new(client)))
			)?
			.with_import_queue(|_config, client, mut select_chain, transaction_pool| {
				let select_chain = select_chain.take()
					.ok_or_else(|| substrate_service::Error::SelectChainRequired)?;
				let (block_import, link_half) =
					grandpa::block_import::<_, _, _, node_runtime::RuntimeApi, _, _>(
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
				tasks_to_spawn.push(Box::new(pruning_task));

				Ok(import_queue)
			})?
			.with_rpc_extensions(|client, pool| {
				use node_rpc::accounts::{Accounts, AccountsApi};

				let mut io = jsonrpc_core::IoHandler::<substrate_service::RpcMetadata>::default();
				io.extend_with(
					AccountsApi::to_delegate(Accounts::new(client, pool))
				);
				io
			})?;

		(builder, import_setup, inherent_data_providers, tasks_to_spawn)
	}}
}

/// Creates a full service from the configuration.
///
/// We need to use a macro because the test suit doesn't work with an opaque service. It expects
/// concrete types instead.
macro_rules! new_full {
	($config:expr) => {{
		use futures::Future;

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

		let (builder, mut import_setup, inherent_data_providers, mut tasks_to_spawn) = new_full_start!($config);

		let service = builder.with_network_protocol(|_| Ok(crate::service::NodeProtocol::new()))?
			.with_finality_proof_provider(|client, backend|
				Ok(Arc::new(grandpa::FinalityProofProvider::new(backend, client)) as _)
			)?
			.build()?;

		let (block_import, link_half, babe_link) = import_setup.take()
				.expect("Link Half and Block Import are present for Full Services or setup failed before. qed");

		// spawn any futures that were created in the previous setup steps
		for task in tasks_to_spawn.drain(..) {
			service.spawn_task(
				task.select(service.on_exit())
					.map(|_| ())
					.map_err(|_| ())
			);
		}

		if is_authority {
			let proposer = substrate_basic_authorship::ProposerFactory {
				client: service.client(),
				transaction_pool: service.transaction_pool(),
			};

			let client = service.client();
			let select_chain = service.select_chain()
				.ok_or(substrate_service::Error::SelectChainRequired)?;

			let babe_config = babe::BabeParams {
				config: babe::Config::get_or_compute(&*client)?,
				keystore: service.keystore(),
				client,
				select_chain,
				block_import,
				env: proposer,
				sync_oracle: service.network(),
				inherent_data_providers: inherent_data_providers.clone(),
				force_authoring: force_authoring,
				time_source: babe_link,
			};

			let babe = babe::start_babe(babe_config)?;
			let select = babe.select(service.on_exit()).then(|_| Ok(()));
			service.spawn_task(Box::new(select));
		}

		let config = grandpa::Config {
			// FIXME #1578 make this available through chainspec
			gossip_duration: std::time::Duration::from_millis(333),
			justification_period: 4096,
			name: Some(name),
			keystore: Some(service.keystore()),
		};

		match (is_authority, disable_grandpa) {
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
	}}
}

/// Builds a new service for a full client.
pub fn new_full<C: Send + Default + 'static>(config: Configuration<C, GenesisConfig>)
-> Result<impl AbstractService, ServiceError> {
	new_full!(config).map(|(service, _)| service)
}

/// Builds a new service for a light client.
pub fn new_light<C: Send + Default + 'static>(config: Configuration<C, GenesisConfig>)
-> Result<impl AbstractService, ServiceError> {
	use futures::Future;

	let inherent_data_providers = InherentDataProviders::new();
	let mut tasks_to_spawn = Vec::new();

	let service = ServiceBuilder::new_light::<Block, RuntimeApi, node_executor::Executor>(config)?
		.with_select_chain(|_config, backend| {
			Ok(LongestChain::new(backend.clone()))
		})?
		.with_transaction_pool(|config, client|
			Ok(TransactionPool::new(config, transaction_pool::ChainApi::new(client)))
		)?
		.with_import_queue_and_fprb(|_config, client, backend, _select_chain, transaction_pool| {
			let fetch_checker = backend.blockchain().fetcher()
				.upgrade()
				.map(|fetcher| fetcher.checker().clone())
				.ok_or_else(|| "Trying to start light import queue without active fetch checker")?;
			let block_import = grandpa::light_block_import::<_, _, _, RuntimeApi, _>(
				client.clone(), backend, Arc::new(fetch_checker), client.clone()
			)?;

			let finality_proof_import = block_import.clone();
			let finality_proof_request_builder =
				finality_proof_import.create_finality_proof_request_builder();

			let (import_queue, _, _, pruning_task) = import_queue(
				Config::get_or_compute(&*client)?,
				block_import,
				None,
				Some(Box::new(finality_proof_import)),
				client.clone(),
				client,
				inherent_data_providers.clone(),
				Some(transaction_pool)
			)?;

			tasks_to_spawn.push(Box::new(pruning_task));

			Ok((import_queue, finality_proof_request_builder))
		})?
		.with_network_protocol(|_| Ok(NodeProtocol::new()))?
		.with_finality_proof_provider(|client, backend|
			Ok(Arc::new(GrandpaFinalityProofProvider::new(backend, client)) as _)
		)?
		.with_rpc_extensions(|client, pool| {
			use node_rpc::accounts::{Accounts, AccountsApi};

			let mut io = jsonrpc_core::IoHandler::default();
			io.extend_with(
				AccountsApi::to_delegate(Accounts::new(client, pool))
			);
			io
		})?
		.build()?;

	// spawn any futures that were created in the previous setup steps
	for task in tasks_to_spawn.drain(..) {
		service.spawn_task(
			task.select(service.on_exit())
				.map(|_| ())
				.map_err(|_| ())
		);
	}

	Ok(service)
}

#[cfg(test)]
mod tests {
	use std::sync::Arc;
	use babe::CompatibleDigestItem;
	use consensus_common::{
		Environment, Proposer, BlockImportParams, BlockOrigin, ForkChoiceStrategy
	};
	use node_primitives::DigestItem;
	use node_runtime::{BalancesCall, Call, UncheckedExtrinsic};
	use node_runtime::constants::{currency::CENTS, time::{PRIMARY_PROBABILITY, SLOT_DURATION}};
	use codec::{Encode, Decode};
	use primitives::{
		crypto::Pair as CryptoPair, blake2_256,
		sr25519::Public as AddressPublic, H256,
	};
	use sr_primitives::{generic::{BlockId, Era, Digest, SignedPayload}, traits::Block, OpaqueExtrinsic};
	use timestamp;
	use finality_tracker;
	use keyring::AccountKeyring;
	use substrate_service::AbstractService;
	use crate::service::{new_full, new_light};

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
			|config| new_light(config),
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
			|config| new_full!(config),
			|config| new_light(config),
			|service, inherent_data_providers| {
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
						PRIMARY_PROBABILITY,
						&keystore,
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

				BlockImportParams {
					origin: BlockOrigin::File,
					header: new_header,
					justification: None,
					post_digests: vec![item],
					body: Some(new_body),
					finalized: true,
					auxiliary: Vec::new(),
					fork_choice: ForkChoiceStrategy::LongestChain,
				}
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
				let extra = (check_version, check_genesis, check_era, check_nonce, check_weight, take_fees);
				let raw_payload = SignedPayload::from_raw(
					function,
					extra,
					(version, genesis_hash, genesis_hash, (), (), ())
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
			|config| new_light(config),
			vec![
				"//Alice".into(),
				"//Bob".into(),
			],
		)
	}
}
