// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

#![warn(unused_extern_crates)]

//! Service implementation. Specialized wrapper over substrate service.

use futures::prelude::*;
use node_executor::ExecutorDispatch;
use node_primitives::Block;
use node_runtime::RuntimeApi;
use sc_client_api::{ExecutorProvider, RemoteBackend};
use sc_consensus_babe::{self, SlotProportion};
use sc_executor::NativeElseWasmExecutor;
use sc_network::{Event, NetworkService};
use sc_service::{config::Configuration, error::Error as ServiceError, TaskManager};
use sc_telemetry::{Telemetry, TelemetryWorker};
use sp_runtime::traits::Block as BlockT;
use std::sync::Arc;

use jsonrpsee::RpcModule;
use pallet_contracts_rpc::ContractsRpc;
use pallet_mmr_rpc::MmrRpc;
use pallet_transaction_payment_rpc::TransactionPaymentRpc;
use sc_consensus_babe_rpc::BabeRpc;
use sc_finality_grandpa_rpc::GrandpaRpc;
use sc_sync_state_rpc::SyncStateRpc;
use substrate_frame_rpc_system::{SystemApiServer, SystemRpc, SystemRpcBackendFull};

type FullClient =
	sc_service::TFullClient<Block, RuntimeApi, NativeElseWasmExecutor<ExecutorDispatch>>;
type FullBackend = sc_service::TFullBackend<Block>;
type FullSelectChain = sc_consensus::LongestChain<FullBackend, Block>;
type FullGrandpaBlockImport =
	grandpa::GrandpaBlockImport<FullBackend, Block, FullClient, FullSelectChain>;
type LightClient =
	sc_service::TLightClient<Block, RuntimeApi, NativeElseWasmExecutor<ExecutorDispatch>>;

/// Build and initialise an incomplete set of chain components and RPC modules needed to start a
/// full client after further components are added.
pub fn new_partial(
	config: &Configuration,
) -> Result<
	sc_service::PartialComponents<
		FullClient,
		FullBackend,
		FullSelectChain,
		sc_consensus::DefaultImportQueue<Block, FullClient>,
		sc_transaction_pool::FullPool<Block, FullClient>,
		(
			// Block import setup.
			(
				sc_consensus_babe::BabeBlockImport<Block, FullClient, FullGrandpaBlockImport>,
				grandpa::LinkHalf<Block, FullClient, FullSelectChain>,
				sc_consensus_babe::BabeLink<Block>,
			),
			Option<Telemetry>,
		),
	>,
	ServiceError,
> {
	let telemetry = config
		.telemetry_endpoints
		.clone()
		.filter(|x| !x.is_empty())
		.map(|endpoints| -> Result<_, sc_telemetry::Error> {
			let worker = TelemetryWorker::new(16)?;
			let telemetry = worker.handle().new_telemetry(endpoints);
			Ok((worker, telemetry))
		})
		.transpose()?;

	let executor = NativeElseWasmExecutor::<ExecutorDispatch>::new(
		config.wasm_method,
		config.default_heap_pages,
		config.max_runtime_instances,
	);

	let (client, backend, keystore_container, task_manager) =
		sc_service::new_full_parts::<Block, RuntimeApi, _>(
			&config,
			telemetry.as_ref().map(|(_, telemetry)| telemetry.handle()),
			executor,
		)?;
	let client = Arc::new(client);

	let telemetry = telemetry.map(|(worker, telemetry)| {
		task_manager.spawn_handle().spawn("telemetry", worker.run());
		telemetry
	});

	let select_chain = sc_consensus::LongestChain::new(backend.clone());

	let transaction_pool = sc_transaction_pool::BasicPool::new_full(
		config.transaction_pool.clone(),
		config.role.is_authority().into(),
		config.prometheus_registry(),
		task_manager.spawn_essential_handle(),
		client.clone(),
	);

	let (grandpa_block_import, grandpa_link) = grandpa::block_import(
		client.clone(),
		&(client.clone() as Arc<_>),
		select_chain.clone(),
		telemetry.as_ref().map(|x| x.handle()),
	)?;
	let justification_import = grandpa_block_import.clone();

	let (block_import, babe_link) = sc_consensus_babe::block_import(
		sc_consensus_babe::Config::get_or_compute(&*client)?,
		grandpa_block_import,
		client.clone(),
	)?;

	let slot_duration = babe_link.config().slot_duration();
	let import_queue = sc_consensus_babe::import_queue(
		babe_link.clone(),
		block_import.clone(),
		Some(Box::new(justification_import)),
		client.clone(),
		select_chain.clone(),
		move |_, ()| async move {
			let timestamp = sp_timestamp::InherentDataProvider::from_system_time();

			let slot =
				sp_consensus_babe::inherents::InherentDataProvider::from_timestamp_and_duration(
					*timestamp,
					slot_duration,
				);

			let uncles =
				sp_authorship::InherentDataProvider::<<Block as BlockT>::Header>::check_inherents();

			Ok((timestamp, slot, uncles))
		},
		&task_manager.spawn_essential_handle(),
		config.prometheus_registry(),
		sp_consensus::CanAuthorWithNativeVersion::new(client.executor().clone()),
		telemetry.as_ref().map(|x| x.handle()),
	)?;

	// Grandpa stuff
	let shared_authority_set = grandpa_link.shared_authority_set().clone();
	let justification_stream = grandpa_link.justification_stream().clone();
	let backend2 = backend.clone();
	// Babe stuff
	let select_chain2 = select_chain.clone();
	let sync_keystore = keystore_container.sync_keystore().clone();
	let client2 = client.clone();
	let babe_link2 = babe_link.clone();
	// SyncState
	let chain_spec = config.chain_spec.cloned_box();
	let shared_epoch_changes = babe_link.epoch_changes().clone();
	// System
	let transaction_pool2 = transaction_pool.clone();
	let rpc_builder = Box::new(move |deny_unsafe, executor| -> RpcModule<()> {
		let grandpa_rpc = GrandpaRpc::new(
			executor,
			shared_authority_set.clone(),
			grandpa::SharedVoterState::empty(),
			justification_stream,
			grandpa::FinalityProofProvider::new_for_service(
				backend2,
				Some(shared_authority_set.clone()),
			),
		)
		.into_rpc_module()
		.expect("TODO: error handling");

		let babe_rpc = BabeRpc::new(
			client2.clone(),
			babe_link.epoch_changes().clone(),
			sync_keystore,
			babe_link.config().clone(),
			select_chain2,
			deny_unsafe,
		)
		.into_rpc_module()
		.expect("TODO: error handling");
		let sync_state_rpc = SyncStateRpc::new(
			chain_spec,
			client2.clone(),
			shared_authority_set.clone(),
			shared_epoch_changes,
			deny_unsafe,
		)
		.expect("TODO: error handling")
		.into_rpc_module()
		.expect("TODO: error handling");
		let transaction_payment_rpc = TransactionPaymentRpc::new(client2.clone())
			.into_rpc_module()
			.expect("TODO: error handling");
		let system_rpc_backend =
			SystemRpcBackendFull::new(client2.clone(), transaction_pool2.clone(), deny_unsafe);
		let system_rpc = SystemRpc::new(Box::new(system_rpc_backend)).into_rpc();
		let mmr_rpc = MmrRpc::new(client2.clone()).into_rpc_module().expect("TODO: error handling");
		let contracts_rpc = ContractsRpc::new(client2.clone())
			.into_rpc_module()
			.expect("TODO: error handling");

		let mut module = RpcModule::new(());
		module.merge(grandpa_rpc).expect("TODO: error handling");
		module.merge(babe_rpc).expect("TODO: error handling");
		module.merge(sync_state_rpc).expect("TODO: error handling");
		module.merge(transaction_payment_rpc).expect("TODO: error handling");
		module.merge(system_rpc).expect("TODO: error handling");
		module.merge(mmr_rpc).expect("TODO: error handling");
		module.merge(contracts_rpc).expect("TODO: error handling");
		module
	});

	let import_setup = (block_import, grandpa_link, babe_link2);

	Ok(sc_service::PartialComponents {
		client,
		backend,
		task_manager,
		keystore_container,
		select_chain,
		import_queue,
		transaction_pool,
		rpc_builder,
		other: (import_setup, telemetry),
	})
}

pub struct NewFullBase {
	pub task_manager: TaskManager,
	pub client: Arc<FullClient>,
	pub network: Arc<NetworkService<Block, <Block as BlockT>::Hash>>,
	pub transaction_pool: Arc<sc_transaction_pool::FullPool<Block, FullClient>>,
}

/// Creates a full service from the configuration.
pub fn new_full_base(
	mut config: Configuration,
	with_startup_data: impl FnOnce(
		&sc_consensus_babe::BabeBlockImport<Block, FullClient, FullGrandpaBlockImport>,
		&sc_consensus_babe::BabeLink<Block>,
	),
) -> Result<NewFullBase, ServiceError> {
	let sc_service::PartialComponents {
		client,
		backend,
		mut task_manager,
		import_queue,
		keystore_container,
		select_chain,
		transaction_pool,
		rpc_builder,
		other: (import_setup, mut telemetry),
	} = new_partial(&config)?;

	let auth_disc_publish_non_global_ips = config.network.allow_non_globals_in_dht;

	config.network.extra_sets.push(grandpa::grandpa_peers_set_config());
	let warp_sync = Arc::new(grandpa::warp_proof::NetworkProvider::new(
		backend.clone(),
		import_setup.1.shared_authority_set().clone(),
	));

	let (network, system_rpc_tx, network_starter) =
		sc_service::build_network(sc_service::BuildNetworkParams {
			config: &config,
			client: client.clone(),
			transaction_pool: transaction_pool.clone(),
			spawn_handle: task_manager.spawn_handle(),
			import_queue,
			on_demand: None,
			block_announce_validator_builder: None,
			warp_sync: Some(warp_sync),
		})?;

	if config.offchain_worker.enabled {
		sc_service::build_offchain_workers(
			&config,
			task_manager.spawn_handle(),
			client.clone(),
			network.clone(),
		);
	}

	let role = config.role.clone();
	let force_authoring = config.force_authoring;
	let backoff_authoring_blocks =
		Some(sc_consensus_slots::BackoffAuthoringOnFinalizedHeadLagging::default());
	let name = config.network.node_name.clone();
	let enable_grandpa = !config.disable_grandpa;
	let prometheus_registry = config.prometheus_registry().cloned();

	let _rpc_handlers = sc_service::spawn_tasks(sc_service::SpawnTasksParams {
		config,
		backend: backend.clone(),
		client: client.clone(),
		keystore: keystore_container.sync_keystore(),
		network: network.clone(),
		rpc_builder: Box::new(rpc_builder),
		transaction_pool: transaction_pool.clone(),
		task_manager: &mut task_manager,
		on_demand: None,
		remote_blockchain: None,
		system_rpc_tx,
		telemetry: telemetry.as_mut(),
	})?;

	let (block_import, grandpa_link, babe_link) = import_setup;

	(with_startup_data)(&block_import, &babe_link);

	if let sc_service::config::Role::Authority { .. } = &role {
		let proposer = sc_basic_authorship::ProposerFactory::new(
			task_manager.spawn_handle(),
			client.clone(),
			transaction_pool.clone(),
			prometheus_registry.as_ref(),
			telemetry.as_ref().map(|x| x.handle()),
		);

		let can_author_with =
			sp_consensus::CanAuthorWithNativeVersion::new(client.executor().clone());

		let client_clone = client.clone();
		let slot_duration = babe_link.config().slot_duration();
		let babe_config = sc_consensus_babe::BabeParams {
			keystore: keystore_container.sync_keystore(),
			client: client.clone(),
			select_chain,
			env: proposer,
			block_import,
			sync_oracle: network.clone(),
			justification_sync_link: network.clone(),
			create_inherent_data_providers: move |parent, ()| {
				let client_clone = client_clone.clone();
				async move {
					let uncles = sc_consensus_uncles::create_uncles_inherent_data_provider(
						&*client_clone,
						parent,
					)?;

					let timestamp = sp_timestamp::InherentDataProvider::from_system_time();

					let slot =
						sp_consensus_babe::inherents::InherentDataProvider::from_timestamp_and_duration(
							*timestamp,
							slot_duration,
						);

					let storage_proof =
						sp_transaction_storage_proof::registration::new_data_provider(
							&*client_clone,
							&parent,
						)?;

					Ok((timestamp, slot, uncles, storage_proof))
				}
			},
			force_authoring,
			backoff_authoring_blocks,
			babe_link,
			can_author_with,
			block_proposal_slot_portion: SlotProportion::new(0.5),
			max_block_proposal_slot_portion: None,
			telemetry: telemetry.as_ref().map(|x| x.handle()),
		};

		let babe = sc_consensus_babe::start_babe(babe_config)?;
		task_manager.spawn_essential_handle().spawn_blocking("babe-proposer", babe);
	}

	// Spawn authority discovery module.
	if role.is_authority() {
		let authority_discovery_role =
			sc_authority_discovery::Role::PublishAndDiscover(keystore_container.keystore());
		let dht_event_stream =
			network.event_stream("authority-discovery").filter_map(|e| async move {
				match e {
					Event::Dht(e) => Some(e),
					_ => None,
				}
			});
		let (authority_discovery_worker, _service) =
			sc_authority_discovery::new_worker_and_service_with_config(
				sc_authority_discovery::WorkerConfig {
					publish_non_global_ips: auth_disc_publish_non_global_ips,
					..Default::default()
				},
				client.clone(),
				network.clone(),
				Box::pin(dht_event_stream),
				authority_discovery_role,
				prometheus_registry.clone(),
			);

		task_manager
			.spawn_handle()
			.spawn("authority-discovery-worker", authority_discovery_worker.run());
	}

	// if the node isn't actively participating in consensus then it doesn't
	// need a keystore, regardless of which protocol we use below.
	let keystore =
		if role.is_authority() { Some(keystore_container.sync_keystore()) } else { None };

	let config = grandpa::Config {
		// FIXME #1578 make this available through chainspec
		gossip_duration: std::time::Duration::from_millis(333),
		justification_period: 512,
		name: Some(name),
		observer_enabled: false,
		keystore,
		local_role: role,
		telemetry: telemetry.as_ref().map(|x| x.handle()),
	};

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
			network: network.clone(),
			telemetry: telemetry.as_ref().map(|x| x.handle()),
			voting_rule: grandpa::VotingRulesBuilder::default().build(),
			prometheus_registry,
			shared_voter_state: grandpa::SharedVoterState::empty(),
		};

		// the GRANDPA voter task is considered infallible, i.e.
		// if it fails we take down the service with it.
		task_manager
			.spawn_essential_handle()
			.spawn_blocking("grandpa-voter", grandpa::run_grandpa_voter(grandpa_config)?);
	}

	network_starter.start_network();
	Ok(NewFullBase { task_manager, client, network, transaction_pool })
}

/// Builds a new service for a full client.
pub fn new_full(config: Configuration) -> Result<TaskManager, ServiceError> {
	new_full_base(config, |_, _| ()).map(|NewFullBase { task_manager, .. }| task_manager)
}

pub fn new_light_base(
	mut config: Configuration,
) -> Result<
	(
		TaskManager,
		Arc<LightClient>,
		Arc<NetworkService<Block, <Block as BlockT>::Hash>>,
		Arc<
			sc_transaction_pool::LightPool<Block, LightClient, sc_network::config::OnDemand<Block>>,
		>,
	),
	ServiceError,
> {
	let telemetry = config
		.telemetry_endpoints
		.clone()
		.filter(|x| !x.is_empty())
		.map(|endpoints| -> Result<_, sc_telemetry::Error> {
			let worker = TelemetryWorker::new(16)?;
			let telemetry = worker.handle().new_telemetry(endpoints);
			Ok((worker, telemetry))
		})
		.transpose()?;

	let executor = NativeElseWasmExecutor::<ExecutorDispatch>::new(
		config.wasm_method,
		config.default_heap_pages,
		config.max_runtime_instances,
	);

	let (client, backend, keystore_container, mut task_manager, on_demand) =
		sc_service::new_light_parts::<Block, RuntimeApi, _>(
			&config,
			telemetry.as_ref().map(|(_, telemetry)| telemetry.handle()),
			executor,
		)?;

	let mut telemetry = telemetry.map(|(worker, telemetry)| {
		task_manager.spawn_handle().spawn("telemetry", worker.run());
		telemetry
	});

	config.network.extra_sets.push(grandpa::grandpa_peers_set_config());

	let select_chain = sc_consensus::LongestChain::new(backend.clone());

	let transaction_pool = Arc::new(sc_transaction_pool::BasicPool::new_light(
		config.transaction_pool.clone(),
		config.prometheus_registry(),
		task_manager.spawn_essential_handle(),
		client.clone(),
		on_demand.clone(),
	));

	let (grandpa_block_import, grandpa_link) = grandpa::block_import(
		client.clone(),
		&(client.clone() as Arc<_>),
		select_chain.clone(),
		telemetry.as_ref().map(|x| x.handle()),
	)?;
	let justification_import = grandpa_block_import.clone();

	let (babe_block_import, babe_link) = sc_consensus_babe::block_import(
		sc_consensus_babe::Config::get_or_compute(&*client)?,
		grandpa_block_import,
		client.clone(),
	)?;

	let slot_duration = babe_link.config().slot_duration();
	let import_queue = sc_consensus_babe::import_queue(
		babe_link,
		babe_block_import,
		Some(Box::new(justification_import)),
		client.clone(),
		select_chain.clone(),
		move |_, ()| async move {
			let timestamp = sp_timestamp::InherentDataProvider::from_system_time();

			let slot =
				sp_consensus_babe::inherents::InherentDataProvider::from_timestamp_and_duration(
					*timestamp,
					slot_duration,
				);

			let uncles =
				sp_authorship::InherentDataProvider::<<Block as BlockT>::Header>::check_inherents();

			Ok((timestamp, slot, uncles))
		},
		&task_manager.spawn_essential_handle(),
		config.prometheus_registry(),
		sp_consensus::NeverCanAuthor,
		telemetry.as_ref().map(|x| x.handle()),
	)?;

	let warp_sync = Arc::new(grandpa::warp_proof::NetworkProvider::new(
		backend.clone(),
		grandpa_link.shared_authority_set().clone(),
	));

	let (network, system_rpc_tx, network_starter) =
		sc_service::build_network(sc_service::BuildNetworkParams {
			config: &config,
			client: client.clone(),
			transaction_pool: transaction_pool.clone(),
			spawn_handle: task_manager.spawn_handle(),
			import_queue,
			on_demand: Some(on_demand.clone()),
			block_announce_validator_builder: None,
			warp_sync: Some(warp_sync),
		})?;

	let enable_grandpa = !config.disable_grandpa;
	if enable_grandpa {
		let name = config.network.node_name.clone();

		let config = grandpa::Config {
			gossip_duration: std::time::Duration::from_millis(333),
			justification_period: 512,
			name: Some(name),
			observer_enabled: false,
			keystore: None,
			local_role: config.role.clone(),
			telemetry: telemetry.as_ref().map(|x| x.handle()),
		};

		task_manager.spawn_handle().spawn_blocking(
			"grandpa-observer",
			grandpa::run_grandpa_observer(config, grandpa_link, network.clone())?,
		);
	}

	if config.offchain_worker.enabled {
		sc_service::build_offchain_workers(
			&config,
			task_manager.spawn_handle(),
			client.clone(),
			network.clone(),
		);
	}

	// TODO: (dp) implement rpsee builder here for all RPC modules available to the light client.
	sc_service::spawn_tasks(sc_service::SpawnTasksParams {
		on_demand: Some(on_demand),
		remote_blockchain: Some(backend.remote_blockchain()),
		// TODO(niklasad1): implement.
		rpc_builder: Box::new(|_, _| RpcModule::new(())),
		client: client.clone(),
		transaction_pool: transaction_pool.clone(),
		keystore: keystore_container.sync_keystore(),
		config,
		backend,
		system_rpc_tx,
		network: network.clone(),
		task_manager: &mut task_manager,
		telemetry: telemetry.as_mut(),
	})?;

	network_starter.start_network();
	Ok((task_manager, client, network, transaction_pool))
}

/// Builds a new service for a light client.
pub fn new_light(config: Configuration) -> Result<TaskManager, ServiceError> {
	new_light_base(config).map(|(task_manager, _, _, _)| task_manager)
}

#[cfg(test)]
mod tests {
	use crate::service::{new_full_base, new_light_base, NewFullBase};
	use codec::Encode;
	use node_primitives::{Block, DigestItem, Signature};
	use node_runtime::{
		constants::{currency::CENTS, time::SLOT_DURATION},
		Address, BalancesCall, Call, UncheckedExtrinsic,
	};
	use sc_client_api::BlockBackend;
	use sc_consensus::{BlockImport, BlockImportParams, ForkChoiceStrategy};
	use sc_consensus_babe::{BabeIntermediate, CompatibleDigestItem, INTERMEDIATE_KEY};
	use sc_consensus_epochs::descendent_query;
	use sc_keystore::LocalKeystore;
	use sc_service_test::TestNetNode;
	use sc_transaction_pool_api::{ChainEvent, MaintainedTransactionPool};
	use sp_consensus::{BlockOrigin, Environment, Proposer};
	use sp_core::{crypto::Pair as CryptoPair, Public, H256};
	use sp_inherents::InherentDataProvider;
	use sp_keyring::AccountKeyring;
	use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};
	use sp_runtime::{
		generic::{BlockId, Digest, Era, SignedPayload},
		key_types::BABE,
		traits::{Block as BlockT, Header as HeaderT, IdentifyAccount, Verify},
		RuntimeAppPublic,
	};
	use sp_timestamp;
	use std::{borrow::Cow, convert::TryInto, sync::Arc};

	type AccountPublic = <Signature as Verify>::Signer;

	#[test]
	// It is "ignored", but the node-cli ignored tests are running on the CI.
	// This can be run locally with `cargo test --release -p node-cli test_sync -- --ignored`.
	#[ignore]
	fn test_sync() {
		let keystore_path = tempfile::tempdir().expect("Creates keystore path");
		let keystore: SyncCryptoStorePtr =
			Arc::new(LocalKeystore::open(keystore_path.path(), None).expect("Creates keystore"));
		let alice: sp_consensus_babe::AuthorityId =
			SyncCryptoStore::sr25519_generate_new(&*keystore, BABE, Some("//Alice"))
				.expect("Creates authority pair")
				.into();

		let chain_spec = crate::chain_spec::tests::integration_test_config_with_single_authority();

		// For the block factory
		let mut slot = 1u64;

		// For the extrinsics factory
		let bob = Arc::new(AccountKeyring::Bob.pair());
		let charlie = Arc::new(AccountKeyring::Charlie.pair());
		let mut index = 0;

		sc_service_test::sync(
			chain_spec,
			|config| {
				let mut setup_handles = None;
				let NewFullBase { task_manager, client, network, transaction_pool, .. } =
					new_full_base(
						config,
						|block_import: &sc_consensus_babe::BabeBlockImport<Block, _, _>,
						 babe_link: &sc_consensus_babe::BabeLink<Block>| {
							setup_handles = Some((block_import.clone(), babe_link.clone()));
						},
					)?;

				let node = sc_service_test::TestNetComponents::new(
					task_manager,
					client,
					network,
					transaction_pool,
				);
				Ok((node, setup_handles.unwrap()))
			},
			|config| {
				let (keep_alive, _, client, network, transaction_pool) = new_light_base(config)?;
				Ok(sc_service_test::TestNetComponents::new(
					keep_alive,
					client,
					network,
					transaction_pool,
				))
			},
			|service, &mut (ref mut block_import, ref babe_link)| {
				let parent_id = BlockId::number(service.client().chain_info().best_number);
				let parent_header = service.client().header(&parent_id).unwrap().unwrap();
				let parent_hash = parent_header.hash();
				let parent_number = *parent_header.number();

				futures::executor::block_on(service.transaction_pool().maintain(
					ChainEvent::NewBestBlock { hash: parent_header.hash(), tree_route: None },
				));

				let mut proposer_factory = sc_basic_authorship::ProposerFactory::new(
					service.spawn_handle(),
					service.client(),
					service.transaction_pool(),
					None,
					None,
				);

				let mut digest = Digest::<H256>::default();

				// even though there's only one authority some slots might be empty,
				// so we must keep trying the next slots until we can claim one.
				let (babe_pre_digest, epoch_descriptor) = loop {
					let epoch_descriptor = babe_link
						.epoch_changes()
						.shared_data()
						.epoch_descriptor_for_child_of(
							descendent_query(&*service.client()),
							&parent_hash,
							parent_number,
							slot.into(),
						)
						.unwrap()
						.unwrap();

					let epoch = babe_link
						.epoch_changes()
						.shared_data()
						.epoch_data(&epoch_descriptor, |slot| {
							sc_consensus_babe::Epoch::genesis(&babe_link.config(), slot)
						})
						.unwrap();

					if let Some(babe_pre_digest) =
						sc_consensus_babe::authorship::claim_slot(slot.into(), &epoch, &keystore)
							.map(|(digest, _)| digest)
					{
						break (babe_pre_digest, epoch_descriptor);
					}

					slot += 1;
				};

				let inherent_data = (
					sp_timestamp::InherentDataProvider::new(
						std::time::Duration::from_millis(SLOT_DURATION * slot).into(),
					),
					sp_consensus_babe::inherents::InherentDataProvider::new(slot.into()),
				)
					.create_inherent_data()
					.expect("Creates inherent data");

				digest.push(<DigestItem as CompatibleDigestItem>::babe_pre_digest(babe_pre_digest));

				let new_block = futures::executor::block_on(async move {
					let proposer = proposer_factory.init(&parent_header).await;
					proposer
						.unwrap()
						.propose(inherent_data, digest, std::time::Duration::from_secs(1), None)
						.await
				})
				.expect("Error making test block")
				.block;

				let (new_header, new_body) = new_block.deconstruct();
				let pre_hash = new_header.hash();
				// sign the pre-sealed hash of the block and then
				// add it to a digest item.
				let to_sign = pre_hash.encode();
				let signature = SyncCryptoStore::sign_with(
					&*keystore,
					sp_consensus_babe::AuthorityId::ID,
					&alice.to_public_crypto_pair(),
					&to_sign,
				)
				.unwrap()
				.unwrap()
				.try_into()
				.unwrap();
				let item = <DigestItem as CompatibleDigestItem>::babe_seal(signature);
				slot += 1;

				let mut params = BlockImportParams::new(BlockOrigin::File, new_header);
				params.post_digests.push(item);
				params.body = Some(new_body);
				params.intermediates.insert(
					Cow::from(INTERMEDIATE_KEY),
					Box::new(BabeIntermediate::<Block> { epoch_descriptor }) as Box<_>,
				);
				params.fork_choice = Some(ForkChoiceStrategy::LongestChain);

				futures::executor::block_on(block_import.import_block(params, Default::default()))
					.expect("error importing test block");
			},
			|service, _| {
				let amount = 5 * CENTS;
				let to: Address = AccountPublic::from(bob.public()).into_account().into();
				let from: Address = AccountPublic::from(charlie.public()).into_account().into();
				let genesis_hash = service.client().block_hash(0).unwrap().unwrap();
				let best_block_id = BlockId::number(service.client().chain_info().best_number);
				let (spec_version, transaction_version) = {
					let version = service.client().runtime_version_at(&best_block_id).unwrap();
					(version.spec_version, version.transaction_version)
				};
				let signer = charlie.clone();

				let function = Call::Balances(BalancesCall::transfer(to.into(), amount));

				let check_spec_version = frame_system::CheckSpecVersion::new();
				let check_tx_version = frame_system::CheckTxVersion::new();
				let check_genesis = frame_system::CheckGenesis::new();
				let check_era = frame_system::CheckEra::from(Era::Immortal);
				let check_nonce = frame_system::CheckNonce::from(index);
				let check_weight = frame_system::CheckWeight::new();
				let payment = pallet_transaction_payment::ChargeTransactionPayment::from(0);
				let extra = (
					check_spec_version,
					check_tx_version,
					check_genesis,
					check_era,
					check_nonce,
					check_weight,
					payment,
				);
				let raw_payload = SignedPayload::from_raw(
					function,
					extra,
					(spec_version, transaction_version, genesis_hash, genesis_hash, (), (), ()),
				);
				let signature = raw_payload.using_encoded(|payload| signer.sign(payload));
				let (function, extra, _) = raw_payload.deconstruct();
				index += 1;
				UncheckedExtrinsic::new_signed(function, from.into(), signature.into(), extra)
					.into()
			},
		);
	}

	#[test]
	#[ignore]
	fn test_consensus() {
		sc_service_test::consensus(
			crate::chain_spec::tests::integration_test_config_with_two_authorities(),
			|config| {
				let NewFullBase { task_manager, client, network, transaction_pool, .. } =
					new_full_base(config, |_, _| ())?;
				Ok(sc_service_test::TestNetComponents::new(
					task_manager,
					client,
					network,
					transaction_pool,
				))
			},
			|config| {
				let (keep_alive, _, client, network, transaction_pool) = new_light_base(config)?;
				Ok(sc_service_test::TestNetComponents::new(
					keep_alive,
					client,
					network,
					transaction_pool,
				))
			},
			vec!["//Alice".into(), "//Bob".into()],
		)
	}
}
