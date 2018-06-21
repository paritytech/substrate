// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Polkadot service. Starts a thread that spins the network, the client and the transaction pool.
//! Manages communication between them.

extern crate futures;
extern crate ed25519;
extern crate clap;
extern crate exit_future;
extern crate tokio_timer;
extern crate polkadot_primitives;
extern crate polkadot_runtime;
extern crate polkadot_executor;
extern crate polkadot_api;
extern crate polkadot_consensus as consensus;
extern crate polkadot_transaction_pool as transaction_pool;
extern crate substrate_keystore as keystore;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;
extern crate substrate_network as network;
extern crate substrate_codec as codec;
extern crate substrate_executor;
extern crate substrate_state_machine as state_machine;

extern crate tokio_core;
extern crate substrate_client as client;
extern crate substrate_client_db as client_db;

#[macro_use]
extern crate substrate_telemetry;
#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate slog;	// needed until we can reexport `slog_info` from `substrate_telemetry`
#[macro_use]
extern crate log;
#[macro_use]
extern crate hex_literal;

mod components;
mod error;
mod config;

use std::sync::Arc;
use std::thread;
use futures::prelude::*;
use tokio_core::reactor::Core;
use primitives::AuthorityId;
use transaction_pool::TransactionPool;
use keystore::Store as Keystore;
use polkadot_api::PolkadotApi;
use polkadot_primitives::{Block, BlockId, Hash};
use polkadot_runtime::{GenesisConfig, ConsensusConfig, CouncilConfig, DemocracyConfig,
	SessionConfig, StakingConfig};
use client::{Client, BlockchainEvents};
use network::ManageNetwork;
use exit_future::Signal;

pub use self::error::{ErrorKind, Error};
pub use self::components::{Components, FullComponents, LightComponents};
pub use config::{Configuration, Role, OptionChainSpec, ChainSpec};

/// Polkadot service.
pub struct Service<Components: components::Components> {
	thread: Option<thread::JoinHandle<()>>,
	client: Arc<Client<Components::Backend, Components::Executor, Block>>,
	network: Arc<network::Service<Block>>,
	transaction_pool: Arc<TransactionPool>,
	signal: Option<Signal>,
	_consensus: Option<consensus::Service>,
}

pub struct ChainConfig {
	genesis_config: GenesisConfig,
	boot_nodes: Vec<String>,
}

fn poc_2_testnet_config() -> ChainConfig {
	let initial_authorities = vec![
		hex!["82c39b31a2b79a90f8e66e7a77fdb85a4ed5517f2ae39f6a80565e8ecae85cf5"].into(),
		hex!["4de37a07567ebcbf8c64568428a835269a566723687058e017b6d69db00a77e7"].into(),
		hex!["063d7787ebca768b7445dfebe7d62cbb1625ff4dba288ea34488da266dd6dca5"].into(),
		hex!["8101764f45778d4980dadaceee6e8af2517d3ab91ac9bec9cd1714fa5994081c"].into(),
	];
	let endowed_accounts = vec![
		hex!["f295940fa750df68a686fcf4abd4111c8a9c5a5a5a83c4c8639c451a94a7adfd"].into(),
	];
	let genesis_config = GenesisConfig {
		consensus: Some(ConsensusConfig {
			code: include_bytes!("../../runtime/wasm/genesis.wasm").to_vec(),	// TODO change
			authorities: initial_authorities.clone(),
		}),
		system: None,
		session: Some(SessionConfig {
			validators: initial_authorities.iter().cloned().map(Into::into).collect(),
			session_length: 720,	// that's 1 hour per session.
		}),
		staking: Some(StakingConfig {
			current_era: 0,
			intentions: initial_authorities.iter().cloned().map(Into::into).collect(),
			transaction_base_fee: 100,
			transaction_byte_fee: 1,
			existential_deposit: 500,
			transfer_fee: 0,
			creation_fee: 0,
			contract_fee: 0,
			reclaim_rebate: 0,
			balances: endowed_accounts.iter().map(|&k|(k, 1u128 << 60)).collect(),
			validator_count: 12,
			sessions_per_era: 24,	// 24 hours per era.
			bonding_duration: 90,	// 90 days per bond.
		}),
		democracy: Some(DemocracyConfig {
			launch_period: 120 * 24 * 14,	// 2 weeks per public referendum
			voting_period: 120 * 24 * 28,	// 4 weeks to discuss & vote on an active referendum
			minimum_deposit: 1000,	// 1000 as the minimum deposit for a referendum
		}),
		council: Some(CouncilConfig {
			active_council: vec![],
			candidacy_bond: 1000,	// 1000 to become a council candidate
			voter_bond: 100,		// 100 down to vote for a candidate
			present_slash_per_voter: 1,	// slash by 1 per voter for an invalid presentation.
			carry_count: 24,		// carry over the 24 runners-up to the next council election
			presentation_duration: 120 * 24,	// one day for presenting winners.
			approval_voting_period: 7 * 120 * 24,	// one week period between possible council elections.
			term_duration: 180 * 120 * 24,	// 180 day term duration for the council.
			desired_seats: 0, // start with no council: we'll raise this once the stake has been dispersed a bit.
			inactive_grace_period: 1,	// one addition vote should go by before an inactive voter can be reaped.

			cooloff_period: 90 * 120 * 24, // 90 day cooling off period if council member vetoes a proposal.
			voting_period: 7 * 120 * 24, // 7 day voting period for council members.
		}),
		parachains: Some(Default::default()),
	};
	let boot_nodes = vec![
		"enode://a93a29fa68d965452bf0ff8c1910f5992fe2273a72a1ee8d3a3482f68512a61974211ba32bb33f051ceb1530b8ba3527fc36224ba6b9910329025e6d9153cf50@104.211.54.233:30333".into(),
		"enode://051b18f63a316c4c5fef4631f8c550ae0adba179153588406fac3e5bbbbf534ebeda1bf475dceda27a531f6cdef3846ab6a010a269aa643a1fec7bff51af66bd@104.211.48.51:30333".into(),
		"enode://c831ec9011d2c02d2c4620fc88db6d897a40d2f88fd75f47b9e4cf3b243999acb6f01b7b7343474650b34eeb1363041a422a91f1fc3850e43482983ee15aa582@104.211.48.247:30333".into(),
	];
	ChainConfig { genesis_config, boot_nodes }
}

fn testnet_config(initial_authorities: Vec<AuthorityId>) -> ChainConfig {
	let endowed_accounts = vec![
		ed25519::Pair::from_seed(b"Alice                           ").public().0.into(),
		ed25519::Pair::from_seed(b"Bob                             ").public().0.into(),
		ed25519::Pair::from_seed(b"Charlie                         ").public().0.into(),
		ed25519::Pair::from_seed(b"Dave                            ").public().0.into(),
		ed25519::Pair::from_seed(b"Eve                             ").public().0.into(),
		ed25519::Pair::from_seed(b"Ferdie                          ").public().0.into(),
	];
	let genesis_config = GenesisConfig {
		consensus: Some(ConsensusConfig {
			code: include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.compact.wasm").to_vec(),
			authorities: initial_authorities.clone(),
		}),
		system: None,
		session: Some(SessionConfig {
			validators: initial_authorities.iter().cloned().map(Into::into).collect(),
			session_length: 10,
		}),
		staking: Some(StakingConfig {
			current_era: 0,
			intentions: initial_authorities.iter().cloned().map(Into::into).collect(),
			transaction_base_fee: 1,
			transaction_byte_fee: 0,
			existential_deposit: 500,
			transfer_fee: 0,
			creation_fee: 0,
			contract_fee: 0,
			reclaim_rebate: 0,
			balances: endowed_accounts.iter().map(|&k|(k, (1u128 << 60))).collect(),
			validator_count: 2,
			sessions_per_era: 5,
			bonding_duration: 2,
		}),
		democracy: Some(DemocracyConfig {
			launch_period: 9,
			voting_period: 18,
			minimum_deposit: 10,
		}),
		council: Some(CouncilConfig {
			active_council: endowed_accounts.iter().filter(|a| initial_authorities.iter().find(|&b| &a.0 == b).is_none()).map(|a| (a.clone(), 1000000)).collect(),
			candidacy_bond: 10,
			voter_bond: 2,
			present_slash_per_voter: 1,
			carry_count: 4,
			presentation_duration: 10,
			approval_voting_period: 20,
			term_duration: 1000000,
			desired_seats: (endowed_accounts.len() - initial_authorities.len()) as u32,
			inactive_grace_period: 1,

			cooloff_period: 75,
			voting_period: 20,
		}),
		parachains: Some(Default::default()),
	};
	let boot_nodes = Vec::new();
	ChainConfig { genesis_config, boot_nodes }
}

fn development_config() -> ChainConfig {
	testnet_config(vec![
		ed25519::Pair::from_seed(b"Alice                           ").public().into(),
	])
}

fn local_testnet_config() -> ChainConfig {
	testnet_config(vec![
		ed25519::Pair::from_seed(b"Alice                           ").public().into(),
		ed25519::Pair::from_seed(b"Bob                             ").public().into(),
	])
}

/// Creates light client and register protocol with the network service
pub fn new_light(config: Configuration) -> Result<Service<components::LightComponents>, error::Error> {
	Service::new(components::LightComponents, config)
}

/// Creates full client and register protocol with the network service
pub fn new_full(config: Configuration) -> Result<Service<components::FullComponents>, error::Error> {
	let is_validator = (config.roles & Role::VALIDATOR) == Role::VALIDATOR;
	Service::new(components::FullComponents { is_validator }, config)
}

impl<Components> Service<Components>
	where
		Components: components::Components,
		client::error::Error: From<<<<Components as components::Components>::Backend as client::backend::Backend<Block>>::State as state_machine::Backend>::Error>,
{
	/// Creates and register protocol with the network service
	fn new(components: Components, mut config: Configuration) -> Result<Self, error::Error> {
		use std::sync::Barrier;

		let (signal, exit) = ::exit_future::signal();

		// Create client
		let executor = polkadot_executor::Executor::new();

		let mut keystore = Keystore::open(config.keystore_path.into())?;
		for seed in &config.keys {
			keystore.generate_from_seed(seed)?;
		}

		if keystore.contents()?.is_empty() {
			let key = keystore.generate("")?;
			info!("Generated a new keypair: {:?}", key.public());
		}

		let ChainConfig { genesis_config, boot_nodes } = match config.chain_spec {
			ChainSpec::Development => development_config(),
			ChainSpec::LocalTestnet => local_testnet_config(),
			ChainSpec::PoC2Testnet => poc_2_testnet_config(),
		};
		config.network.boot_nodes.extend(boot_nodes);

		let genesis_builder = components::GenesisBuilder {
			config: genesis_config,
		};

		let db_settings = client_db::DatabaseSettings {
			cache_size: None,
			path: config.database_path.into(),
		};

		let (client, on_demand) = components.build_client(db_settings, executor, genesis_builder)?;
		let api = components.build_api(client.clone());
		let best_header = client.best_block_header()?;

		info!("Best block is #{}", best_header.number);
		telemetry!("node.start"; "height" => best_header.number, "best" => ?best_header.hash());

		let transaction_pool = Arc::new(TransactionPool::new(config.transaction_pool));
		let transaction_pool_adapter = components.build_network_tx_pool(client.clone(), api.clone(), transaction_pool.clone());
		let network_params = network::Params {
			config: network::ProtocolConfig {
				roles: config.roles,
			},
			network_config: config.network,
			chain: client.clone(),
			on_demand: on_demand.clone().map(|d| d as Arc<network::OnDemandService>),
			transaction_pool: transaction_pool_adapter,
		};
		let network = network::Service::new(network_params)?;
		let barrier = ::std::sync::Arc::new(Barrier::new(2));
		on_demand.map(|on_demand| on_demand.set_service_link(Arc::downgrade(&network)));


		let thread = {
			let client = client.clone();
			let network = network.clone();
			let txpool = transaction_pool.clone();

			let thread_barrier = barrier.clone();
			thread::spawn(move || {
				network.start_network();

				thread_barrier.wait();
				let mut core = Core::new().expect("tokio::Core could not be created");

				// block notifications
				let network1 = network.clone();
				let txpool1 = txpool.clone();

				let events = client.import_notification_stream()
					.for_each(move |notification| {
						network1.on_block_imported(notification.hash, &notification.header);
						prune_imported(&*api, &*txpool1, notification.hash);
						Ok(())
					});
				core.handle().spawn(events);

				// transaction notifications
				let events = txpool.import_notification_stream()
					// TODO [ToDr] Consider throttling?
					.for_each(move |_| {
						network.trigger_repropagate();
						Ok(())
					});
				core.handle().spawn(events);

				if let Err(e) = core.run(exit) {
					debug!("Polkadot service event loop shutdown with {:?}", e);
				}
				debug!("Polkadot service shutdown");
			})
		};

		// wait for the network to start up before starting the consensus
		// service.
		barrier.wait();

		// Spin consensus service if configured
		let consensus_service = components.build_consensus(client.clone(), network.clone(), transaction_pool.clone(), &keystore)?;

		Ok(Service {
			thread: Some(thread),
			client: client,
			network: network,
			transaction_pool: transaction_pool,
			signal: Some(signal),
			_consensus: consensus_service,
		})
	}

	/// Get shared client instance.
	pub fn client(&self) -> Arc<Client<Components::Backend, Components::Executor, Block>> {
		self.client.clone()
	}

	/// Get shared network instance.
	pub fn network(&self) -> Arc<network::Service<Block>> {
		self.network.clone()
	}

	/// Get shared transaction pool instance.
	pub fn transaction_pool(&self) -> Arc<TransactionPool> {
		self.transaction_pool.clone()
	}
}

/// Produce a task which prunes any finalized transactions from the pool.
pub fn prune_imported<A>(api: &A, pool: &TransactionPool, hash: Hash)
	where
		A: PolkadotApi,
{
	match api.check_id(BlockId::hash(hash)) {
		Ok(id) => {
			let ready = transaction_pool::Ready::create(id, api);
			pool.cull(None, ready);
		},
		Err(e) => warn!("Failed to check block id: {:?}", e),
	}
}

impl<Components> Drop for Service<Components> where Components: components::Components {
	fn drop(&mut self) {
		self.network.stop_network();

		if let Some(signal) = self.signal.take() {
			signal.fire();
		}

		if let Some(thread) = self.thread.take() {
			thread.join().expect("The service thread has panicked");
		}
	}
}
