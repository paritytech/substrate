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
extern crate parking_lot;
extern crate tokio_timer;
extern crate polkadot_primitives;
extern crate polkadot_runtime;
extern crate polkadot_executor;
extern crate polkadot_api;
extern crate polkadot_consensus as consensus;
extern crate polkadot_transaction_pool as transaction_pool;
extern crate polkadot_keystore as keystore;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;
extern crate substrate_network as network;
extern crate substrate_codec as codec;
extern crate substrate_executor;

extern crate tokio_core;
extern crate substrate_client as client;

#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate log;
#[macro_use]
extern crate hex_literal;

mod error;
mod config;

use std::sync::Arc;
use std::thread;
use futures::prelude::*;
use parking_lot::Mutex;
use tokio_core::reactor::Core;
use codec::Slicable;
use primitives::block::{Id as BlockId, Extrinsic, ExtrinsicHash, HeaderHash};
use primitives::hashing;
use transaction_pool::TransactionPool;
use substrate_executor::NativeExecutor;
use polkadot_executor::Executor as LocalDispatch;
use keystore::Store as Keystore;
use polkadot_api::PolkadotApi;
use polkadot_runtime::{GenesisConfig, ConsensusConfig, CouncilConfig, DemocracyConfig,
	SessionConfig, StakingConfig, BuildExternalities};
use client::{genesis, BlockchainEvents};
use client::in_mem::Backend as InMemory;
use network::ManageNetwork;

pub use self::error::{ErrorKind, Error};
pub use config::{Configuration, Role, ChainSpec};

type Client = client::Client<InMemory, NativeExecutor<LocalDispatch>>;

/// Polkadot service.
pub struct Service {
	thread: Option<thread::JoinHandle<()>>,
	client: Arc<Client>,
	network: Arc<network::Service>,
	transaction_pool: Arc<Mutex<TransactionPool>>,
	_consensus: Option<consensus::Service>,
}

struct TransactionPoolAdapter {
	pool: Arc<Mutex<TransactionPool>>,
	client: Arc<Client>,
}

impl network::TransactionPool for TransactionPoolAdapter {
	fn transactions(&self) -> Vec<(ExtrinsicHash, Vec<u8>)> {
		let best_block = match self.client.info() {
			Ok(info) => info.chain.best_hash,
			Err(e) => {
				debug!("Error getting best block: {:?}", e);
				return Vec::new();
			}
		};
		let id = self.client.check_id(BlockId::Hash(best_block)).expect("Best block is always valid; qed.");
		let ready = transaction_pool::Ready::create(id, &*self.client);
		self.pool.lock().pending(ready).map(|t| {
			let hash = ::primitives::Hash::from(&t.hash()[..]);
			let tx = codec::Slicable::encode(t.as_transaction());
			(hash, tx)
		}).collect()
	}

	fn import(&self, transaction: &[u8]) -> Option<ExtrinsicHash> {
		if let Some(tx) = codec::Slicable::decode(&mut &transaction[..]) {
			match self.pool.lock().import(tx) {
				Ok(t) => Some(t.hash()[..].into()),
				Err(e) => match *e.kind() {
					transaction_pool::ErrorKind::AlreadyImported(hash) => Some(hash[..].into()),
					_ => {
						debug!("Error adding transaction to the pool: {:?}", e);
						None
					},
				}
			}
		} else {
			debug!("Error decoding transaction");
			None
		}
	}
}

pub struct ChainConfig {
	genesis_config: GenesisConfig,
	boot_nodes: Vec<String>,
}

fn poc_1_testnet_config() -> ChainConfig {
	let initial_authorities = vec![
		hex!["82c39b31a2b79a90f8e66e7a77fdb85a4ed5517f2ae39f6a80565e8ecae85cf5"].into(),
		hex!["4de37a07567ebcbf8c64568428a835269a566723687058e017b6d69db00a77e7"].into(),
		hex!["063d7787ebca768b7445dfebe7d62cbb1625ff4dba288ea34488da266dd6dca5"].into(),
	];
	let endowed_accounts = vec![
		hex!["24d132eb1a4cbf8e46de22652019f1e07fadd5037a6a057c75dbbfd4641ba85d"].into(),
	];
	let genesis_config = GenesisConfig {
		consensus: Some(ConsensusConfig {
			code: include_bytes!("../../runtime/wasm/genesis.wasm").to_vec(),	// TODO change
			authorities: initial_authorities.clone(),
		}),
		system: None,
		session: Some(SessionConfig {
			validators: initial_authorities.clone(),
			session_length: 720,	// that's 1 hour per session.
		}),
		staking: Some(StakingConfig {
			current_era: 0,
			intentions: vec![],
			transaction_fee: 100,
			balances: endowed_accounts.iter().map(|&k|(k, 1u64 << 60)).collect(),
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
	let boot_nodes = Vec::new();
	ChainConfig { genesis_config, boot_nodes }
}

fn local_testnet_config() -> ChainConfig {
	let initial_authorities = vec![
		ed25519::Pair::from_seed(b"Alice                           ").public().into(),
		ed25519::Pair::from_seed(b"Bob                             ").public().into(),
	];
	let endowed_accounts = vec![
		ed25519::Pair::from_seed(b"Alice                           ").public().into(),
		ed25519::Pair::from_seed(b"Bob                             ").public().into(),
		ed25519::Pair::from_seed(b"Charlie                         ").public().into(),
		ed25519::Pair::from_seed(b"Dave                            ").public().into(),
		ed25519::Pair::from_seed(b"Eve                             ").public().into(),
		ed25519::Pair::from_seed(b"Ferdie                          ").public().into(),
	];
	let genesis_config = GenesisConfig {
		consensus: Some(ConsensusConfig {
			code: include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.compact.wasm").to_vec(),
			authorities: initial_authorities.clone(),
		}),
		system: None,
		session: Some(SessionConfig {
			validators: initial_authorities.clone(),
			session_length: 10,
		}),
		staking: Some(StakingConfig {
			current_era: 0,
			intentions: vec![],
			transaction_fee: 1,
			balances: endowed_accounts.iter().map(|&k|(k, 1u64 << 60)).collect(),
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
			active_council: vec![],
			candidacy_bond: 10,
			voter_bond: 2,
			present_slash_per_voter: 1,
			carry_count: 4,
			presentation_duration: 10,
			approval_voting_period: 20,
			term_duration: 40,
			desired_seats: 0,
			inactive_grace_period: 1,

			cooloff_period: 75,
			voting_period: 20,
		}),
		parachains: Some(Default::default()),
	};
	let boot_nodes = Vec::new();
	ChainConfig { genesis_config, boot_nodes }
}

impl Service {
	/// Creates and register protocol with the network service
	pub fn new(mut config: Configuration) -> Result<Service, error::Error> {
		// Create client
		let executor = polkadot_executor::Executor::new();
		let mut storage = Default::default();

		let mut keystore = Keystore::open(config.keystore_path.into())?;
		for seed in &config.keys {
			keystore.generate_from_seed(seed)?;
		}

		if keystore.contents()?.is_empty() {
			let key = keystore.generate("")?;
			info!("Generated a new keypair: {:?}", key.public());
		}

		let ChainConfig { genesis_config, boot_nodes } = match config.chain_spec {
			ChainSpec::Development => local_testnet_config(),
			ChainSpec::PoC1Testnet => poc_1_testnet_config(),
		};
		config.network.boot_nodes.extend(boot_nodes);

		let prepare_genesis = || {
			storage = genesis_config.build_externalities();
			let block = genesis::construct_genesis_block(&storage);
			(primitives::block::Header::decode(&mut block.header.encode().as_ref()).expect("to_vec() always gives a valid serialisation; qed"), storage.into_iter().collect())
		};

		let client = Arc::new(client::new_in_mem(executor, prepare_genesis)?);
		let best_header = client.best_block_header()?;
		info!("Starting Polkadot. Best block is #{}", best_header.number);
		let transaction_pool = Arc::new(Mutex::new(TransactionPool::new(config.transaction_pool)));
		let transaction_pool_adapter = Arc::new(TransactionPoolAdapter {
			pool: transaction_pool.clone(),
			client: client.clone(),
		});
		let network_params = network::Params {
			config: network::ProtocolConfig {
				roles: config.roles,
			},
			network_config: config.network,
			chain: client.clone(),
			transaction_pool: transaction_pool_adapter,
		};
		let network = network::Service::new(network_params)?;

		// Spin consensus service if configured
		let consensus_service = if config.roles & Role::VALIDATOR == Role::VALIDATOR {
			// Load the first available key. Code above makes sure it exisis.
			let key = keystore.load(&keystore.contents()?[0], "")?;
			info!("Using authority key {:?}", key.public());
			Some(consensus::Service::new(client.clone(), network.clone(), transaction_pool.clone(), key))
		} else {
			None
		};

		let thread_client = client.clone();
		let thread_network = network.clone();
		let thread_txpool = transaction_pool.clone();
		let thread = thread::spawn(move || {
			thread_network.start_network();
			let mut core = Core::new().expect("tokio::Core could not be created");
			let events = thread_client.import_notification_stream().for_each(|notification| {
				thread_network.on_block_imported(notification.hash, &notification.header);
				prune_imported(&*thread_client, &*thread_txpool, notification.hash);

				Ok(())
			});
			if let Err(e) = core.run(events) {
				debug!("Polkadot service event loop shutdown with {:?}", e);
			}
			debug!("Polkadot service shutdown");
		});
		Ok(Service {
			thread: Some(thread),
			client: client,
			network: network,
			transaction_pool: transaction_pool,
			_consensus: consensus_service,
		})
	}

	/// Get shared client instance.
	pub fn client(&self) -> Arc<Client> {
		self.client.clone()
	}

	/// Get shared network instance.
	pub fn network(&self) -> Arc<network::Service> {
		self.network.clone()
	}

	/// Get shared transaction pool instance.
	pub fn transaction_pool(&self) -> Arc<Mutex<TransactionPool>> {
		self.transaction_pool.clone()
	}
}

fn prune_transactions(pool: &mut TransactionPool, extrinsics: &[Extrinsic]) {
	for extrinsic in extrinsics {
		let hash: _ = hashing::blake2_256(&extrinsic.encode()).into();
		pool.remove(&hash, true);
	}
}

/// Produce a task which prunes any finalized transactions from the pool.
pub fn prune_imported(client: &Client, pool: &Mutex<TransactionPool>, hash: HeaderHash) {
	let id = BlockId::Hash(hash);
	match client.body(&id) {
		Ok(Some(body)) => prune_transactions(&mut *pool.lock(), &body[..]),
		Ok(None) => warn!("Missing imported block {:?}", hash),
		Err(e) => warn!("Failed to fetch block: {:?}", e),
	}
}

impl Drop for Service {
	fn drop(&mut self) {
		self.client.stop_notifications();
		self.network.stop_network();
		if let Some(thread) = self.thread.take() {
			thread.join().expect("The service thread has panicked");
		}
	}
}
