// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Substrate Demo CLI library.

#![warn(missing_docs)]

extern crate ctrlc;
extern crate ed25519;
extern crate env_logger;
extern crate futures;
extern crate tokio;
extern crate triehash;
extern crate substrate_client as client;
extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;
extern crate substrate_rpc;
extern crate substrate_rpc_servers as rpc;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_state_machine as state_machine;
extern crate substrate_extrinsic_pool as extrinsic_pool;
extern crate demo_executor;
extern crate demo_primitives;
extern crate demo_runtime;

#[macro_use]
extern crate hex_literal;
#[macro_use]
extern crate clap;
#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate log;

pub mod error;

use std::sync::Arc;
use demo_primitives::Hash;
use demo_runtime::{Block, BlockId, UncheckedExtrinsic, GenesisConfig,
	ConsensusConfig, CouncilConfig, DemocracyConfig, SessionConfig, StakingConfig,
	TimestampConfig};
use futures::{Future, Sink, Stream};
use tokio::runtime::Runtime;
use demo_executor::NativeExecutor;

struct DummyPool;
impl extrinsic_pool::api::ExtrinsicPool<UncheckedExtrinsic, BlockId, Hash> for DummyPool {
	type Error = extrinsic_pool::txpool::Error;

	fn submit(&self, _block: BlockId, _: Vec<UncheckedExtrinsic>)
		-> Result<Vec<Hash>, Self::Error>
	{
		Err("unimplemented".into())
	}

	fn submit_and_watch(&self, _block: BlockId, _: UncheckedExtrinsic)
		-> Result<extrinsic_pool::watcher::Watcher<Hash>, Self::Error>
	{
		Err("unimplemented".into())
	}

	fn light_status(&self) -> extrinsic_pool::txpool::LightStatus {
		unreachable!()
	}

	fn import_notification_stream(&self) -> extrinsic_pool::api::EventStream {
		unreachable!()
	}
}

struct DummySystem;
impl substrate_rpc::system::SystemApi for DummySystem {
	fn system_name(&self) -> substrate_rpc::system::error::Result<String> {
		Ok("substrate-demo".into())
	}
	fn system_version(&self) -> substrate_rpc::system::error::Result<String> {
		Ok(crate_version!().into())
	}
	fn system_chain(&self) -> substrate_rpc::system::error::Result<String> {
		Ok("default".into())
	}
}

/// Parse command line arguments and start the node.
///
/// IANA unassigned port ranges that we could use:
/// 6717-6766		Unassigned
/// 8504-8553		Unassigned
/// 9556-9591		Unassigned
/// 9803-9874		Unassigned
/// 9926-9949		Unassigned
pub fn run<I, T>(args: I) -> error::Result<()> where
	I: IntoIterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
{
	let yaml = load_yaml!("./cli.yml");
	let matches = clap::App::from_yaml(yaml).version(crate_version!()).get_matches_from_safe(args)?;

	// TODO [ToDr] Split parameters parsing from actual execution.
	let log_pattern = matches.value_of("log").unwrap_or("");
	init_logger(log_pattern);

	// Create client
	let executor = NativeExecutor::with_heap_pages(8);

	let god_key = hex!["3d866ec8a9190c8343c2fc593d21d8a6d0c5c4763aaab2349de3a6111d64d124"];
	let genesis_config = GenesisConfig {
		consensus: Some(ConsensusConfig {
			code: vec![],	// TODO
			authorities: vec![god_key.clone().into()],
		}),
		system: None,
		session: Some(SessionConfig {
			validators: vec![god_key.clone().into()],
			session_length: 720,	// that's 1 hour per session.
			broken_percent_late: 30,
		}),
		staking: Some(StakingConfig {
			current_era: 0,
			intentions: vec![],
			transaction_base_fee: 100,
			transaction_byte_fee: 1,
			transfer_fee: 0,
			creation_fee: 0,
			reclaim_rebate: 0,
			existential_deposit: 500,
			balances: vec![(god_key.clone().into(), 1u64 << 63)].into_iter().collect(),
			validator_count: 12,
			sessions_per_era: 24,	// 24 hours per era.
			bonding_duration: 90,	// 90 days per bond.
			early_era_slash: 10000,
			session_reward: 100,
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
		timestamp: Some(TimestampConfig {
			period: 5,					// 5 second block time.
		}),
	};

	let client = Arc::new(client::new_in_mem::<NativeExecutor<demo_executor::Executor>, Block, _>(executor, genesis_config)?);
	let mut runtime = Runtime::new()?;
	let _rpc_servers = {
		let handler = || {
			let chain = rpc::apis::chain::Chain::new(client.clone(), runtime.executor());
			let author = rpc::apis::author::Author::new(client.clone(), Arc::new(DummyPool), runtime.executor());
			rpc::rpc_handler::<Block, _, _, _, _>(client.clone(), chain, author, DummySystem)
		};
		let http_address = "127.0.0.1:9933".parse().unwrap();
		let ws_address = "127.0.0.1:9944".parse().unwrap();

		(
			rpc::start_http(&http_address, handler())?,
			rpc::start_ws(&ws_address, handler())?
		)
	};

	if let Some(_) = matches.subcommand_matches("validator") {
		info!("Starting validator.");
		let (exit_send, exit) = futures::sync::mpsc::channel(1);
		ctrlc::CtrlC::set_handler(move || {
			exit_send.clone().send(()).wait().expect("Error sending exit notification");
		});

		runtime.block_on(exit.into_future()).expect("Error running informant event loop");
		return Ok(())
	}

	println!("No command given.\n");
	let _ = clap::App::from_yaml(yaml).print_long_help();

	Ok(())
}

fn init_logger(pattern: &str) {
	let mut builder = env_logger::LogBuilder::new();
	// Disable info logging by default for some modules:
	builder.filter(Some("hyper"), log::LogLevelFilter::Warn);
	// Enable info for others.
	builder.filter(None, log::LogLevelFilter::Info);

	if let Ok(lvl) = std::env::var("RUST_LOG") {
		builder.parse(&lvl);
	}

	builder.parse(pattern);


	builder.init().expect("Logger initialized only once.");
}
