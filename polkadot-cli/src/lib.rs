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

//! Polkadot CLI library.

#![warn(missing_docs)]

extern crate env_logger;
extern crate ed25519;
extern crate triehash;
extern crate substrate_codec as codec;
extern crate substrate_state_machine as state_machine;
extern crate substrate_client as client;
extern crate substrate_primitives as primitives;
extern crate substrate_rpc_servers as rpc;
extern crate polkadot_primitives;
extern crate polkadot_executor;
extern crate polkadot_runtime;

#[macro_use]
extern crate hex_literal;
#[macro_use]
extern crate clap;
#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate log;

mod genesis;
pub mod error;

use codec::Slicable;
use polkadot_runtime::genesismap::{additional_storage_with_genesis, GenesisConfig};

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
	let executor = polkadot_executor::executor();
	let mut storage = Default::default();
	let god_key = hex!["3d866ec8a9190c8343c2fc593d21d8a6d0c5c4763aaab2349de3a6111d64d124"];

	let genesis_config = GenesisConfig {
		validators: vec![god_key.clone()],
		authorities: vec![god_key.clone()],
		balances: vec![(god_key.clone(), 1u64 << 63)].into_iter().collect(),
		block_time: 5,			// 5 second block time.
		session_length: 720,	// that's 1 hour per session.
		sessions_per_era: 24,	// 24 hours per era.
		bonding_duration: 90,	// 90 days per bond.
		approval_ratio: 667,	// 66.7% approvals required for legislation.
	};
	let prepare_genesis = || {
		storage = genesis_config.genesis_map();
		let block = genesis::construct_genesis_block(&storage);
		storage.extend(additional_storage_with_genesis(&block));
		(primitives::block::Header::from_slice(&mut block.header.to_vec().as_ref()).expect("to_vec() always gives a valid serialisation; qed"), storage.into_iter().collect())
	};
	let client = client::new_in_mem(executor, prepare_genesis)?;

	let address = "127.0.0.1:9933".parse().unwrap();
	let handler = rpc::rpc_handler(client);
	let server = rpc::start_http(&address, handler)?;

	if let Some(_) = matches.subcommand_matches("collator") {
		info!("Starting collator.");
		server.wait();
		return Ok(());
	}

	if let Some(_) = matches.subcommand_matches("validator") {
		info!("Starting validator.");
		server.wait();
		return Ok(());
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
