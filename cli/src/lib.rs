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
extern crate polkadot_client as client;
extern crate polkadot_executor as executor;
extern crate polkadot_primitives as primitives;
extern crate polkadot_rpc_servers as rpc;

#[macro_use]
extern crate clap;
#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate log;

pub mod error;

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
	let executor = executor::executor();
	let client = client::new_in_mem(executor)?;

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

