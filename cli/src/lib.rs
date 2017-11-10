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

#[macro_use]
extern crate clap;
#[macro_use]
extern crate log;

/// Parse command line arguments and start the node.
pub fn main() {
	let yaml = load_yaml!("./cli.yml");
	let matches = clap::App::from_yaml(yaml).get_matches();

	let log_pattern = matches.value_of("log").unwrap_or("");
	init_logger(log_pattern);

	if let Some(_) = matches.subcommand_matches("collator") {
		info!("Starting collator.");
		return;
	}

	if let Some(_) = matches.subcommand_matches("validator") {
		info!("Starting validator.");
		return;
	}

	println!("No command given.\n");
	let _ = clap::App::from_yaml(yaml).print_long_help();
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
