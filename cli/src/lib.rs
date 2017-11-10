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

extern crate clap;
extern crate env_logger;
extern crate log;

use clap::{Arg, App, SubCommand};

pub fn main() {
	let matches = App::new("Polkadot")
		.arg(Arg::with_name("log")
			.short("l")
			.value_name("LOG")
			.help("Sets logging.")
			.takes_value(true))
		.subcommand(SubCommand::with_name("collator"))
		.subcommand(SubCommand::with_name("validator"))
		.get_matches();

	let log_pattern = matches.value_of("log").unwrap_or("");
	init_logger(log_pattern);

	if let Some(_) = matches.subcommand_matches("collator") {
		println!("Running collator.");
		return;
	}

	if let Some(_) = matches.subcommand_matches("validator") {
		println!("Running collator.");
		return;
	}
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
