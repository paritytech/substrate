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

extern crate app_dirs;
extern crate env_logger;
extern crate atty;
extern crate ansi_term;
extern crate regex;
extern crate time;
extern crate futures;
extern crate tokio_core;
extern crate ctrlc;
extern crate fdlimit;
extern crate ed25519;
extern crate triehash;
extern crate parking_lot;
extern crate serde;
extern crate serde_json;

extern crate substrate_client as client;
extern crate substrate_network as network;
extern crate substrate_primitives;
extern crate substrate_rpc;
extern crate substrate_rpc_servers as rpc;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_state_machine as state_machine;
extern crate polkadot_primitives;
extern crate polkadot_runtime;
extern crate polkadot_service as service;
#[macro_use]
extern crate slog;	// needed until we can reexport `slog_info` from `substrate_telemetry`
#[macro_use]
extern crate substrate_telemetry;
extern crate polkadot_transaction_pool as txpool;

#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate clap;
#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate log;
#[macro_use]
extern crate hex_literal;

pub mod error;
mod informant;
mod chain_spec;
mod preset_config;

pub use chain_spec::ChainSpec;
pub use preset_config::PresetConfig;

use std::io;
use std::fs::File;
use std::net::SocketAddr;
use std::path::{Path, PathBuf};
use std::collections::HashMap;
use substrate_primitives::hexdisplay::HexDisplay;
use substrate_primitives::storage::{StorageData, StorageKey};
use substrate_telemetry::{init_telemetry, TelemetryConfig};
use runtime_primitives::StorageMap;
use polkadot_primitives::Block;

use futures::sync::mpsc;
use futures::{Sink, Future, Stream};
use tokio_core::reactor;

const DEFAULT_TELEMETRY_URL: &str = "ws://telemetry.polkadot.io:1024";

#[derive(Clone)]
struct SystemConfiguration {
	chain_name: String,
}

impl substrate_rpc::system::SystemApi for SystemConfiguration {
	fn system_name(&self) -> substrate_rpc::system::error::Result<String> {
		Ok("parity-polkadot".into())
	}

	fn system_version(&self) -> substrate_rpc::system::error::Result<String> {
		Ok(crate_version!().into())
	}

	fn system_chain(&self) -> substrate_rpc::system::error::Result<String> {
		Ok(self.chain_name.clone())
	}
}

fn read_storage_json(filename: &str) -> Option<StorageMap> {
	let file = File::open(PathBuf::from(filename)).ok()?;
	let h: HashMap<StorageKey, StorageData> = ::serde_json::from_reader(&file).ok()?;
	Some(h.into_iter().map(|(k, v)| (k.0, v.0)).collect())
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
	let core = reactor::Core::new().expect("tokio::Core could not be created");

	let yaml = load_yaml!("./cli.yml");
	let matches = match clap::App::from_yaml(yaml).version(&(crate_version!().to_owned() + "\n")[..]).get_matches_from_safe(args) {
		Ok(m) => m,
		Err(ref e) if e.kind == clap::ErrorKind::VersionDisplayed => return Ok(()),
		Err(ref e) if e.kind == clap::ErrorKind::HelpDisplayed => {
			let _ = clap::App::from_yaml(yaml).print_long_help();
			return Ok(())
		}
		Err(e) => return Err(e.into()),
	};

	// TODO [ToDr] Split parameters parsing from actual execution.
	let log_pattern = matches.value_of("log").unwrap_or("");
	init_logger(log_pattern);
	fdlimit::raise_fd_limit();

	info!("Parity ·:· Polkadot");
	info!("  version {}", crate_version!());
	info!("  by Parity Technologies, 2017, 2018");

	let mut config = service::Configuration::default();

	if let Some(name) = matches.value_of("name") {
		config.name = name.into();
		info!("Node name: {}", config.name);
	}

	let chain_spec = matches.value_of("chain")
		.map(ChainSpec::from)
		.unwrap_or_else(|| if matches.is_present("dev") { ChainSpec::Development } else { ChainSpec::PoC2Testnet });
	info!("Chain specification: {}", chain_spec);

	config.chain_name = chain_spec.clone().into();

	let _guard = if matches.is_present("telemetry") || matches.value_of("telemetry-url").is_some() {
		let name = config.name.clone();
		let chain_name = config.chain_name.clone();
		Some(init_telemetry(TelemetryConfig {
			url: matches.value_of("telemetry-url").unwrap_or(DEFAULT_TELEMETRY_URL).into(),
			on_connect: Box::new(move || {
				telemetry!("system.connected";
					"name" => name.clone(),
					"implementation" => "parity-polkadot",
					"version" => crate_version!(),
					"config" => "",
					"chain" => chain_name.clone(),
				);
			}),
		}))
	} else {
		None
	};

	let base_path = matches.value_of("base-path")
		.map(|x| Path::new(x).to_owned())
		.unwrap_or_else(default_base_path);

	config.keystore_path = matches.value_of("keystore")
		.map(|x| Path::new(x).to_owned())
		.unwrap_or_else(|| keystore_path(&base_path))
		.to_string_lossy()
		.into();

	config.database_path = db_path(&base_path).to_string_lossy().into();

	let (mut genesis_storage, boot_nodes) = PresetConfig::from_spec(chain_spec)
		.map(PresetConfig::deconstruct)
		.unwrap_or_else(|f| (Box::new(move ||
			read_storage_json(&f)
				.map(|s| { info!("{} storage items read from {}", s.len(), f); s })
				.unwrap_or_else(|| panic!("Bad genesis state file: {}", f))
		), vec![]));

	if matches.is_present("build-genesis") {
		info!("Building genesis");
		for (i, (k, v)) in genesis_storage().iter().enumerate() {
			print!("{}\n\"0x{}\": \"0x{}\"", if i > 0 {','} else {'{'}, HexDisplay::from(k), HexDisplay::from(v));
		}
		println!("\n}}");
		return Ok(())
	}

	config.genesis_storage = genesis_storage;

	let role =
		if matches.is_present("collator") {
			info!("Starting collator");
			service::Role::COLLATOR
		} else if matches.is_present("light") {
			info!("Starting (light)");
			service::Role::LIGHT
		} else if matches.is_present("validator") || matches.is_present("dev") {
			info!("Starting validator");
			service::Role::VALIDATOR
		} else {
			info!("Starting (heavy)");
			service::Role::FULL
		};

	config.roles = role;
	{
		config.network.boot_nodes = matches
			.values_of("bootnodes")
			.map_or(Default::default(), |v| v.map(|n| n.to_owned()).collect());
		config.network.boot_nodes.extend(boot_nodes);
		config.network.config_path = Some(network_path(&base_path).to_string_lossy().into());
		config.network.net_config_path = config.network.config_path.clone();

		let port = match matches.value_of("port") {
			Some(port) => port.parse().expect("Invalid p2p port value specified."),
			None => 30333,
		};
		config.network.listen_address = Some(SocketAddr::new("0.0.0.0".parse().unwrap(), port));
		config.network.public_address = None;
		config.network.client_version = format!("parity-polkadot/{}", crate_version!());
		config.network.use_secret = match matches.value_of("node-key").map(|s| s.parse()) {
			Some(Ok(secret)) => Some(secret),
			Some(Err(err)) => return Err(format!("Error parsing node key: {}", err).into()),
			None => None,
		};
	}

	config.keys = matches.values_of("key").unwrap_or_default().map(str::to_owned).collect();
	if matches.is_present("dev") {
		config.keys.push("Alice".into());
	}

	let sys_conf = SystemConfiguration {
		chain_name: config.chain_name.clone(),
	};

	match role == service::Role::LIGHT {
		true => run_until_exit(core, service::new_light(config)?, &matches, sys_conf),
		false => run_until_exit(core, service::new_full(config)?, &matches, sys_conf),
	}
}

fn run_until_exit<C>(mut core: reactor::Core, service: service::Service<C>, matches: &clap::ArgMatches, sys_conf: SystemConfiguration) -> error::Result<()>
	where
		C: service::Components,
		client::error::Error: From<<<<C as service::Components>::Backend as client::backend::Backend<Block>>::State as state_machine::Backend>::Error>,
{
	let exit = {
		// can't use signal directly here because CtrlC takes only `Fn`.
		let (exit_send, exit) = mpsc::channel(1);
		ctrlc::CtrlC::set_handler(move || {
			exit_send.clone().send(()).wait().expect("Error sending exit notification");
		});

		exit
	};

	informant::start(&service, core.handle());

	let _rpc_servers = {
		let http_address = parse_address("127.0.0.1:9933", "rpc-port", matches)?;
		let ws_address = parse_address("127.0.0.1:9944", "ws-port", matches)?;

		let handler = || {
			let chain = rpc::apis::chain::Chain::new(service.client(), core.remote());
			let author = rpc::apis::author::Author::new(service.client(), service.transaction_pool());
			rpc::rpc_handler::<Block, _, _, _, _>(
				service.client(),
				chain,
				author,
				sys_conf.clone(),
			)
		};
		(
			start_server(http_address, |address| rpc::start_http(address, handler())),
			start_server(ws_address, |address| rpc::start_ws(address, handler())),
		)
	};

	core.run(exit.into_future()).expect("Error running informant event loop");
	Ok(())
}

fn start_server<T, F>(mut address: SocketAddr, start: F) -> Result<T, io::Error> where
	F: Fn(&SocketAddr) -> Result<T, io::Error>,
{
	start(&address)
		.or_else(|e| match e.kind() {
			io::ErrorKind::AddrInUse |
			io::ErrorKind::PermissionDenied => {
				warn!("Unable to bind server to {}. Trying random port.", address);
				address.set_port(0);
				start(&address)
			},
			_ => Err(e),
		})
}

fn parse_address(default: &str, port_param: &str, matches: &clap::ArgMatches) -> Result<SocketAddr, String> {
	let mut address: SocketAddr = default.parse().ok().ok_or(format!("Invalid address specified for --{}.", port_param))?;
	if let Some(port) = matches.value_of(port_param) {
		let port: u16 = port.parse().ok().ok_or(format!("Invalid port for --{} specified.", port_param))?;
		address.set_port(port);
	}

	Ok(address)
}

fn keystore_path(base_path: &Path) -> PathBuf {
	let mut path = base_path.to_owned();
	path.push("keystore");
	path
}

fn db_path(base_path: &Path) -> PathBuf {
	let mut path = base_path.to_owned();
	path.push("db");
	path
}

fn network_path(base_path: &Path) -> PathBuf {
	let mut path = base_path.to_owned();
	path.push("network");
	path
}

fn default_base_path() -> PathBuf {
	use app_dirs::{AppInfo, AppDataType};

	let app_info = AppInfo {
		name: "Polkadot",
		author: "Parity Technologies",
	};

	app_dirs::get_app_root(
		AppDataType::UserData,
		&app_info,
	).expect("app directories exist on all supported platforms; qed")
}

fn init_logger(pattern: &str) {
	use ansi_term::Colour;

	let mut builder = env_logger::LogBuilder::new();
	// Disable info logging by default for some modules:
	builder.filter(Some("ws"), log::LogLevelFilter::Warn);
	builder.filter(Some("hyper"), log::LogLevelFilter::Warn);
	// Enable info for others.
	builder.filter(None, log::LogLevelFilter::Info);

	if let Ok(lvl) = std::env::var("RUST_LOG") {
		builder.parse(&lvl);
	}

	builder.parse(pattern);
	let isatty = atty::is(atty::Stream::Stderr);
	let enable_color = isatty;

	let format = move |record: &log::LogRecord| {
		let timestamp = time::strftime("%Y-%m-%d %H:%M:%S", &time::now()).expect("Error formatting log timestamp");

		let mut output = if log::max_log_level() <= log::LogLevelFilter::Info {
			format!("{} {}", Colour::Black.bold().paint(timestamp), record.args())
		} else {
			let name = ::std::thread::current().name().map_or_else(Default::default, |x| format!("{}", Colour::Blue.bold().paint(x)));
			format!("{} {} {} {}  {}", Colour::Black.bold().paint(timestamp), name, record.level(), record.target(), record.args())
		};

		if !enable_color {
			output = kill_color(output.as_ref());
		}

		if !isatty && record.level() <= log::LogLevel::Info && atty::is(atty::Stream::Stdout) {
			// duplicate INFO/WARN output to console
			println!("{}", output);
		}
		output
	};
	builder.format(format);

	builder.init().expect("Logger initialized only once.");
}

fn kill_color(s: &str) -> String {
	lazy_static! {
		static ref RE: regex::Regex = regex::Regex::new("\x1b\\[[^m]+m").expect("Error initializing color regex");
	}
	RE.replace_all(s, "").to_string()
}
