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
extern crate futures;
extern crate tokio_core;
extern crate ctrlc;
extern crate ed25519;
extern crate triehash;
extern crate substrate_codec as codec;
extern crate substrate_state_machine as state_machine;
extern crate substrate_client as client;
extern crate substrate_primitives as primitives;
extern crate substrate_network as network;
extern crate substrate_rpc_servers as rpc;
extern crate substrate_runtime_support as runtime_support;
extern crate polkadot_primitives;
extern crate polkadot_executor;
extern crate polkadot_runtime;
extern crate polkadot_service as service;

#[macro_use]
extern crate clap;
#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate log;

pub mod error;
mod informant;

use std::io;
use std::net::SocketAddr;
use std::path::{Path, PathBuf};
use futures::sync::mpsc;
use futures::{Sink, Future, Stream};
use tokio_core::reactor;
use service::ChainSpec;

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
	let mut core = reactor::Core::new().expect("tokio::Core could not be created");
	let exit = {
		// can't use signal directly here because CtrlC takes only `Fn`.
		let (exit_send, exit) = mpsc::channel(1);
		ctrlc::CtrlC::set_handler(move || {
			exit_send.clone().send(()).wait().expect("Error sending exit notification");
		});

		exit
	};

	let yaml = load_yaml!("./cli.yml");
	let matches = match clap::App::from_yaml(yaml).version(crate_version!()).get_matches_from_safe(args) {
		Ok(m) => m,
		Err(ref e) if e.kind == clap::ErrorKind::VersionDisplayed => return Ok(()),
		Err(ref e) if e.kind == clap::ErrorKind::HelpDisplayed || e.kind == clap::ErrorKind::VersionDisplayed => {
			let _ = clap::App::from_yaml(yaml).print_long_help();
			return Ok(());
		}
		Err(e) => return Err(e.into()),
	};

	// TODO [ToDr] Split parameters parsing from actual execution.
	let log_pattern = matches.value_of("log").unwrap_or("");
	init_logger(log_pattern);

	let mut config = service::Configuration::default();

	let base_path = matches.value_of("base-path")
		.map(|x| Path::new(x).to_owned())
		.unwrap_or_else(default_base_path);

	config.keystore_path = matches.value_of("keystore")
		.map(|x| Path::new(x).to_owned())
		.unwrap_or_else(|| keystore_path(&base_path))
		.to_string_lossy()
		.into();

	let mut role = service::Role::FULL;
	if matches.is_present("collator") {
		info!("Starting collator.");
		role = service::Role::COLLATOR;
	}
	else if matches.is_present("validator") {
		info!("Starting validator.");
		role = service::Role::VALIDATOR;
	}

	match matches.value_of("chain") {
		Some("poc-1") => config.chain_spec = ChainSpec::PoC1Testnet,
		Some("dev") => config.chain_spec = ChainSpec::Development,
		None => (),
		Some(unknown) => panic!("Invalid chain name: {}", unknown),
	}
	info!("Chain specification: {}", match config.chain_spec {
		ChainSpec::Development => "Local Development",
		ChainSpec::PoC1Testnet => "PoC-1 Testnet",
	});

	config.roles = role;
	{
		config.network.boot_nodes = matches
			.values_of("bootnodes")
			.map_or(Default::default(), |v| v.map(|n| n.to_owned()).collect());
		config.network.config_path = Some(network_path(&base_path).to_string_lossy().into());
		config.network.net_config_path = config.network.config_path.clone();

		let port = match matches.value_of("port") {
			Some(port) => port.parse().expect("Invalid p2p port value specified."),
			None => 30333,
		};
		config.network.listen_address = Some(SocketAddr::new("0.0.0.0".parse().unwrap(), port));
		config.network.public_address = None;
		config.network.client_version = format!("parity-polkadot/{}", crate_version!());
	}

	config.keys = matches.values_of("key").unwrap_or_default().map(str::to_owned).collect();

	let service = service::Service::new(config)?;

	informant::start(&service, core.handle());

	let _rpc_servers = {
		let http_address = parse_address("127.0.0.1:9933", "rpc-port", &matches)?;
		let ws_address = parse_address("127.0.0.1:9944", "ws-port", &matches)?;

		let handler = || {
			let chain = rpc::apis::chain::Chain::new(service.client(), core.remote());
			rpc::rpc_handler(service.client(), chain, service.transaction_pool())
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
	let mut address: SocketAddr = default.parse().unwrap();
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


	builder.init().expect("Logger initialized only once.");
}
