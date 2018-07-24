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
extern crate fdlimit;
extern crate futures;
extern crate tokio;
extern crate ed25519;
extern crate triehash;
extern crate parking_lot;
extern crate serde;
extern crate serde_json;
extern crate names;
extern crate backtrace;

extern crate substrate_client as client;
extern crate substrate_network as network;
extern crate substrate_codec as codec;
extern crate substrate_primitives;
extern crate substrate_rpc;
extern crate substrate_rpc_servers as rpc;
extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_state_machine as state_machine;
extern crate substrate_extrinsic_pool;
extern crate substrate_service;
extern crate polkadot_primitives;
extern crate polkadot_runtime;
extern crate polkadot_service as service;
#[macro_use]
extern crate slog;	// needed until we can reexport `slog_info` from `substrate_telemetry`
#[macro_use]
extern crate substrate_telemetry;
extern crate polkadot_transaction_pool as txpool;
extern crate exit_future;

#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate clap;
#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate log;

pub mod error;
mod informant;
mod chain_spec;
mod panic_hook;

pub use chain_spec::ChainSpec;
pub use client::error::Error as ClientError;
pub use client::backend::Backend as ClientBackend;
pub use state_machine::Backend as StateMachineBackend;
pub use polkadot_primitives::Block as PolkadotBlock;
pub use service::{Components as ServiceComponents, Service, CustomConfiguration};

use std::io::{Write, Read, stdin, stdout};
use std::fs::File;
use std::net::SocketAddr;
use std::path::{Path, PathBuf};
use names::{Generator, Name};
use regex::Regex;

use futures::Future;
use tokio::runtime::Runtime;
use service::PruningMode;

const DEFAULT_TELEMETRY_URL: &str = "wss://telemetry.polkadot.io/submit/";

/// Executable version. Used to pass version information from the root crate.
pub struct VersionInfo {
	/// Implementation version.
	pub version: &'static str,
	/// SCM Commit hash.
	pub commit: &'static str,
}

fn load_spec(matches: &clap::ArgMatches) -> Result<(service::ChainSpec, bool), String> {
	let chain_spec = matches.value_of("chain")
		.map(ChainSpec::from)
		.unwrap_or_else(|| if matches.is_present("dev") { ChainSpec::Development } else { ChainSpec::KrummeLanke });
	let is_global = match chain_spec {
		ChainSpec::KrummeLanke => true,
		_ => false,
	};
	let spec = chain_spec.load()?;
	info!("Chain specification: {}", spec.name());
	Ok((spec, is_global))
}

fn base_path(matches: &clap::ArgMatches) -> PathBuf {
	matches.value_of("base-path")
		.map(|x| Path::new(x).to_owned())
		.unwrap_or_else(default_base_path)
}

/// Additional worker making use of the node, to run asynchronously before shutdown.
///
/// This will be invoked with the service and spawn a future that resolves
/// when complete.
pub trait Worker {
	/// A future that resolves when the work is done or the node should exit.
	/// This will be run on a tokio runtime.
	type Work: Future<Item=(),Error=()> + Send + 'static;

	/// An exit scheduled for the future.
	type Exit: Future<Item=(),Error=()> + Send + 'static;

	/// Return configuration for the polkadot node.
	// TODO: make this the full configuration, so embedded nodes don't need
	// string CLI args
	fn configuration(&self) -> CustomConfiguration { Default::default() }

	/// Don't work, but schedule an exit.
	fn exit_only(self) -> Self::Exit;

	/// Do work and schedule exit.
	fn work<C: ServiceComponents>(self, service: &Service<C>) -> Self::Work;
}

/// Check whether a node name is considered as valid
fn is_node_name_valid(_name: &str) -> Result<(), &str> {
	const MAX_NODE_NAME_LENGTH: usize = 32;
	let name = _name.to_string();
	if name.chars().count() >= MAX_NODE_NAME_LENGTH {
		return Err("Node name too long");
}

	let invalid_chars = r"[\\.@]";
	let re = Regex::new(invalid_chars).unwrap();
	if re.is_match(&name) {
		return Err("Node name should not contain invalid chars such as '.' and '@'");
	}

	let invalid_patterns = r"(https?:\\/+)?(www)+";
	let re = Regex::new(invalid_patterns).unwrap();
	if re.is_match(&name) {
		return Err("Node name should not contain urls");
	}

	Ok(())
}

/// Parse command line arguments and start the node.
///
/// IANA unassigned port ranges that we could use:
/// 6717-6766		Unassigned
/// 8504-8553		Unassigned
/// 9556-9591		Unassigned
/// 9803-9874		Unassigned
/// 9926-9949		Unassigned
pub fn run<I, T, W>(args: I, worker: W, version: VersionInfo) -> error::Result<()> where
	I: IntoIterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
	W: Worker,
{
	panic_hook::set();

	let yaml = load_yaml!("./cli.yml");
	let matches = match clap::App::from_yaml(yaml)
		.version(&(crate_version!().to_owned() + "\n")[..])
		.get_matches_from_safe(args) {
			Ok(m) => m,
			Err(e) => e.exit(),
	};

	// TODO [ToDr] Split parameters parsing from actual execution.
	let log_pattern = matches.value_of("log").unwrap_or("");
	init_logger(log_pattern);
	fdlimit::raise_fd_limit();

	info!("Parity ·:· Polkadot");
	info!("  version {}", crate_version!());
	info!("  by Parity Technologies, 2017, 2018");

	if let Some(matches) = matches.subcommand_matches("build-spec") {
		return build_spec(matches);
	}

	if let Some(matches) = matches.subcommand_matches("export-blocks") {
		return export_blocks(matches, worker.exit_only());
	}

	if let Some(matches) = matches.subcommand_matches("import-blocks") {
		return import_blocks(matches, worker.exit_only());
	}

	if let Some(matches) = matches.subcommand_matches("revert") {
		return revert_chain(matches);
	}

	let (spec, is_global) = load_spec(&matches)?;
	let mut config = service::Configuration::default_with_spec(spec);
	config.impl_name = "parity-polkadot";
	config.impl_commit = version.commit;
	config.impl_version = version.version;

	config.name = match matches.value_of("name") {
		None => Generator::with_naming(Name::Numbered).next().unwrap(),
		Some(name) => name.into(),
	};
	match is_node_name_valid(&config.name) {
		Ok(_) => info!("Node name: {}", config.name),
		Err(msg) => return Err(error::ErrorKind::Input(
			format!("Invalid node name '{}'. Reason: {}. If unsure, use none.", config.name, msg)).into())
	}

	let base_path = base_path(&matches);

	config.keystore_path = matches.value_of("keystore")
		.map(|x| Path::new(x).to_owned())
		.unwrap_or_else(|| keystore_path(&base_path, config.chain_spec.id()))
		.to_string_lossy()
		.into();

	config.database_path = db_path(&base_path, config.chain_spec.id()).to_string_lossy().into();

	config.pruning = match matches.value_of("pruning") {
		Some("archive") => PruningMode::ArchiveAll,
		None => PruningMode::default(),
		Some(s) => PruningMode::keep_blocks(s.parse()
			.map_err(|_| error::ErrorKind::Input("Invalid pruning mode specified".to_owned()))?),
	};

	let role =
		if matches.is_present("light") {
			info!("Starting (light)");
			config.execution_strategy = service::ExecutionStrategy::NativeWhenPossible;
			service::Roles::LIGHT
		} else if matches.is_present("validator") || matches.is_present("dev") {
			info!("Starting validator");
			config.execution_strategy = service::ExecutionStrategy::Both;
			service::Roles::AUTHORITY
		} else {
			info!("Starting (heavy)");
			config.execution_strategy = service::ExecutionStrategy::NativeWhenPossible;
			service::Roles::FULL
		};

	if let Some(v) = matches.value_of("min-heap-pages") {
		config.min_heap_pages = v.parse().map_err(|_| "Invalid --min-heap-pages argument")?;
	}
	if let Some(v) = matches.value_of("max-heap-pages") {
		config.max_heap_pages = v.parse().map_err(|_| "Invalid --max-heap-pages argument")?;
	}

	if let Some(s) = matches.value_of("execution") {
		config.execution_strategy = match s {
			"both" => service::ExecutionStrategy::Both,
			"native" => service::ExecutionStrategy::NativeWhenPossible,
			"wasm" => service::ExecutionStrategy::AlwaysWasm,
			_ => return Err(error::ErrorKind::Input("Invalid execution mode specified".to_owned()).into()),
		};
	}

	config.roles = role;
	{
		config.network.boot_nodes.extend(matches
			.values_of("bootnodes")
			.map_or(Default::default(), |v| v.map(|n| n.to_owned()).collect::<Vec<_>>()));
		config.network.config_path = Some(network_path(&base_path, config.chain_spec.id()).to_string_lossy().into());
		config.network.net_config_path = config.network.config_path.clone();

		let port = match matches.value_of("port") {
			Some(port) => port.parse().map_err(|_| "Invalid p2p port value specified.")?,
			None => 30333,
		};

		config.network.listen_address = Some(SocketAddr::new("0.0.0.0".parse().unwrap(), port));
		config.network.public_address = None;
		config.network.client_version = config.client_id();
		config.network.use_secret = match matches.value_of("node-key").map(|s| s.parse()) {
			Some(Ok(secret)) => Some(secret),
			Some(Err(err)) => return Err(format!("Error parsing node key: {}", err).into()),
			None => None,
		};
	}

	config.custom = worker.configuration();

	config.keys = matches.values_of("key").unwrap_or_default().map(str::to_owned).collect();
	if matches.is_present("dev") {
		config.keys.push("Alice".into());
	}

	config.rpc_http = Some(parse_address("127.0.0.1:9933", "rpc-port", &matches)?);
	config.rpc_ws = Some(parse_address("127.0.0.1:9944", "ws-port", &matches)?);

	let mut runtime = Runtime::new()?;
	let executor = runtime.executor();

	let telemetry_enabled =
		matches.is_present("telemetry")
		|| matches.value_of("telemetry-url").is_some()
		|| (is_global && !matches.is_present("no-telemetry"));
	let telemetry_url = if telemetry_enabled {
		Some(matches.value_of("telemetry-url").unwrap_or(DEFAULT_TELEMETRY_URL).into())
	} else {
		None
	};

	config.telemetry_url = telemetry_url;

	match role == service::Roles::LIGHT {
		true => run_until_exit(&mut runtime, service::new_light(config, executor)?, worker)?,
		false => run_until_exit(&mut runtime, service::new_full(config, executor)?, worker)?,
	}

	// TODO: hard exit if this stalls?
	runtime.shutdown_on_idle().wait().expect("failed to shut down event loop");
	Ok(())
}

fn build_spec(matches: &clap::ArgMatches) -> error::Result<()> {
	let (spec, _) = load_spec(&matches)?;
	info!("Building chain spec");
	let json = spec.to_json(matches.is_present("raw"))?;
	print!("{}", json);
	Ok(())
}

fn export_blocks<E>(matches: &clap::ArgMatches, exit: E) -> error::Result<()>
	where E: Future<Item=(),Error=()> + Send + 'static
{
	let base_path = base_path(matches);
	let (spec, _) = load_spec(&matches)?;
	let mut config = service::Configuration::default_with_spec(spec);
	config.database_path = db_path(&base_path, config.chain_spec.id()).to_string_lossy().into();
	info!("DB path: {}", config.database_path);
	let from: u64 = match matches.value_of("from") {
		Some(v) => v.parse().map_err(|_| "Invalid --from argument")?,
		None => 1,
	};

	let to: Option<u64> = match matches.value_of("to") {
		Some(v) => Some(v.parse().map_err(|_| "Invalid --to argument")?),
		None => None,
	};
	let json = matches.is_present("json");

	let file: Box<Write> = match matches.value_of("OUTPUT") {
		Some(filename) => Box::new(File::create(filename)?),
		None => Box::new(stdout()),
	};

	Ok(substrate_service::chain_ops::export_blocks::<service::Factory, _, _>(config, exit, file, from, to, json)?)
}

fn import_blocks<E>(matches: &clap::ArgMatches, exit: E) -> error::Result<()>
	where E: Future<Item=(),Error=()> + Send + 'static
{
	let (spec, _) = load_spec(&matches)?;
	let base_path = base_path(matches);
	let mut config = service::Configuration::default_with_spec(spec);
	config.database_path = db_path(&base_path, config.chain_spec.id()).to_string_lossy().into();

	if let Some(v) = matches.value_of("min-heap-pages") {
		config.min_heap_pages = v.parse().map_err(|_| "Invalid --min-heap-pages argument")?;
	}
	if let Some(v) = matches.value_of("max-heap-pages") {
		config.max_heap_pages = v.parse().map_err(|_| "Invalid --max-heap-pages argument")?;
	}

	if let Some(s) = matches.value_of("execution") {
		config.execution_strategy = match s {
			"both" => service::ExecutionStrategy::Both,
			"native" => service::ExecutionStrategy::NativeWhenPossible,
			"wasm" => service::ExecutionStrategy::AlwaysWasm,
			_ => return Err(error::ErrorKind::Input("Invalid execution mode specified".to_owned()).into()),
		};
	}

	let file: Box<Read> = match matches.value_of("INPUT") {
		Some(filename) => Box::new(File::open(filename)?),
		None => Box::new(stdin()),
	};

	Ok(substrate_service::chain_ops::import_blocks::<service::Factory, _, _>(config, exit, file)?)
}

fn revert_chain(matches: &clap::ArgMatches) -> error::Result<()> {
	let (spec, _) = load_spec(&matches)?;
	let base_path = base_path(matches);
	let mut config = service::Configuration::default_with_spec(spec);
	config.database_path = db_path(&base_path, config.chain_spec.id()).to_string_lossy().into();

	let blocks = match matches.value_of("NUM") {
		Some(v) => v.parse().map_err(|_| "Invalid block count specified")?,
		None => 256,
	};

	Ok(substrate_service::chain_ops::revert_chain::<service::Factory>(config, blocks)?)
}

fn run_until_exit<C, W>(
	runtime: &mut Runtime,
	service: service::Service<C>,
	worker: W,
) -> error::Result<()>
	where
		C: service::Components,
		W: Worker,
{
	let (exit_send, exit) = exit_future::signal();

	let executor = runtime.executor();
	informant::start(&service, exit.clone(), executor.clone());

	let _ = runtime.block_on(worker.work(&service));
	exit_send.fire();
	Ok(())
}

fn parse_address(default: &str, port_param: &str, matches: &clap::ArgMatches) -> Result<SocketAddr, String> {
	let mut address: SocketAddr = default.parse().ok().ok_or(format!("Invalid address specified for --{}.", port_param))?;
	if let Some(port) = matches.value_of(port_param) {
		let port: u16 = port.parse().ok().ok_or(format!("Invalid port for --{} specified.", port_param))?;
		address.set_port(port);
	}

	Ok(address)
}

fn keystore_path(base_path: &Path, chain_id: &str) -> PathBuf {
	let mut path = base_path.to_owned();
	path.push("chains");
	path.push(chain_id);
	path.push("keystore");
	path
}

fn db_path(base_path: &Path, chain_id: &str) -> PathBuf {
	let mut path = base_path.to_owned();
	path.push("chains");
	path.push(chain_id);
	path.push("db");
	path
}

fn network_path(base_path: &Path, chain_id: &str) -> PathBuf {
	let mut path = base_path.to_owned();
	path.push("chains");
	path.push(chain_id);
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
		static ref RE: Regex = Regex::new("\x1b\\[[^m]+m").expect("Error initializing color regex");
	}
	RE.replace_all(s, "").to_string()
}

#[cfg(test)]
mod tests {
	use super::*;

    #[test]
    fn tests_node_name_good() {
        assert!(is_node_name_valid("short name").is_ok());
    }

    #[test]
	fn tests_node_name_bad() {
        assert!(is_node_name_valid("long names are not very cool for the ui").is_err());
        assert!(is_node_name_valid("Dots.not.Ok").is_err());
        assert!(is_node_name_valid("http://visit.me").is_err());
        assert!(is_node_name_valid("https://visit.me").is_err());
        assert!(is_node_name_valid("www.visit.me").is_err());
        assert!(is_node_name_valid("email@domain").is_err());
    }
}
