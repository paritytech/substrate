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

pub use chain_spec::ChainSpec;
pub use client::error::Error as ClientError;
pub use client::backend::Backend as ClientBackend;
pub use state_machine::Backend as StateMachineBackend;
pub use polkadot_primitives::Block as PolkadotBlock;
pub use service::{Components as ServiceComponents, Service};

use std::io::{self, Write, Read, stdin, stdout};
use std::fs::File;
use std::net::SocketAddr;
use std::path::{Path, PathBuf};
use substrate_telemetry::{init_telemetry, TelemetryConfig};
use polkadot_primitives::BlockId;
use codec::Slicable;
use client::BlockOrigin;
use runtime_primitives::generic::SignedBlock;

use futures::Future;
use tokio::runtime::Runtime;
use service::PruningMode;

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

fn load_spec(matches: &clap::ArgMatches) -> Result<(service::ChainSpec, bool), String> {
	let chain_spec = matches.value_of("chain")
		.map(ChainSpec::from)
		.unwrap_or_else(|| if matches.is_present("dev") { ChainSpec::Development } else { ChainSpec::StagingTestnet });
	let is_global = match chain_spec {
		ChainSpec::PoC1Testnet | ChainSpec::StagingTestnet => true,
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
	type Work: Future<Item=(),Error=()>;

	/// An exit scheduled for the future.
	type Exit: Future<Item=(),Error=()> + Send + 'static;

	/// Don't work, but schedule an exit.
	fn exit_only(self) -> Self::Exit;

	/// Do work and schedule exit.
	fn work<C: ServiceComponents>(self, service: &Service<C>) -> Self::Work;
}

/// Parse command line arguments and start the node.
///
/// IANA unassigned port ranges that we could use:
/// 6717-6766		Unassigned
/// 8504-8553		Unassigned
/// 9556-9591		Unassigned
/// 9803-9874		Unassigned
/// 9926-9949		Unassigned
pub fn run<I, T, W>(args: I, worker: W) -> error::Result<()> where
	I: IntoIterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
	W: Worker,
{
	let yaml = load_yaml!("./cli.yml");
	let matches = match clap::App::from_yaml(yaml).version(&(crate_version!().to_owned() + "\n")[..]).get_matches_from_safe(args) {
		Ok(m) => m,
		Err(ref e) if e.kind == clap::ErrorKind::VersionDisplayed => return Ok(()),
		Err(ref e) if e.kind == clap::ErrorKind::HelpDisplayed => {
			print!("{}", e);
			return Ok(())
		}
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

	let (spec, is_global) = load_spec(&matches)?;
	let mut config = service::Configuration::default_with_spec(spec);

	if let Some(name) = matches.value_of("name") {
		config.name = name.into();
		info!("Node name: {}", config.name);
	}

	let base_path = base_path(&matches);
	config.keystore_path = matches.value_of("keystore")
		.map(|x| Path::new(x).to_owned())
		.unwrap_or_else(|| keystore_path(&base_path))
		.to_string_lossy()
		.into();

	config.database_path = db_path(&base_path).to_string_lossy().into();

	config.pruning = match matches.value_of("pruning") {
		Some("archive") => PruningMode::ArchiveAll,
		None => PruningMode::keep_blocks(256),
		Some(s) => PruningMode::keep_blocks(s.parse()
			.map_err(|_| error::ErrorKind::Input("Invalid pruning mode specified".to_owned()))?),
	};

	let role =
		if matches.is_present("collator") {
			info!("Starting collator");
			// TODO [rob]: collation node implementation
			// This isn't a thing. Different parachains will have their own collator executables and
			// maybe link to libpolkadot to get a light-client. 
			service::Role::LIGHT
		} else if matches.is_present("light") {
			info!("Starting (light)");
			config.execution_strategy = service::ExecutionStrategy::NativeWhenPossible;
			service::Role::LIGHT
		} else if matches.is_present("validator") || matches.is_present("dev") {
			info!("Starting validator");
			config.execution_strategy = service::ExecutionStrategy::Both;
			service::Role::AUTHORITY
		} else {
			info!("Starting (heavy)");
			config.execution_strategy = service::ExecutionStrategy::NativeWhenPossible;
			service::Role::FULL
		};

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
		chain_name: config.chain_spec.name().to_owned(),
	};

	let mut runtime = Runtime::new()?;
	let executor = runtime.executor();

	let telemetry_enabled =
		matches.is_present("telemetry")
		|| matches.value_of("telemetry-url").is_some()
		|| (is_global && !matches.is_present("no-telemetry"));
	let _guard = if telemetry_enabled {
		let name = config.name.clone();
		let chain_name = config.chain_spec.name().to_owned();
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

	match role == service::Role::LIGHT {
		true => run_until_exit(&mut runtime, service::new_light(config, executor)?, &matches, sys_conf, worker)?,
		false => run_until_exit(&mut runtime, service::new_full(config, executor)?, &matches, sys_conf, worker)?,
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
	config.database_path = db_path(&base_path).to_string_lossy().into();
	info!("DB path: {}", config.database_path);
	let client = service::new_client(config)?;
	let (exit_send, exit_recv) = std::sync::mpsc::channel();
	::std::thread::spawn(move || {
		let _ = exit.wait();
		let _ = exit_send.send(());
	});
	info!("Exporting blocks");
	let mut block: u32 = match matches.value_of("from") {
		Some(v) => v.parse().map_err(|_| "Invalid --from argument")?,
		None => 1,
	};

	let last = match matches.value_of("to") {
		Some(v) => v.parse().map_err(|_| "Invalid --to argument")?,
		None => client.info()?.chain.best_number as u32,
	};

	if last < block {
		return Err("Invalid block range specified".into());
	}

	let json = matches.is_present("json");

	let mut file: Box<Write> = match matches.value_of("OUTPUT") {
		Some(filename) => Box::new(File::open(filename)?),
		None => Box::new(stdout()),
	};

	if !json {
		file.write(&(last - block + 1).encode())?;
	}

	loop {
		if exit_recv.try_recv().is_ok() {
			break;
		}
		match client.block(&BlockId::number(block as u64))? {
			Some(block) => {
				if json {
					serde_json::to_writer(&mut *file, &block).map_err(|e| format!("Eror writing JSON: {}", e))?;
				} else {
					file.write(&block.encode())?;
				}
			},
			None => break,
		}
		if block % 10000 == 0 {
			info!("#{}", block);
		}
		if block == last {
			break;
		}
		block += 1;
	}
	Ok(())
}

fn import_blocks<E>(matches: &clap::ArgMatches, exit: E) -> error::Result<()>
	where E: Future<Item=(),Error=()> + Send + 'static
{
	let (spec, _) = load_spec(&matches)?;
	let base_path = base_path(matches);
	let mut config = service::Configuration::default_with_spec(spec);
	config.database_path = db_path(&base_path).to_string_lossy().into();
	let client = service::new_client(config)?;
	let (exit_send, exit_recv) = std::sync::mpsc::channel();

	::std::thread::spawn(move || {
		let _ = exit.wait();
		let _ = exit_send.send(());
	});

	let mut file: Box<Read> = match matches.value_of("INPUT") {
		Some(filename) => Box::new(File::open(filename)?),
		None => Box::new(stdin()),
	};

	info!("Importing blocks");
	let count: u32 = Slicable::decode(&mut file).ok_or("Error reading file")?;
	let mut block = 0;
	for _ in 0 .. count {
		if exit_recv.try_recv().is_ok() {
			break;
		}
		match SignedBlock::decode(&mut file) {
			Some(block) => {
				let header = client.check_justification(block.block.header, block.justification.into())?;
				client.import_block(BlockOrigin::File, header, Some(block.block.extrinsics))?;
			},
			None => {
				warn!("Error reading block data.");
				break;
			}
		}
		block += 1;
		if block % 10000 == 0 {
			info!("#{}", block);
		}
	}
	info!("Imported {} blocks. Best: #{}", block, client.info()?.chain.best_number);

	Ok(())
}

fn run_until_exit<C, W>(
	runtime: &mut Runtime,
	service: service::Service<C>,
	matches: &clap::ArgMatches,
	sys_conf: SystemConfiguration,
	worker: W,
) -> error::Result<()>
	where
		C: service::Components,
		W: Worker,
{
	let (exit_send, exit) = exit_future::signal();

	let executor = runtime.executor();
	informant::start(&service, exit.clone(), executor.clone());

	let _rpc_servers = {
		let http_address = parse_address("127.0.0.1:9933", "rpc-port", matches)?;
		let ws_address = parse_address("127.0.0.1:9944", "ws-port", matches)?;

		let handler = || {
			let client = (&service as &substrate_service::Service<C>).client();
			let chain = rpc::apis::chain::Chain::new(client.clone(), executor.clone());
			let author = rpc::apis::author::Author::new(client.clone(), service.extrinsic_pool());
			rpc::rpc_handler::<service::ComponentBlock<C>, _, _, _, _>(
				client,
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

	let _ = worker.work(&service).wait();
	exit_send.fire();
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
