// Copyright 2017-2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Substrate CLI library.

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

extern crate app_dirs;
extern crate env_logger;
extern crate atty;
extern crate ansi_term;
extern crate regex;
extern crate time;
extern crate fdlimit;
extern crate futures;
extern crate tokio;
extern crate names;
extern crate backtrace;
extern crate sysinfo;

extern crate substrate_client as client;
extern crate substrate_network as network;
extern crate sr_primitives as runtime_primitives;
extern crate substrate_service as service;
extern crate substrate_primitives as primitives;
#[macro_use]
extern crate slog;	// needed until we can reexport `slog_info` from `substrate_telemetry`
#[macro_use]
extern crate substrate_telemetry;
extern crate exit_future;

#[macro_use]
extern crate lazy_static;
extern crate clap;
#[macro_use]
extern crate error_chain;
#[macro_use]
extern crate log;
extern crate structopt;

mod params;
pub mod error;
pub mod informant;
mod panic_hook;

use runtime_primitives::traits::As;
use service::{
	ServiceFactory, FactoryFullConfiguration, RuntimeGenesis,
	FactoryGenesis, PruningMode, ChainSpec,
};
use network::{
	Protocol, config::{NetworkConfiguration, NonReservedPeerMode},
	multiaddr,
};
use primitives::H256;

use std::io::{Write, Read, stdin, stdout};
use std::iter;
use std::fs;
use std::fs::File;
use std::net::{Ipv4Addr, SocketAddr};
use std::path::{Path, PathBuf};
use std::str::FromStr;
use names::{Generator, Name};
use regex::Regex;
use structopt::StructOpt;
pub use params::{CoreParams, CoreCommands, ExecutionStrategy};

use futures::Future;

/// Executable version. Used to pass version information from the root crate.
pub struct VersionInfo {
	/// Implementation version.
	pub version: &'static str,
	/// SCM Commit hash.
	pub commit: &'static str,
	/// Executable file name.
	pub executable_name: &'static str,
	/// Executable file description.
	pub description: &'static str,
	/// Executable file author.
	pub author: &'static str,
}

/// CLI Action
pub enum Action<E> {
	/// Substrate handled the command. No need to do anything.
	ExecutedInternally,
	/// Service mode requested. Caller should start the service.
	RunService(E),
}

/// Something that can be converted into an exit signal.
pub trait IntoExit {
	/// Exit signal type.
	type Exit: Future<Item=(),Error=()> + Send + 'static;
	/// Convert into exit signal.
	fn into_exit(self) -> Self::Exit;
}

fn get_chain_key(matches: &clap::ArgMatches) -> String {
	matches.value_of("chain").unwrap_or_else(
		|| if matches.is_present("dev") { "dev" } else { "" }
	).into()
}

fn load_spec<F, G>(matches: &clap::ArgMatches, factory: F) -> Result<ChainSpec<G>, String>
	where G: RuntimeGenesis, F: FnOnce(&str) -> Result<Option<ChainSpec<G>>, String>,
{
	let chain_key = get_chain_key(matches);
	let spec = match factory(&chain_key)? {
		Some(spec) => spec,
		None => ChainSpec::from_json_file(PathBuf::from(chain_key))?
	};
	Ok(spec)
}

fn base_path(matches: &clap::ArgMatches) -> PathBuf {
	matches.value_of("base_path")
		.map(|x| Path::new(x).to_owned())
		.unwrap_or_else(default_base_path)
}

fn create_input_err<T: Into<String>>(msg: T) -> error::Error {
	error::ErrorKind::Input(msg.into()).into()
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

/// Parse command line arguments
pub fn parse_args_default<'a, I, T>(args: I, version: VersionInfo) -> clap::ArgMatches<'a>
where
	I: IntoIterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
{
	let full_version = service::config::full_version_from_strs(
		version.version,
		version.commit
	);

	match CoreParams::clap()
		.name(version.executable_name)
		.author(version.author)
		.about(version.description)
		.version(&(full_version + "\n")[..])
		.get_matches_from_safe(args) {
			Ok(m) => m,
			Err(e) => e.exit(),
	}
}

/// Parse clap::Matches into config and chain specification
pub fn parse_matches<'a, F, S>(
	spec_factory: S,
	version: VersionInfo,
	impl_name: &'static str,
	matches: &clap::ArgMatches<'a>
) -> error::Result<(ChainSpec<<F as service::ServiceFactory>::Genesis>, FactoryFullConfiguration<F>)>
where
	F: ServiceFactory,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,

{
	let spec = load_spec(&matches, spec_factory)?;
	let mut config = service::Configuration::default_with_spec(spec.clone());

	config.impl_name = impl_name;
	config.impl_commit = version.commit;
	config.impl_version = version.version;

	config.name = match matches.value_of("name") {
		None => Generator::with_naming(Name::Numbered).next().unwrap(),
		Some(name) => name.into(),
	};
	match is_node_name_valid(&config.name) {
		Ok(_) => (),
		Err(msg) => bail!(
			create_input_err(
				format!("Invalid node name '{}'. Reason: {}. If unsure, use none.",
					config.name,
					msg
				)
			)
		)
	}

	let base_path = base_path(&matches);

	config.keystore_path = matches.value_of("keystore")
		.map(|x| Path::new(x).to_owned())
		.unwrap_or_else(|| keystore_path(&base_path, config.chain_spec.id()))
		.to_string_lossy()
		.into();

	config.database_path = db_path(&base_path, config.chain_spec.id()).to_string_lossy().into();
	config.database_cache_size = match matches.value_of("database_cache_size") {
		Some(s) => Some(s.parse().map_err(|_| "Invalid Database Cache size specified")?),
		_=> None
	};
	config.pruning = match matches.value_of("pruning") {
		Some("archive") => PruningMode::ArchiveAll,
		None => PruningMode::default(),
		Some(s) => PruningMode::keep_blocks(s.parse()
			.map_err(|_| create_input_err("Invalid pruning mode specified"))?),
	};

	let role =
		if matches.is_present("light") {
			config.block_execution_strategy = service::ExecutionStrategy::NativeWhenPossible;
			service::Roles::LIGHT
		} else if matches.is_present("validator") || matches.is_present("dev") {
			config.block_execution_strategy = service::ExecutionStrategy::Both;
			service::Roles::AUTHORITY
		} else {
			config.block_execution_strategy = service::ExecutionStrategy::NativeWhenPossible;
			service::Roles::FULL
		};

	if let Some(s) = matches.value_of("execution") {
		config.block_execution_strategy = match s {
			"both" => service::ExecutionStrategy::Both,
			"native" => service::ExecutionStrategy::NativeWhenPossible,
			"wasm" => service::ExecutionStrategy::AlwaysWasm,
			_ => bail!(create_input_err("Invalid execution mode specified")),
		};
	}

	config.roles = role;
	{
		config.network.boot_nodes.extend(matches
			.values_of("bootnodes")
			.map_or(Default::default(), |v| v.map(|n| n.to_owned()).collect::<Vec<_>>()));
		config.network.config_path = Some(network_path(&base_path, config.chain_spec.id()).to_string_lossy().into());
		config.network.net_config_path = config.network.config_path.clone();
		config.network.reserved_nodes.extend(matches
			 .values_of("reserved_nodes")
			 .map_or(Default::default(), |v| v.map(|n| n.to_owned()).collect::<Vec<_>>()));
		if !config.network.reserved_nodes.is_empty() {
			config.network.non_reserved_mode = NonReservedPeerMode::Deny;
		}

		config.network.listen_addresses = Vec::new();
		for addr in matches.values_of("listen_addr").unwrap_or_default() {
			let addr = addr.parse().map_err(|_| "Invalid listen multiaddress")?;
			config.network.listen_addresses.push(addr);
		}
		if config.network.listen_addresses.is_empty() {
			let port = match matches.value_of("port") {
				Some(port) => port.parse().map_err(|_| "Invalid p2p port value specified.")?,
				None => 30333,
			};
			config.network.listen_addresses = vec![
				iter::once(Protocol::Ip4(Ipv4Addr::new(0, 0, 0, 0)))
					.chain(iter::once(Protocol::Tcp(port)))
					.collect()
			];
		}

		config.network.public_addresses = Vec::new();

		config.network.client_version = config.client_id();
		config.network.use_secret = match matches.value_of("node_key").map(H256::from_str) {
			Some(Ok(secret)) => Some(secret.into()),
			Some(Err(err)) => bail!(create_input_err(format!("Error parsing node key: {}", err))),
			None => None,
		};

		let in_peers = match matches.value_of("in_peers") {
			Some(in_peers) => in_peers.parse().map_err(|_| "Invalid in-peers value specified.")?,
			None => 25,
		};
		let out_peers = match matches.value_of("out_peers") {
			Some(out_peers) => out_peers.parse().map_err(|_| "Invalid out-peers value specified.")?,
			None => 25,
		};

		config.network.in_peers = in_peers;
		config.network.out_peers = out_peers;
	}

	config.keys = matches.values_of("key").unwrap_or_default().map(str::to_owned).collect();
	if matches.is_present("dev") {
		config.keys.push("Alice".into());
	}

	let rpc_interface: &str = if matches.is_present("rpc_external") { "0.0.0.0" } else { "127.0.0.1" };
	let ws_interface: &str = if matches.is_present("ws_external") { "0.0.0.0" } else { "127.0.0.1" };

	config.rpc_http = Some(parse_address(&format!("{}:{}", rpc_interface, 9933), "rpc_port", &matches)?);
	config.rpc_ws = Some(parse_address(&format!("{}:{}", ws_interface, 9944), "ws_port", &matches)?);

	// Override telemetry
	if matches.is_present("no_telemetry") {
		config.telemetry_url = None;
	} else if let Some(url) = matches.value_of("telemetry_url") {
		config.telemetry_url = Some(url.to_owned());
	}

	Ok((spec, config))
}

fn get_db_path_for_subcommand(
	main_cmd: &clap::ArgMatches,
	sub_cmd: &clap::ArgMatches
) -> error::Result<PathBuf> {
	if main_cmd.is_present("chain") && sub_cmd.is_present("chain") {
		bail!(create_input_err("`--chain` option is present two times"));
	}

	fn check_contradicting_chain_dev_flags(
		m0: &clap::ArgMatches,
		m1: &clap::ArgMatches
	) -> error::Result<()> {
		if m0.is_present("dev") && m1.is_present("chain") {
			bail!(create_input_err("`--dev` and `--chain` given on different levels"));
		}

		Ok(())
	}

	check_contradicting_chain_dev_flags(main_cmd, sub_cmd)?;
	check_contradicting_chain_dev_flags(sub_cmd, main_cmd)?;

	let spec_id = if sub_cmd.is_present("chain") || sub_cmd.is_present("dev") {
		get_chain_key(sub_cmd)
	} else {
		get_chain_key(main_cmd)
	};

	if main_cmd.is_present("base_path") && sub_cmd.is_present("base_path") {
		bail!(create_input_err("`--base_path` option is present two times"));
	}

	let base_path = if sub_cmd.is_present("base_path") {
		base_path(sub_cmd)
	} else {
		base_path(main_cmd)
	};

	Ok(db_path(&base_path, &spec_id))
}

//
// IANA unassigned port ranges that we could use:
// 6717-6766		Unassigned
// 8504-8553		Unassigned
// 9556-9591		Unassigned
// 9803-9874		Unassigned
// 9926-9949		Unassigned

/// execute default commands or return service configuration
pub fn execute_default<'a, F, E>(
	spec: ChainSpec<FactoryGenesis<F>>,
	exit: E,
	matches: &clap::ArgMatches<'a>,
	config: &FactoryFullConfiguration<F>
) -> error::Result<Action<E>>
where
	E: IntoExit,
	F: ServiceFactory,
{
	panic_hook::set();

	let log_pattern = matches.value_of("log").unwrap_or("");
	init_logger(log_pattern);
	fdlimit::raise_fd_limit();

	if let Some(matches) = matches.subcommand_matches("build-spec") {
		build_spec::<F>(matches, spec, config)?;
		return Ok(Action::ExecutedInternally);
	} else if let Some(sub_matches) = matches.subcommand_matches("export-blocks") {
		export_blocks::<F, _>(
			get_db_path_for_subcommand(matches, sub_matches)?,
			matches,
			spec,
			exit.into_exit()
		)?;
		return Ok(Action::ExecutedInternally);
	} else if let Some(sub_matches) = matches.subcommand_matches("import-blocks") {
		import_blocks::<F, _>(
			get_db_path_for_subcommand(matches, sub_matches)?,
			matches,
			spec,
			exit.into_exit()
		)?;
		return Ok(Action::ExecutedInternally);
	} else if let Some(sub_matches) = matches.subcommand_matches("revert") {
		revert_chain::<F>(
			get_db_path_for_subcommand(matches, sub_matches)?,
			sub_matches,
			spec
		)?;
		return Ok(Action::ExecutedInternally);
	} else if let Some(sub_matches) = matches.subcommand_matches("purge-chain") {
		purge_chain::<F>(get_db_path_for_subcommand(matches, sub_matches)?)?;
		return Ok(Action::ExecutedInternally);
	}

	Ok(Action::RunService(exit))
}

fn with_default_boot_node<F>(
	spec: &ChainSpec<FactoryGenesis<F>>,
	config: &NetworkConfiguration
) -> error::Result<ChainSpec<FactoryGenesis<F>>>
where
	F: ServiceFactory
{
	let mut spec = spec.clone();
	if spec.boot_nodes().is_empty() {
		let network_keys =
			network::obtain_private_key(config)
				.map_err(|err| format!("Error obtaining network key: {}", err))?;
		let peer_id = network_keys.to_peer_id();
		let addr = multiaddr![
			Ip4([127, 0, 0, 1]),
			Tcp(30333u16),
			P2p(peer_id)
		];
		spec.add_boot_node(addr)
	}
	Ok(spec)
}

fn build_spec<F>(
	matches: &clap::ArgMatches,
	spec: ChainSpec<FactoryGenesis<F>>,
	config: &FactoryFullConfiguration<F>
) -> error::Result<()>
where
	F: ServiceFactory
{
	info!("Building chain spec");
	let raw = matches.is_present("raw");
	let spec = with_default_boot_node::<F>(&spec, &config.network)?;
	let json = service::chain_ops::build_spec::<FactoryGenesis<F>>(spec, raw)?;
	print!("{}", json);
	Ok(())
}

fn export_blocks<F, E>(
	db_path: PathBuf,
	matches: &clap::ArgMatches,
	spec: ChainSpec<FactoryGenesis<F>>,
	exit: E
) -> error::Result<()>
	where F: ServiceFactory, E: Future<Item=(),Error=()> + Send + 'static,
{
	let mut config = service::Configuration::default_with_spec(spec);
	config.database_path = db_path.to_string_lossy().into();
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

	let file: Box<Write> = match matches.value_of("output") {
		Some(filename) => Box::new(File::create(filename)?),
		None => Box::new(stdout()),
	};

	Ok(service::chain_ops::export_blocks::<F, _, _>(config, exit, file, As::sa(from), to.map(As::sa), json)?)
}

fn import_blocks<F, E>(
	db_path: PathBuf,
	matches: &clap::ArgMatches,
	spec: ChainSpec<FactoryGenesis<F>>,
	exit: E
) -> error::Result<()>
	where F: ServiceFactory, E: Future<Item=(),Error=()> + Send + 'static,
{
	let mut config = service::Configuration::default_with_spec(spec);
	config.database_path = db_path.to_string_lossy().into();

	if let Some(s) = matches.value_of("execution") {
		config.block_execution_strategy = match s {
			"both" => service::ExecutionStrategy::Both,
			"native" => service::ExecutionStrategy::NativeWhenPossible,
			"wasm" => service::ExecutionStrategy::AlwaysWasm,
			_ => return Err(error::ErrorKind::Input("Invalid block execution mode specified".to_owned()).into()),
		};
	}

	if let Some(s) = matches.value_of("api-execution") {
		config.api_execution_strategy = match s {
			"both" => service::ExecutionStrategy::Both,
			"native" => service::ExecutionStrategy::NativeWhenPossible,
			"wasm" => service::ExecutionStrategy::AlwaysWasm,
			_ => return Err(error::ErrorKind::Input("Invalid API execution mode specified".to_owned()).into()),
		};
	}

	let file: Box<Read> = match matches.value_of("input") {
		Some(filename) => Box::new(File::open(filename)?),
		None => Box::new(stdin()),
	};

	Ok(service::chain_ops::import_blocks::<F, _, _>(config, exit, file)?)
}

fn revert_chain<F>(
	db_path: PathBuf,
	matches: &clap::ArgMatches,
	spec: ChainSpec<FactoryGenesis<F>>
) -> error::Result<()>
	where F: ServiceFactory,
{
	let mut config = service::Configuration::default_with_spec(spec);
	config.database_path = db_path.to_string_lossy().into();

	let blocks = match matches.value_of("num") {
		Some(v) => v.parse().map_err(|_| "Invalid block count specified")?,
		None => 256,
	};

	Ok(service::chain_ops::revert_chain::<F>(config, As::sa(blocks))?)
}

fn purge_chain<F>(
	db_path: PathBuf,
) -> error::Result<()>
	where F: ServiceFactory,
{
	print!("Are you sure to remove {:?}? (y/n)", &db_path);
	stdout().flush().expect("failed to flush stdout");

	let mut input = String::new();
	stdin().read_line(&mut input)?;
	let input = input.trim();

	match input.chars().nth(0) {
		Some('y') | Some('Y') => {
			fs::remove_dir_all(&db_path)?;
			println!("{:?} removed.", &db_path);
		},
		_ => println!("Aborted"),
	}

	Ok(())
}

fn parse_address(
	default: &str,
	port_param: &str,
	matches: &clap::ArgMatches
) -> Result<SocketAddr, String> {
	let mut address: SocketAddr = default.parse().ok().ok_or_else(
		|| format!("Invalid address specified for --{}.", port_param)
	)?;
	if let Some(port) = matches.value_of(port_param) {
		let port: u16 = port.parse().ok().ok_or_else(
			|| format!("Invalid port for --{} specified.", port_param)
		)?;
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
		name: "Substrate",
		author: "Parity Technologies",
	};

	app_dirs::get_app_root(
		AppDataType::UserData,
		&app_info,
	).expect("app directories exist on all supported platforms; qed")
}

fn init_logger(pattern: &str) {
	use ansi_term::Colour;

	let mut builder = env_logger::Builder::new();
	// Disable info logging by default for some modules:
	builder.filter(Some("ws"), log::LevelFilter::Off);
	builder.filter(Some("hyper"), log::LevelFilter::Warn);
	// Enable info for others.
	builder.filter(None, log::LevelFilter::Info);

	if let Ok(lvl) = std::env::var("RUST_LOG") {
		builder.parse(&lvl);
	}

	builder.parse(pattern);
	let isatty = atty::is(atty::Stream::Stderr);
	let enable_color = isatty;

	builder.format(move |buf, record| {
		let timestamp = time::strftime("%Y-%m-%d %H:%M:%S", &time::now()).expect("Error formatting log timestamp");

		let mut output = if log::max_level() <= log::LevelFilter::Info {
			format!("{} {}", Colour::Black.bold().paint(timestamp), record.args())
		} else {
			let name = ::std::thread::current().name().map_or_else(Default::default, |x| format!("{}", Colour::Blue.bold().paint(x)));
			format!("{} {} {} {}  {}", Colour::Black.bold().paint(timestamp), name, record.level(), record.target(), record.args())
		};

		if !enable_color {
			output = kill_color(output.as_ref());
		}

		if !isatty && record.level() <= log::Level::Info && atty::is(atty::Stream::Stdout) {
			// duplicate INFO/WARN output to console
			println!("{}", output);
		}
		writeln!(buf, "{}", output)
	});

	builder.init();
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
