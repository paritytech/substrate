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
	Protocol, config::{NetworkConfiguration, NonReservedPeerMode, Secret},
	multiaddr,
};
use primitives::H256;

use std::{
	io::{Write, Read, stdin, stdout}, iter, fs::{self, File}, net::{Ipv4Addr, SocketAddr},
	path::{Path, PathBuf}, str::FromStr,
};

use names::{Generator, Name};
use regex::Regex;
use structopt::StructOpt;
pub use params::{
	CoreParams, CoreCommands, RunCmd, PurgeChainCmd, RevertCmd,
	ImportBlocksCmd, ExportBlocksCmd, BuildSpecCmd, NetworkConfigurationParams,
	SharedParams,
};

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

/// Something that can be converted into an exit signal.
pub trait IntoExit {
	/// Exit signal type.
	type Exit: Future<Item=(),Error=()> + Send + 'static;
	/// Convert into exit signal.
	fn into_exit(self) -> Self::Exit;
}

fn get_chain_key(cli: &SharedParams) -> String {
	match cli.chain {
		Some(ref chain) => chain.clone(),
		None => if cli.dev { "dev".into() } else { "".into() }
	}
}

fn load_spec<F, G>(cli: &SharedParams, factory: F) -> error::Result<ChainSpec<G>>
	where G: RuntimeGenesis, F: FnOnce(&str) -> Result<Option<ChainSpec<G>>, String>,
{
	let chain_key = get_chain_key(cli);
	let spec = match factory(&chain_key)? {
		Some(spec) => spec,
		None => ChainSpec::from_json_file(PathBuf::from(chain_key))?
	};
	Ok(spec)
}

fn base_path(cli: &SharedParams) -> PathBuf {
	cli.base_path.clone().unwrap_or_else(default_base_path)
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

/// Something that can return the `CoreParams`.
pub trait GetCoreParams {
	/// Return the `CoreParams`.
	fn core_params(&self) -> CoreParams;
}

/// Parse command line interface arguments and executes the desired command.
pub fn parse_and_execute<'a, F, C, S, RS, E>(
	spec_factory: S,
	version: VersionInfo,
	impl_name: &'static str,
	matches: clap::ArgMatches<'a>,
	exit: E,
	run_service: RS,
) -> error::Result<()>
where
	F: ServiceFactory,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
	C: StructOpt + GetCoreParams,
	E: IntoExit,
	RS: FnOnce(E, C, FactoryFullConfiguration<F>) -> Result<(), String>,
{
	panic_hook::set();

	let cli_args = C::from_clap(&matches);
	let core_params = cli_args.core_params();

	init_logger(core_params.log.as_ref().map(|v| v.as_ref()).unwrap_or(""));
	fdlimit::raise_fd_limit();

	match core_params.cmds {
		CoreCommands::Run(params) => run_node::<F, _, _, _, _>(
			params, cli_args, spec_factory, exit, run_service, impl_name, version
		),
		CoreCommands::BuildSpec(params) => build_spec::<F, _>(params, spec_factory),
		CoreCommands::ExportBlocks(params) => export_blocks::<F, _, _>(params, spec_factory, exit),
		CoreCommands::ImportBlocks(params) => import_blocks::<F, _, _>(params, spec_factory, exit),
		CoreCommands::PurgeChain(params) => purge_chain::<F, _>(params, spec_factory),
		CoreCommands::Revert(params) => revert_chain::<F, _>(params, spec_factory),
	}
}

fn parse_node_key(key: Option<String>) -> error::Result<Option<Secret>> {
	match key.map(|k| H256::from_str(&k)) {
		Some(Ok(secret)) => Ok(Some(secret.into())),
		Some(Err(err)) => Err(create_input_err(format!("Error parsing node key: {}", err))),
		None => Ok(None),
	}
}

/// Fill the given `NetworkConfiguration` by looking at the cli parameters.
fn fill_network_configuration(
	cli: NetworkConfigurationParams,
	base_path: &Path,
	chain_spec_id: &str,
	config: &mut NetworkConfiguration,
	client_id: String,
) -> error::Result<()> {
	config.boot_nodes.extend(cli.bootnodes.into_iter());
	config.config_path = Some(
		network_path(&base_path, chain_spec_id).to_string_lossy().into()
	);
	config.net_config_path = config.config_path.clone();
	config.reserved_nodes.extend(cli.reserved_nodes.into_iter());
	if !config.reserved_nodes.is_empty() {
		config.non_reserved_mode = NonReservedPeerMode::Deny;
	}

	for addr in cli.listen_addr.iter() {
		let addr = addr.parse().map_err(|_| "Invalid listen multiaddress")?;
		config.listen_addresses.push(addr);
	}

	if config.listen_addresses.is_empty() {
		let port = match cli.port {
			Some(port) => port,
			None => 30333,
		};

		config.listen_addresses = vec![
			iter::once(Protocol::Ip4(Ipv4Addr::new(0, 0, 0, 0)))
				.chain(iter::once(Protocol::Tcp(port)))
				.collect()
		];
	}

	config.public_addresses = Vec::new();

	config.client_version = client_id;
	config.use_secret = parse_node_key(cli.node_key)?;

	config.in_peers = cli.in_peers;
	config.out_peers = cli.out_peers;

	Ok(())
}

fn create_run_node_config<F, S>(
	cli: RunCmd, spec_factory: S, impl_name: &'static str, version: VersionInfo
) -> error::Result<FactoryFullConfiguration<F>>
where
	F: ServiceFactory,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	let spec = load_spec(&cli.shared_params, spec_factory)?;
	let mut config = service::Configuration::default_with_spec(spec.clone());

	config.impl_name = impl_name;
	config.impl_commit = version.commit;
	config.impl_version = version.version;

	config.name = match cli.name {
		None => Generator::with_naming(Name::Numbered).next().unwrap(),
		Some(name) => name,
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

	let base_path = base_path(&cli.shared_params);

	config.keystore_path = cli.keystore_path
		.unwrap_or_else(|| keystore_path(&base_path, config.chain_spec.id()))
		.to_string_lossy()
		.into();

	config.database_path =
		db_path(&base_path, config.chain_spec.id()).to_string_lossy().into();
	config.database_cache_size = config.database_cache_size;
	config.pruning = match cli.pruning {
		Some(ref s) if s == "archive" => PruningMode::ArchiveAll,
		None => PruningMode::default(),
		Some(s) => PruningMode::keep_blocks(
			s.parse().map_err(|_| create_input_err("Invalid pruning mode specified"))?
		),
	};

	let role =
		if cli.light {
			config.block_execution_strategy = service::ExecutionStrategy::NativeWhenPossible;
			service::Roles::LIGHT
		} else if cli.validator || cli.shared_params.dev {
			config.block_execution_strategy = service::ExecutionStrategy::Both;
			service::Roles::AUTHORITY
		} else {
			config.block_execution_strategy = service::ExecutionStrategy::NativeWhenPossible;
			service::Roles::FULL
		};

	config.block_execution_strategy = cli.execution.into();

	config.roles = role;
	let client_id = config.client_id();
	fill_network_configuration(
		cli.network_config,
		&base_path,
		spec.id(),
		&mut config.network,
		client_id,
	)?;

	if let Some(key) = cli.key {
		config.keys.push(key);
	}

	if cli.shared_params.dev {
		config.keys.push("Alice".into());
	}

	let rpc_interface: &str = if cli.rpc_external { "0.0.0.0" } else { "127.0.0.1" };
	let ws_interface: &str = if cli.ws_external { "0.0.0.0" } else { "127.0.0.1" };

	config.rpc_http = Some(
		parse_address(&format!("{}:{}", rpc_interface, 9933), cli.rpc_port)?
	);
	config.rpc_ws = Some(
		parse_address(&format!("{}:{}", ws_interface, 9944), cli.ws_port)?
	);

	// Override telemetry
	if cli.no_telemetry {
		config.telemetry_url = None;
	} else if let Some(url) = cli.telemetry_url {
		config.telemetry_url = Some(url);
	}

	Ok(config)
}

fn run_node<F, S, RS, C, E>(
	cli: RunCmd,
	main_cli: C,
	spec_factory: S,
	exit: E,
	run_service: RS,
	impl_name: &'static str,
	version: VersionInfo,
) -> error::Result<()>
where
	C: StructOpt,
	F: ServiceFactory,
	E: IntoExit,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
	RS: FnOnce(E, C, FactoryFullConfiguration<F>) -> Result<(), String>,
 {
	let config = create_run_node_config::<F, _>(cli, spec_factory, impl_name, version)?;

	run_service(exit, main_cli, config).map_err(Into::into)
}

//
// IANA unassigned port ranges that we could use:
// 6717-6766		Unassigned
// 8504-8553		Unassigned
// 9556-9591		Unassigned
// 9803-9874		Unassigned
// 9926-9949		Unassigned

fn with_default_boot_node<F>(
	mut spec: ChainSpec<FactoryGenesis<F>>,
	cli: &BuildSpecCmd,
) -> error::Result<ChainSpec<FactoryGenesis<F>>>
where
	F: ServiceFactory
{
	if spec.boot_nodes().is_empty() {
		let network_path =
			Some(network_path(&base_path(&cli.shared_params), spec.id()).to_string_lossy().into());
		let network_key = parse_node_key(cli.node_key.clone())?;

		let network_keys =
			network::obtain_private_key(&network_key, &network_path)
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

fn build_spec<F, S>(
	cli: BuildSpecCmd,
	spec_factory: S,
) -> error::Result<()>
where
	F: ServiceFactory,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	info!("Building chain spec");
	let spec = load_spec(&cli.shared_params, spec_factory)?;
	let spec = with_default_boot_node::<F>(spec, &cli)?;
	let json = service::chain_ops::build_spec::<FactoryGenesis<F>>(spec, cli.raw)?;

	print!("{}", json);

	Ok(())
}

fn create_config_with_db_path<F, S>(
	spec_factory: S, cli: &SharedParams
) -> error::Result<FactoryFullConfiguration<F>>
where
	F: ServiceFactory,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	let spec = load_spec(cli, spec_factory)?;
	let base_path = base_path(cli);

	let mut config = service::Configuration::default_with_spec(spec.clone());
	config.database_path = db_path(&base_path, spec.id()).to_string_lossy().into();

	Ok(config)
}

fn export_blocks<F, E, S>(
	cli: ExportBlocksCmd,
	spec_factory: S,
	exit: E
) -> error::Result<()>
where
	F: ServiceFactory,
	E: IntoExit,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	let config = create_config_with_db_path::<F, _>(spec_factory, &cli.shared_params)?;

	info!("DB path: {}", config.database_path);
	let from = cli.from.unwrap_or(1);
	let to = cli.to;
	let json = cli.json;

	let file: Box<Write> = match cli.output {
		Some(filename) => Box::new(File::create(filename)?),
		None => Box::new(stdout()),
	};

	service::chain_ops::export_blocks::<F, _, _>(
		config, exit.into_exit(), file, As::sa(from), to.map(As::sa), json
	).map_err(Into::into)
}

fn import_blocks<F, E, S>(
	cli: ImportBlocksCmd,
	spec_factory: S,
	exit: E
) -> error::Result<()>
where
	F: ServiceFactory,
	E: IntoExit,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	let mut config = create_config_with_db_path::<F, _>(spec_factory, &cli.shared_params)?;

	config.block_execution_strategy = cli.execution.into();
	config.api_execution_strategy = cli.api_execution.into();

	let file: Box<Read> = match cli.input {
		Some(filename) => Box::new(File::open(filename)?),
		None => Box::new(stdin()),
	};

	service::chain_ops::import_blocks::<F, _, _>(config, exit.into_exit(), file).map_err(Into::into)
}

fn revert_chain<F, S>(
	cli: RevertCmd,
	spec_factory: S,
) -> error::Result<()>
where
	F: ServiceFactory,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	let config = create_config_with_db_path::<F, _>(spec_factory, &cli.shared_params)?;
	let blocks = cli.num.unwrap_or(256);
	Ok(service::chain_ops::revert_chain::<F>(config, As::sa(blocks))?)
}

fn purge_chain<F, S>(
	cli: PurgeChainCmd,
	spec_factory: S,
) -> error::Result<()>
where
	F: ServiceFactory,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	let config = create_config_with_db_path::<F, _>(spec_factory, &cli.shared_params)?;

	let db_path = config.database_path;
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
	address: &str,
	port: Option<u16>,
) -> Result<SocketAddr, String> {
	let mut address: SocketAddr = address.parse().map_err(
		|_| format!("Invalid address: {}", address)
	)?;
	if let Some(port) = port {
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
		let timestamp =
			time::strftime("%Y-%m-%d %H:%M:%S", &time::now())
				.expect("Error formatting log timestamp");

		let mut output = if log::max_level() <= log::LevelFilter::Info {
			format!("{} {}", Colour::Black.bold().paint(timestamp), record.args())
		} else {
			let name = ::std::thread::current()
				.name()
				.map_or_else(Default::default, |x| format!("{}", Colour::Blue.bold().paint(x)));
			format!(
				"{} {} {} {}  {}",
				Colour::Black.bold().paint(timestamp),
				name,
				record.level(),
				record.target(),
				record.args()
			)
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
