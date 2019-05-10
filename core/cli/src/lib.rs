// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

#[macro_use]
mod traits;
mod params;
pub mod error;
pub mod informant;

use client::ExecutionStrategies;
use runtime_primitives::traits::As;
use service::{
	ServiceFactory, FactoryFullConfiguration, RuntimeGenesis,
	FactoryGenesis, PruningMode, ChainSpec,
};
use network::{
	self, multiaddr::Protocol,
	config::{NetworkConfiguration, NonReservedPeerMode, NodeKeyConfig},
	build_multiaddr,
};
use primitives::H256;

use std::{
	io::{Write, Read, stdin, stdout, ErrorKind}, iter, fs::{self, File}, net::{Ipv4Addr, SocketAddr},
	path::{Path, PathBuf}, str::FromStr,
};

use names::{Generator, Name};
use regex::Regex;
use structopt::{StructOpt, clap::AppSettings};
#[doc(hidden)]
pub use structopt::clap::App;
use params::{
	RunCmd, PurgeChainCmd, RevertCmd, ImportBlocksCmd, ExportBlocksCmd, BuildSpecCmd,
	NetworkConfigurationParams, SharedParams, MergeParameters, TransactionPoolParams,
	NodeKeyParams, NodeKeyType
};
pub use params::{NoCustom, CoreParams};
pub use traits::{GetLogFilter, AugmentClap};
use app_dirs::{AppInfo, AppDataType};
use error_chain::bail;
use log::info;
use lazy_static::lazy_static;

use futures::Future;
use substrate_telemetry::TelemetryEndpoints;

/// The maximum number of characters for a node name.
const NODE_NAME_MAX_LENGTH: usize = 32;

/// The file name of the node's Secp256k1 secret key inside the chain-specific
/// network config directory, if neither `--node-key` nor `--node-key-file`
/// is specified in combination with `--node-key-type=secp256k1`.
const NODE_KEY_SECP256K1_FILE: &str = "secret";

/// The file name of the node's Ed25519 secret key inside the chain-specific
/// network config directory, if neither `--node-key` nor `--node-key-file`
/// is specified in combination with `--node-key-type=ed25519`.
const NODE_KEY_ED25519_FILE: &str = "secret_ed25519";

/// Executable version. Used to pass version information from the root crate.
pub struct VersionInfo {
	/// Implemtation name.
	pub name: &'static str,
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
	/// Support URL.
	pub support_url: &'static str,
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

fn generate_node_name() -> String {
	let result = loop {
		let node_name = Generator::with_naming(Name::Numbered).next().unwrap();
		let count = node_name.chars().count();

		if count < NODE_NAME_MAX_LENGTH {
			break node_name
		}
	};

	result
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

fn base_path(cli: &SharedParams, version: &VersionInfo) -> PathBuf {
	cli.base_path.clone()
		.unwrap_or_else(||
			app_dirs::get_app_root(
				AppDataType::UserData,
				&AppInfo {
					name: version.executable_name,
					author: version.author
				}
			).expect("app directories exist on all supported platforms; qed")
		)
}

fn input_err<T: Into<String>>(msg: T) -> error::Error {
	error::ErrorKind::Input(msg.into()).into()
}

/// Check whether a node name is considered as valid
fn is_node_name_valid(_name: &str) -> Result<(), &str> {
	let name = _name.to_string();
	if name.chars().count() >= NODE_NAME_MAX_LENGTH {
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

/// Parse command line interface arguments and executes the desired command.
///
/// # Return value
///
/// A result that indicates if any error occurred.
/// If no error occurred and a custom subcommand was found, the subcommand is returned.
/// The user needs to handle this subcommand on its own.
///
/// # Remarks
///
/// `CC` is a custom subcommand. This needs to be an `enum`! If no custom subcommand is required,
/// `NoCustom` can be used as type here.
/// `RP` is are custom parameters for the run command. This needs to be a `struct`! The custom
/// parameters are visible to the user as if they were normal run command parameters. If no custom
/// parameters are required, `NoCustom` can be used as type here.
pub fn parse_and_execute<'a, F, CC, RP, S, RS, E, I, T>(
	spec_factory: S,
	version: &VersionInfo,
	impl_name: &'static str,
	args: I,
	exit: E,
	run_service: RS,
) -> error::Result<Option<CC>>
where
	F: ServiceFactory,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
	CC: StructOpt + Clone + GetLogFilter,
	RP: StructOpt + Clone + AugmentClap,
	E: IntoExit,
	RS: FnOnce(E, RunCmd, RP, FactoryFullConfiguration<F>) -> Result<(), String>,
	I: IntoIterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
{
	panic_handler::set(version.support_url);

	let full_version = service::config::full_version_from_strs(
		version.version,
		version.commit
	);

	let matches = CoreParams::<CC, RP>::clap()
		.name(version.executable_name)
		.author(version.author)
		.about(version.description)
		.version(&(full_version + "\n")[..])
		.setting(AppSettings::GlobalVersion)
		.setting(AppSettings::ArgsNegateSubcommands)
		.setting(AppSettings::SubcommandsNegateReqs)
		.get_matches_from(args);
	let cli_args = CoreParams::<CC, RP>::from_clap(&matches);

	init_logger(cli_args.get_log_filter().as_ref().map(|v| v.as_ref()).unwrap_or(""));
	fdlimit::raise_fd_limit();

	match cli_args {
		params::CoreParams::Run(params) => run_node::<F, _, _, _, _>(
			params, spec_factory, exit, run_service, impl_name, version,
		).map(|_| None),
		params::CoreParams::BuildSpec(params) =>
			build_spec::<F, _>(params, spec_factory, version).map(|_| None),
		params::CoreParams::ExportBlocks(params) =>
			export_blocks::<F, _, _>(params, spec_factory, exit, version).map(|_| None),
		params::CoreParams::ImportBlocks(params) =>
			import_blocks::<F, _, _>(params, spec_factory, exit, version).map(|_| None),
		params::CoreParams::PurgeChain(params) =>
			purge_chain::<F, _>(params, spec_factory, version).map(|_| None),
		params::CoreParams::Revert(params) =>
			revert_chain::<F, _>(params, spec_factory, version).map(|_| None),
		params::CoreParams::Custom(params) => Ok(Some(params)),
	}
}

/// Create a `NodeKeyConfig` from the given `NodeKeyParams` in the context
/// of an optional network config storage directory.
fn node_key_config<P>(params: NodeKeyParams, net_config_dir: &Option<P>)
	-> error::Result<NodeKeyConfig>
where
	P: AsRef<Path>
{
	match params.node_key_type {
		NodeKeyType::Secp256k1 =>
			params.node_key.as_ref().map(parse_secp256k1_secret).unwrap_or_else(||
				Ok(params.node_key_file
					.or_else(|| net_config_file(net_config_dir, NODE_KEY_SECP256K1_FILE))
					.map(network::Secret::File)
					.unwrap_or(network::Secret::New)))
				.map(NodeKeyConfig::Secp256k1),

		NodeKeyType::Ed25519 =>
			params.node_key.as_ref().map(parse_ed25519_secret).unwrap_or_else(||
				Ok(params.node_key_file
					.or_else(|| net_config_file(net_config_dir, NODE_KEY_ED25519_FILE))
					.map(network::Secret::File)
					.unwrap_or(network::Secret::New)))
				.map(NodeKeyConfig::Ed25519)
	}
}

fn net_config_file<P>(net_config_dir: &Option<P>, name: &str) -> Option<PathBuf>
where
	P: AsRef<Path>
{
	net_config_dir.as_ref().map(|d| d.as_ref().join(name))
}

/// Create an error caused by an invalid node key argument.
fn invalid_node_key(e: impl std::fmt::Display) -> error::Error {
	input_err(format!("Invalid node key: {}", e))
}

/// Parse a Secp256k1 secret key from a hex string into a `network::Secret`.
fn parse_secp256k1_secret(hex: &String) -> error::Result<network::Secp256k1Secret> {
	H256::from_str(hex).map_err(invalid_node_key).and_then(|bytes|
		network::identity::secp256k1::SecretKey::from_bytes(bytes)
			.map(network::Secret::Input)
			.map_err(invalid_node_key))
}

/// Parse a Ed25519 secret key from a hex string into a `network::Secret`.
fn parse_ed25519_secret(hex: &String) -> error::Result<network::Ed25519Secret> {
	H256::from_str(&hex).map_err(invalid_node_key).and_then(|bytes|
		network::identity::ed25519::SecretKey::from_bytes(bytes)
			.map(network::Secret::Input)
			.map_err(invalid_node_key))
}

/// Fill the given `PoolConfiguration` by looking at the cli parameters.
fn fill_transaction_pool_configuration<F: ServiceFactory>(
	options: &mut FactoryFullConfiguration<F>,
	params: TransactionPoolParams,
) -> error::Result<()> {
	// ready queue
	options.transaction_pool.ready.count = params.pool_limit;
	options.transaction_pool.ready.total_bytes = params.pool_kbytes * 1024;

	// future queue
	let factor = 10;
	options.transaction_pool.future.count = params.pool_limit / factor;
	options.transaction_pool.future.total_bytes = params.pool_kbytes * 1024 / factor;

	Ok(())
}

/// Fill the given `NetworkConfiguration` by looking at the cli parameters.
fn fill_network_configuration(
	cli: NetworkConfigurationParams,
	base_path: &Path,
	chain_spec_id: &str,
	config: &mut NetworkConfiguration,
	client_id: String,
	is_dev: bool,
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
	config.node_key = node_key_config(cli.node_key_params, &config.net_config_path)?;

	config.in_peers = cli.in_peers;
	config.out_peers = cli.out_peers;

	config.enable_mdns = !is_dev && !cli.no_mdns;

	Ok(())
}

fn create_run_node_config<F, S>(
	cli: RunCmd, spec_factory: S, impl_name: &'static str, version: &VersionInfo
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

	config.name = match cli.name.or(cli.keyring.account.map(|a| a.to_string())) {
		None => generate_node_name(),
		Some(name) => name,
	};
	match is_node_name_valid(&config.name) {
		Ok(_) => (),
		Err(msg) => bail!(
			input_err(
				format!("Invalid node name '{}'. Reason: {}. If unsure, use none.",
					config.name,
					msg
				)
			)
		)
	}

	let base_path = base_path(&cli.shared_params, version);

	config.keystore_path = cli.keystore_path
		.unwrap_or_else(|| keystore_path(&base_path, config.chain_spec.id()))
		.to_string_lossy()
		.into();

	config.database_path =
		db_path(&base_path, config.chain_spec.id()).to_string_lossy().into();
	config.database_cache_size = cli.database_cache_size;
	config.state_cache_size = cli.state_cache_size;
	config.pruning = match cli.pruning {
		Some(ref s) if s == "archive" => PruningMode::ArchiveAll,
		None => PruningMode::default(),
		Some(s) => PruningMode::keep_blocks(
			s.parse().map_err(|_| input_err("Invalid pruning mode specified"))?
		),
	};

	let role =
		if cli.light {
			service::Roles::LIGHT
		} else if cli.validator || cli.shared_params.dev {
			service::Roles::AUTHORITY
		} else {
			service::Roles::FULL
		};

	let exec = cli.execution_strategies;
	config.execution_strategies = ExecutionStrategies {
		syncing: exec.syncing_execution.into(),
		importing: exec.importing_execution.into(),
		block_construction: exec.block_construction_execution.into(),
		offchain_worker: exec.offchain_worker_execution.into(),
		other: exec.other_execution.into(),
	};

	config.offchain_worker = match (cli.offchain_worker, role) {
		(params::OffchainWorkerEnabled::WhenValidating, service::Roles::AUTHORITY) => true,
		(params::OffchainWorkerEnabled::Always, _) => true,
		(params::OffchainWorkerEnabled::Never, _) => false,
		(params::OffchainWorkerEnabled::WhenValidating, _) => false,
	};

	config.roles = role;
	config.disable_grandpa = cli.no_grandpa;

	let is_dev = cli.shared_params.dev;

	let client_id = config.client_id();
	fill_network_configuration(
		cli.network_config,
		&base_path,
		spec.id(),
		&mut config.network,
		client_id,
		is_dev,
	)?;

	fill_transaction_pool_configuration::<F>(
		&mut config,
		cli.pool_config,
	)?;

	if let Some(key) = cli.key {
		config.keys.push(key);
	}

	if cli.shared_params.dev {
		config.keys.push("//Alice".into());
	}

	if let Some(account) = cli.keyring.account {
		config.keys.push(format!("//{}", account));
	}

	let rpc_interface: &str = if cli.rpc_external { "0.0.0.0" } else { "127.0.0.1" };
	let ws_interface: &str = if cli.ws_external { "0.0.0.0" } else { "127.0.0.1" };

	config.rpc_http = Some(
		parse_address(&format!("{}:{}", rpc_interface, 9933), cli.rpc_port)?
	);
	config.rpc_ws = Some(
		parse_address(&format!("{}:{}", ws_interface, 9944), cli.ws_port)?
	);
	config.rpc_cors = cli.rpc_cors.unwrap_or_else(|| if is_dev {
		log::warn!("Running in --dev mode, RPC CORS has been disabled.");
		None
	} else {
		Some(vec![
			"http://localhost:*".into(),
			"http://127.0.0.1:*".into(),
			"https://localhost:*".into(),
			"https://127.0.0.1:*".into(),
			"https://polkadot.js.org".into(),
			"https://substrate-ui.parity.io".into(),
		])
	});

	// Override telemetry
	if cli.no_telemetry {
		config.telemetry_endpoints = None;
	} else if !cli.telemetry_endpoints.is_empty() {
		config.telemetry_endpoints = Some(TelemetryEndpoints::new(cli.telemetry_endpoints));
	}

	// Imply forced authoring on --dev
	config.force_authoring = cli.shared_params.dev || cli.force_authoring;

	Ok(config)
}

fn run_node<F, S, RS, E, RP>(
	cli: MergeParameters<RunCmd, RP>,
	spec_factory: S,
	exit: E,
	run_service: RS,
	impl_name: &'static str,
	version: &VersionInfo,
) -> error::Result<()>
where
	RP: StructOpt + Clone,
	F: ServiceFactory,
	E: IntoExit,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
	RS: FnOnce(E, RunCmd, RP, FactoryFullConfiguration<F>) -> Result<(), String>,
 {
	let config = create_run_node_config::<F, _>(cli.left.clone(), spec_factory, impl_name, version)?;

	run_service(exit, cli.left, cli.right, config).map_err(Into::into)
}

//
// IANA unassigned port ranges that we could use:
// 6717-6766		Unassigned
// 8504-8553		Unassigned
// 9556-9591		Unassigned
// 9803-9874		Unassigned
// 9926-9949		Unassigned

fn with_default_boot_node<F>(
	spec: &mut ChainSpec<FactoryGenesis<F>>,
	cli: BuildSpecCmd,
	version: &VersionInfo,
) -> error::Result<()>
where
	F: ServiceFactory
{
	if spec.boot_nodes().is_empty() {
		let base_path = base_path(&cli.shared_params, version);
		let storage_path = network_path(&base_path, spec.id());
		let node_key = node_key_config(cli.node_key_params, &Some(storage_path))?;
		let keys = node_key.into_keypair()?;
		let peer_id = keys.public().into_peer_id();
		let addr = build_multiaddr![
			Ip4([127, 0, 0, 1]),
			Tcp(30333u16),
			P2p(peer_id)
		];
		spec.add_boot_node(addr)
	}
	Ok(())
}

fn build_spec<F, S>(
	cli: BuildSpecCmd,
	spec_factory: S,
	version: &VersionInfo,
) -> error::Result<()>
where
	F: ServiceFactory,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	info!("Building chain spec");
	let raw_output = cli.raw;
	let mut spec = load_spec(&cli.shared_params, spec_factory)?;
	with_default_boot_node::<F>(&mut spec, cli, version)?;
	let json = service::chain_ops::build_spec::<FactoryGenesis<F>>(spec, raw_output)?;

	print!("{}", json);

	Ok(())
}

fn create_config_with_db_path<F, S>(
	spec_factory: S, cli: &SharedParams, version: &VersionInfo,
) -> error::Result<FactoryFullConfiguration<F>>
where
	F: ServiceFactory,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	let spec = load_spec(cli, spec_factory)?;
	let base_path = base_path(cli, version);

	let mut config = service::Configuration::default_with_spec(spec.clone());
	config.database_path = db_path(&base_path, spec.id()).to_string_lossy().into();

	Ok(config)
}

fn export_blocks<F, E, S>(
	cli: ExportBlocksCmd,
	spec_factory: S,
	exit: E,
	version: &VersionInfo,
) -> error::Result<()>
where
	F: ServiceFactory,
	E: IntoExit,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	let config = create_config_with_db_path::<F, _>(spec_factory, &cli.shared_params, version)?;

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
	exit: E,
	version: &VersionInfo,
) -> error::Result<()>
where
	F: ServiceFactory,
	E: IntoExit,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	let config = create_config_with_db_path::<F, _>(spec_factory, &cli.shared_params, version)?;

	let file: Box<Read> = match cli.input {
		Some(filename) => Box::new(File::open(filename)?),
		None => Box::new(stdin()),
	};

	service::chain_ops::import_blocks::<F, _, _>(config, exit.into_exit(), file).map_err(Into::into)
}

fn revert_chain<F, S>(
	cli: RevertCmd,
	spec_factory: S,
	version: &VersionInfo,
) -> error::Result<()>
where
	F: ServiceFactory,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	let config = create_config_with_db_path::<F, _>(spec_factory, &cli.shared_params, version)?;
	let blocks = cli.num;
	Ok(service::chain_ops::revert_chain::<F>(config, As::sa(blocks))?)
}

fn purge_chain<F, S>(
	cli: PurgeChainCmd,
	spec_factory: S,
	version: &VersionInfo,
) -> error::Result<()>
where
	F: ServiceFactory,
	S: FnOnce(&str) -> Result<Option<ChainSpec<FactoryGenesis<F>>>, String>,
{
	let config = create_config_with_db_path::<F, _>(spec_factory, &cli.shared_params, version)?;
	let db_path = config.database_path;

	if cli.yes == false {
		print!("Are you sure to remove {:?}? (y/n)", &db_path);
		stdout().flush().expect("failed to flush stdout");

		let mut input = String::new();
		stdin().read_line(&mut input)?;
		let input = input.trim();

		match input.chars().nth(0) {
			Some('y') | Some('Y') => {},
			_ => {
				println!("Aborted");
				return Ok(());
			},
		}
	}

	match fs::remove_dir_all(&db_path) {
		Result::Ok(_) => {
			println!("{:?} removed.", &db_path);
			Ok(())
		},
		Result::Err(ref err) if err.kind() == ErrorKind::NotFound => {
			println!("{:?} did not exist.", &db_path);
			Ok(())
		},
		Result::Err(err) => Result::Err(err.into())
	}
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

fn init_logger(pattern: &str) {
	use ansi_term::Colour;

	let mut builder = env_logger::Builder::new();
	// Disable info logging by default for some modules:
	builder.filter(Some("ws"), log::LevelFilter::Off);
	builder.filter(Some("hyper"), log::LevelFilter::Warn);
	// Enable info for others.
	builder.filter(None, log::LevelFilter::Info);

	if let Ok(lvl) = std::env::var("RUST_LOG") {
		builder.parse_filters(&lvl);
	}

	builder.parse_filters(pattern);
	let isatty = atty::is(atty::Stream::Stderr);
	let enable_color = isatty;

	builder.format(move |buf, record| {
		let now = time::now();
		let timestamp =
			time::strftime("%Y-%m-%d %H:%M:%S", &now)
				.expect("Error formatting log timestamp");

		let mut output = if log::max_level() <= log::LevelFilter::Info {
			format!("{} {}", Colour::Black.bold().paint(timestamp), record.args())
		} else {
			let name = ::std::thread::current()
				.name()
				.map_or_else(Default::default, |x| format!("{}", Colour::Blue.bold().paint(x)));
			let millis = (now.tm_nsec as f32 / 1000000.0).round() as usize;
			let timestamp = format!("{}.{:03}", timestamp, millis);
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
	use tempdir::TempDir;
	use network::identity::{secp256k1, ed25519};

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

	#[test]
	fn test_node_key_config_input() {
		fn secret_input(net_config_dir: Option<String>) -> error::Result<()> {
			NodeKeyType::variants().into_iter().try_for_each(|t| {
				let node_key_type = NodeKeyType::from_str(t).unwrap();
				let sk = match node_key_type {
					NodeKeyType::Secp256k1 => secp256k1::SecretKey::generate().as_ref().to_vec(),
					NodeKeyType::Ed25519 => ed25519::SecretKey::generate().as_ref().to_vec()
				};
				let params = NodeKeyParams {
					node_key_type,
					node_key: Some(format!("{:x}", H256::from_slice(sk.as_ref()))),
					node_key_file: None
				};
				node_key_config(params, &net_config_dir).and_then(|c| match c {
					NodeKeyConfig::Secp256k1(network::Secret::Input(ref ski))
						if node_key_type == NodeKeyType::Secp256k1 &&
							&sk[..] == ski.as_ref() => Ok(()),
					NodeKeyConfig::Ed25519(network::Secret::Input(ref ski))
						if node_key_type == NodeKeyType::Ed25519 &&
							&sk[..] == ski.as_ref() => Ok(()),
					_ => Err(input_err("Unexpected node key config"))
				})
			})
		}

		assert!(secret_input(None).is_ok());
		assert!(secret_input(Some("x".to_string())).is_ok());
	}

	#[test]
	fn test_node_key_config_file() {
		fn secret_file(net_config_dir: Option<String>) -> error::Result<()> {
			NodeKeyType::variants().into_iter().try_for_each(|t| {
				let node_key_type = NodeKeyType::from_str(t).unwrap();
				let tmp = TempDir::new("alice")?;
				let file = tmp.path().join(format!("{}_mysecret", t)).to_path_buf();
				let params = NodeKeyParams {
					node_key_type,
					node_key: None,
					node_key_file: Some(file.clone())
				};
				node_key_config(params, &net_config_dir).and_then(|c| match c {
					NodeKeyConfig::Secp256k1(network::Secret::File(ref f))
						if node_key_type == NodeKeyType::Secp256k1 && f == &file => Ok(()),
					NodeKeyConfig::Ed25519(network::Secret::File(ref f))
						if node_key_type == NodeKeyType::Ed25519 && f == &file => Ok(()),
					_ => Err(input_err("Unexpected node key config"))
				})
			})
		}

		assert!(secret_file(None).is_ok());
		assert!(secret_file(Some("x".to_string())).is_ok());
	}

	#[test]
	fn test_node_key_config_default() {
		fn with_def_params<F>(f: F) -> error::Result<()>
		where
			F: Fn(NodeKeyParams) -> error::Result<()>
		{
			NodeKeyType::variants().into_iter().try_for_each(|t| {
				let node_key_type = NodeKeyType::from_str(t).unwrap();
				f(NodeKeyParams {
					node_key_type,
					node_key: None,
					node_key_file: None
				})
			})
		}

		fn no_config_dir() -> error::Result<()> {
			with_def_params(|params| {
				let typ = params.node_key_type;
				node_key_config::<String>(params, &None)
					.and_then(|c| match c {
						NodeKeyConfig::Secp256k1(network::Secret::New)
							if typ == NodeKeyType::Secp256k1 => Ok(()),
						NodeKeyConfig::Ed25519(network::Secret::New)
							if typ == NodeKeyType::Ed25519 => Ok(()),
						_ => Err(input_err("Unexpected node key config"))
					})
			})
		}

		fn some_config_dir(net_config_dir: String) -> error::Result<()> {
			with_def_params(|params| {
				let dir = PathBuf::from(net_config_dir.clone());
				let typ = params.node_key_type;
				node_key_config(params, &Some(net_config_dir.clone()))
					.and_then(move |c| match c {
						NodeKeyConfig::Secp256k1(network::Secret::File(ref f))
							if typ == NodeKeyType::Secp256k1 &&
								f == &dir.join(NODE_KEY_SECP256K1_FILE) => Ok(()),
						NodeKeyConfig::Ed25519(network::Secret::File(ref f))
							if typ == NodeKeyType::Ed25519 &&
								f == &dir.join(NODE_KEY_ED25519_FILE) => Ok(()),
						_ => Err(input_err("Unexpected node key config"))
				})
			})
		}

		assert!(no_config_dir().is_ok());
		assert!(some_config_dir("x".to_string()).is_ok());
	}
}
