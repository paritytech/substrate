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
mod execution_strategy;
pub mod error;
pub mod informant;

use client::ExecutionStrategies;
use service::{
	config::{Configuration, DatabaseConfig},
	ServiceBuilderExport, ServiceBuilderImport, ServiceBuilderRevert,
	RuntimeGenesis, ChainSpecExtension, PruningMode, ChainSpec,
};
use network::{
	self,
	multiaddr::Protocol,
	config::{
		NetworkConfiguration, TransportConfig, NonReservedPeerMode, NodeKeyConfig, build_multiaddr
	},
};
use primitives::H256;

use std::{
	io::{Write, Read, Seek, Cursor, stdin, stdout, ErrorKind}, iter, fs::{self, File},
	net::{Ipv4Addr, SocketAddr}, path::{Path, PathBuf}, str::FromStr,
};

use names::{Generator, Name};
use regex::Regex;
use structopt::{StructOpt, clap::AppSettings};
#[doc(hidden)]
pub use structopt::clap::App;
use params::{
	RunCmd, PurgeChainCmd, RevertCmd, ImportBlocksCmd, ExportBlocksCmd, BuildSpecCmd,
	NetworkConfigurationParams, MergeParameters, TransactionPoolParams,
	NodeKeyParams, NodeKeyType, Cors,
};
pub use params::{NoCustom, CoreParams, SharedParams, ExecutionStrategy as ExecutionStrategyParam};
pub use traits::{GetLogFilter, AugmentClap};
use app_dirs::{AppInfo, AppDataType};
use log::info;
use lazy_static::lazy_static;

use futures::Future;
use substrate_telemetry::TelemetryEndpoints;

/// default sub directory to store network config
const DEFAULT_NETWORK_CONFIG_PATH : &'static str = "network";
/// default sub directory to store database
const DEFAULT_DB_CONFIG_PATH : &'static str = "db";
/// default sub directory for the key store
const DEFAULT_KEYSTORE_CONFIG_PATH : &'static str =  "keystore";

/// The maximum number of characters for a node name.
const NODE_NAME_MAX_LENGTH: usize = 32;

/// The file name of the node's Ed25519 secret key inside the chain-specific
/// network config directory, if neither `--node-key` nor `--node-key-file`
/// is specified in combination with `--node-key-type=ed25519`.
const NODE_KEY_ED25519_FILE: &str = "secret_ed25519";

/// Executable version. Used to pass version information from the root crate.
#[derive(Clone)]
pub struct VersionInfo {
	/// Implementaiton name.
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

fn load_spec<F, G, E>(cli: &SharedParams, factory: F) -> error::Result<ChainSpec<G, E>> where
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	F: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
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

/// Parse command line interface arguments and prepares the command for execution.
///
/// Before returning, this function performs various initializations, such as initializing the
/// panic handler and the logger, or increasing the limit for file descriptors.
///
/// # Remarks
///
/// `CC` is a custom subcommand. This needs to be an `enum`! If no custom subcommand is required,
/// `NoCustom` can be used as type here.
///
/// `RP` are custom parameters for the run command. This needs to be a `struct`! The custom
/// parameters are visible to the user as if they were normal run command parameters. If no custom
/// parameters are required, `NoCustom` can be used as type here.
pub fn parse_and_prepare<'a, CC, RP, I>(
	version: &'a VersionInfo,
	impl_name: &'static str,
	args: I,
) -> ParseAndPrepare<'a, CC, RP>
where
	CC: StructOpt + Clone + GetLogFilter,
	RP: StructOpt + Clone + AugmentClap,
	I: IntoIterator,
	<I as IntoIterator>::Item: Into<std::ffi::OsString> + Clone,
{
	let full_version = service::config::full_version_from_strs(
		version.version,
		version.commit
	);

	panic_handler::set(version.support_url, &full_version);

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
		params::CoreParams::Run(params) => ParseAndPrepare::Run(
			ParseAndPrepareRun { params, impl_name, version }
		),
		params::CoreParams::BuildSpec(params) => ParseAndPrepare::BuildSpec(
			ParseAndPrepareBuildSpec { params, version }
		),
		params::CoreParams::ExportBlocks(params) => ParseAndPrepare::ExportBlocks(
			ParseAndPrepareExport { params, version }
		),
		params::CoreParams::ImportBlocks(params) => ParseAndPrepare::ImportBlocks(
			ParseAndPrepareImport { params, version }
		),
		params::CoreParams::PurgeChain(params) => ParseAndPrepare::PurgeChain(
			ParseAndPreparePurge { params, version }
		),
		params::CoreParams::Revert(params) => ParseAndPrepare::RevertChain(
			ParseAndPrepareRevert { params, version }
		),
		params::CoreParams::Custom(params) => ParseAndPrepare::CustomCommand(params),
	}
}

/// Returns a string displaying the node role, special casing the sentry mode
/// (returning `SENTRY`), since the node technically has an `AUTHORITY` role but
/// doesn't participate.
pub fn display_role<A, B, C>(config: &Configuration<A, B, C>) -> String {
	if config.sentry_mode {
		"SENTRY".to_string()
	} else {
		format!("{:?}", config.roles)
	}
}

/// Output of calling `parse_and_prepare`.
#[must_use]
pub enum ParseAndPrepare<'a, CC, RP> {
	/// Command ready to run the main client.
	Run(ParseAndPrepareRun<'a, RP>),
	/// Command ready to build chain specs.
	BuildSpec(ParseAndPrepareBuildSpec<'a>),
	/// Command ready to export the chain.
	ExportBlocks(ParseAndPrepareExport<'a>),
	/// Command ready to import the chain.
	ImportBlocks(ParseAndPrepareImport<'a>),
	/// Command ready to purge the chain.
	PurgeChain(ParseAndPreparePurge<'a>),
	/// Command ready to revert the chain.
	RevertChain(ParseAndPrepareRevert<'a>),
	/// An additional custom command passed to `parse_and_prepare`.
	CustomCommand(CC),
}

/// Command ready to run the main client.
pub struct ParseAndPrepareRun<'a, RP> {
	params: MergeParameters<RunCmd, RP>,
	impl_name: &'static str,
	version: &'a VersionInfo,
}

impl<'a, RP> ParseAndPrepareRun<'a, RP> {
	/// Runs the command and runs the main client.
	pub fn run<C, G, CE, S, Exit, RS, E>(
		self,
		spec_factory: S,
		exit: Exit,
		run_service: RS,
	) -> error::Result<()>
	where
		S: FnOnce(&str) -> Result<Option<ChainSpec<G, CE>>, String>,
		E: Into<error::Error>,
		RP: StructOpt + Clone,
		C: Default,
		G: RuntimeGenesis,
		CE: ChainSpecExtension,
		Exit: IntoExit,
		RS: FnOnce(Exit, RunCmd, RP, Configuration<C, G, CE>) -> Result<(), E>
	{
		let config = create_run_node_config(
			self.params.left.clone(), spec_factory, self.impl_name, self.version,
		)?;

		run_service(exit, self.params.left, self.params.right, config).map_err(Into::into)
	}
}

/// Command ready to build chain specs.
pub struct ParseAndPrepareBuildSpec<'a> {
	params: BuildSpecCmd,
	version: &'a VersionInfo,
}

impl<'a> ParseAndPrepareBuildSpec<'a> {
	/// Runs the command and build the chain specs.
	pub fn run<C, G, S, E>(
		self,
		spec_factory: S
	) -> error::Result<()> where
		S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
		C: Default,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		info!("Building chain spec");
		let raw_output = self.params.raw;
		let mut spec = load_spec(&self.params.shared_params, spec_factory)?;

		if spec.boot_nodes().is_empty() && !self.params.disable_default_bootnode {
			let base_path = base_path(&self.params.shared_params, self.version);
			let cfg = service::Configuration::<C,_,_>::default_with_spec_and_base_path(spec.clone(), Some(base_path));
			let node_key = node_key_config(
				self.params.node_key_params,
				&Some(cfg.in_chain_config_dir(DEFAULT_NETWORK_CONFIG_PATH).expect("We provided a base_path"))
			)?;
			let keys = node_key.into_keypair()?;
			let peer_id = keys.public().into_peer_id();
			let addr = build_multiaddr![
				Ip4([127, 0, 0, 1]),
				Tcp(30333u16),
				P2p(peer_id)
			];
			spec.add_boot_node(addr)
		}

		let json = service::chain_ops::build_spec(spec, raw_output)?;

		print!("{}", json);

		Ok(())
	}
}

/// Command ready to export the chain.
pub struct ParseAndPrepareExport<'a> {
	params: ExportBlocksCmd,
	version: &'a VersionInfo,
}

impl<'a> ParseAndPrepareExport<'a> {
	/// Runs the command and exports from the chain.
	pub fn run_with_builder<C, G, E, F, B, S, Exit>(
		self,
		builder: F,
		spec_factory: S,
		exit: Exit,
	) -> error::Result<()>
	where S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
		F: FnOnce(Configuration<C, G, E>) -> Result<B, error::Error>,
		B: ServiceBuilderExport,
		C: Default,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		Exit: IntoExit
	{
		let config = create_config_with_db_path(spec_factory, &self.params.shared_params, self.version)?;

		if let DatabaseConfig::Path { ref path, .. } = &config.database {
			info!("DB path: {}", path.display());
		}
		let from = self.params.from.unwrap_or(1);
		let to = self.params.to;
		let json = self.params.json;

		let file: Box<dyn Write> = match self.params.output {
			Some(filename) => Box::new(File::create(filename)?),
			None => Box::new(stdout()),
		};

		builder(config)?.export_blocks(exit.into_exit(), file, from.into(), to.map(Into::into), json)?;
		Ok(())
	}
}

/// Command ready to import the chain.
pub struct ParseAndPrepareImport<'a> {
	params: ImportBlocksCmd,
	version: &'a VersionInfo,
}

impl<'a> ParseAndPrepareImport<'a> {
	/// Runs the command and imports to the chain.
	pub fn run_with_builder<C, G, E, F, B, S, Exit>(
		self,
		builder: F,
		spec_factory: S,
		exit: Exit,
	) -> error::Result<()>
	where S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
		F: FnOnce(Configuration<C, G, E>) -> Result<B, error::Error>,
		B: ServiceBuilderImport,
		C: Default,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		Exit: IntoExit
	{
		let mut config = create_config_with_db_path(spec_factory, &self.params.shared_params, self.version)?;
		config.wasm_method = self.params.wasm_method.into();
		config.execution_strategies = ExecutionStrategies {
			importing: self.params.execution.into(),
			other: self.params.execution.into(),
			..Default::default()
		};

		let file: Box<dyn ReadPlusSeek> = match self.params.input {
			Some(filename) => Box::new(File::open(filename)?),
			None => {
				let mut buffer = Vec::new();
				stdin().read_to_end(&mut buffer)?;
				Box::new(Cursor::new(buffer))
			},
		};

		let fut = builder(config)?.import_blocks(exit.into_exit(), file)?;
		tokio::run(fut);
		Ok(())
	}
}

/// Command ready to purge the chain.
pub struct ParseAndPreparePurge<'a> {
	params: PurgeChainCmd,
	version: &'a VersionInfo,
}

impl<'a> ParseAndPreparePurge<'a> {
	/// Runs the command and purges the chain.
	pub fn run<G, E, S>(
		self,
		spec_factory: S
	) -> error::Result<()> where
		S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		let config = create_config_with_db_path::<(), _, _, _>(
			spec_factory, &self.params.shared_params, self.version
		)?;
		let db_path = match config.database {
			DatabaseConfig::Path { path, .. } => path,
			_ => {
				eprintln!("Cannot purge custom database implementation");
				return Ok(());
			}
		};

		if !self.params.yes {
			print!("Are you sure to remove {:?}? [y/N]: ", &db_path);
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
				eprintln!("{:?} did not exist.", &db_path);
				Ok(())
			},
			Result::Err(err) => Result::Err(err.into())
		}
	}
}

/// Command ready to revert the chain.
pub struct ParseAndPrepareRevert<'a> {
	params: RevertCmd,
	version: &'a VersionInfo,
}

impl<'a> ParseAndPrepareRevert<'a> {
	/// Runs the command and reverts the chain.
	pub fn run_with_builder<C, G, E, F, B, S>(
		self,
		builder: F,
		spec_factory: S
	) -> error::Result<()> where
		S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
		F: FnOnce(Configuration<C, G, E>) -> Result<B, error::Error>,
		B: ServiceBuilderRevert,
		C: Default,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		let config = create_config_with_db_path(
			spec_factory, &self.params.shared_params, self.version
		)?;
		let blocks = self.params.num;
		builder(config)?.revert_chain(blocks.into())?;
		Ok(())
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
		NodeKeyType::Ed25519 =>
			params.node_key.as_ref().map(parse_ed25519_secret).unwrap_or_else(||
				Ok(params.node_key_file
					.or_else(|| net_config_file(net_config_dir, NODE_KEY_ED25519_FILE))
					.map(network::config::Secret::File)
					.unwrap_or(network::config::Secret::New)))
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
	error::Error::Input(format!("Invalid node key: {}", e))
}

/// Parse a Ed25519 secret key from a hex string into a `network::Secret`.
fn parse_ed25519_secret(hex: &String) -> error::Result<network::config::Ed25519Secret> {
	H256::from_str(&hex).map_err(invalid_node_key).and_then(|bytes|
		network::config::identity::ed25519::SecretKey::from_bytes(bytes)
			.map(network::config::Secret::Input)
			.map_err(invalid_node_key))
}

/// Fill the given `PoolConfiguration` by looking at the cli parameters.
fn fill_transaction_pool_configuration<C, G, E>(
	options: &mut Configuration<C, G, E>,
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
	config_path: PathBuf,
	config: &mut NetworkConfiguration,
	client_id: String,
	is_dev: bool,
) -> error::Result<()> {
	config.boot_nodes.extend(cli.bootnodes.into_iter());
	config.config_path = Some(config_path.to_string_lossy().into());
	config.net_config_path = config.config_path.clone();
	config.reserved_nodes.extend(cli.reserved_nodes.into_iter());

	if cli.reserved_only {
		config.non_reserved_mode = NonReservedPeerMode::Deny;
	}

	for addr in cli.listen_addr.iter() {
		let addr = addr.parse().ok().ok_or(error::Error::InvalidListenMultiaddress)?;
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

	config.transport = TransportConfig::Normal {
		enable_mdns: !is_dev && !cli.no_mdns,
		allow_private_ipv4: !cli.no_private_ipv4,
		wasm_external_transport: None,
	};

	config.max_parallel_downloads = cli.max_parallel_downloads;

	Ok(())
}

fn input_keystore_password() -> Result<String, String> {
	rpassword::read_password_from_tty(Some("Keystore password: "))
		.map_err(|e| format!("{:?}", e))
}

/// Fill the password field of the given config instance.
fn fill_config_keystore_password<C, G, E>(
	config: &mut service::Configuration<C, G, E>,
	cli: &RunCmd,
) -> Result<(), String> {
	config.keystore_password = if cli.password_interactive {
		Some(input_keystore_password()?.into())
	} else if let Some(ref file) = cli.password_filename {
		Some(fs::read_to_string(file).map_err(|e| format!("{}", e))?.into())
	} else if let Some(ref password) = cli.password {
		Some(password.clone().into())
	} else {
		None
	};

	Ok(())
}

fn create_run_node_config<C, G, E, S>(
	cli: RunCmd, spec_factory: S, impl_name: &'static str, version: &VersionInfo,
) -> error::Result<Configuration<C, G, E>>
where
	C: Default,
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
{
	let spec = load_spec(&cli.shared_params, spec_factory)?;
	let base_path = base_path(&cli.shared_params, &version);
	let mut config = service::Configuration::default_with_spec_and_base_path(spec.clone(), Some(base_path));

	fill_config_keystore_password(&mut config, &cli)?;

	config.impl_name = impl_name;
	config.impl_commit = version.commit;
	config.impl_version = version.version;

	config.name = match cli.name.or(cli.keyring.account.map(|a| a.to_string())) {
		None => generate_node_name(),
		Some(name) => name,
	};
	match is_node_name_valid(&config.name) {
		Ok(_) => (),
		Err(msg) => Err(
			error::Error::Input(
				format!("Invalid node name '{}'. Reason: {}. If unsure, use none.",
					config.name,
					msg
				)
			)
		)?
	}

	config.keystore_path = cli.keystore_path.or_else(|| config.in_chain_config_dir(DEFAULT_KEYSTORE_CONFIG_PATH));

	config.database = DatabaseConfig::Path {
		path: config.in_chain_config_dir(DEFAULT_DB_CONFIG_PATH).expect("We provided a base_path."),
		cache_size: cli.database_cache_size,
	};
	config.state_cache_size = cli.state_cache_size;

	let is_dev = cli.shared_params.dev;
	let is_authority = cli.validator || cli.sentry || is_dev || cli.keyring.account.is_some();

	let role =
		if cli.light {
			service::Roles::LIGHT
		} else if is_authority {
			service::Roles::AUTHORITY
		} else {
			service::Roles::FULL
		};

	// set sentry mode (i.e. act as an authority but **never** actively participate)
	config.sentry_mode = cli.sentry;

	// by default we disable pruning if the node is an authority (i.e.
	// `ArchiveAll`), otherwise we keep state for the last 256 blocks. if the
	// node is an authority and pruning is enabled explicitly, then we error
	// unless `unsafe_pruning` is set.
	config.pruning = match cli.pruning {
		Some(ref s) if s == "archive" => PruningMode::ArchiveAll,
		None if role == service::Roles::AUTHORITY => PruningMode::ArchiveAll,
		None => PruningMode::default(),
		Some(s) => {
			if role == service::Roles::AUTHORITY && !cli.unsafe_pruning {
				return Err(error::Error::Input(
					"Validators should run with state pruning disabled (i.e. archive). \
					You can ignore this check with `--unsafe-pruning`.".to_string()
				));
			}

			PruningMode::keep_blocks(s.parse()
				.map_err(|_| error::Error::Input("Invalid pruning mode specified".to_string()))?
			)
		},
	};

	config.wasm_method = cli.wasm_method.into();

	let exec = cli.execution_strategies;
	let exec_all_or = |strat: params::ExecutionStrategy| exec.execution.unwrap_or(strat).into();
	config.execution_strategies = ExecutionStrategies {
		syncing: exec_all_or(exec.execution_syncing),
		importing: exec_all_or(exec.execution_import_block),
		block_construction: exec_all_or(exec.execution_block_construction),
		offchain_worker: exec_all_or(exec.execution_offchain_worker),
		other: exec_all_or(exec.execution_other),
	};

	config.offchain_worker = match (cli.offchain_worker, role) {
		(params::OffchainWorkerEnabled::WhenValidating, service::Roles::AUTHORITY) => true,
		(params::OffchainWorkerEnabled::Always, _) => true,
		(params::OffchainWorkerEnabled::Never, _) => false,
		(params::OffchainWorkerEnabled::WhenValidating, _) => false,
	};

	config.roles = role;
	config.disable_grandpa = cli.no_grandpa;

	let client_id = config.client_id();
	fill_network_configuration(
		cli.network_config,
		config.in_chain_config_dir(DEFAULT_NETWORK_CONFIG_PATH).expect("We provided a basepath"),
		&mut config.network,
		client_id,
		is_dev,
	)?;

	fill_transaction_pool_configuration(&mut config, cli.pool_config)?;

	config.dev_key_seed = cli.keyring.account
		.map(|a| format!("//{}", a)).or_else(|| {
			if is_dev {
				Some("//Alice".into())
			} else {
				None
			}
		});

	let rpc_interface: &str = if cli.rpc_external { "0.0.0.0" } else { "127.0.0.1" };
	let ws_interface: &str = if cli.ws_external { "0.0.0.0" } else { "127.0.0.1" };

	config.rpc_http = Some(parse_address(&format!("{}:{}", rpc_interface, 9933), cli.rpc_port)?);
	config.rpc_ws = Some(parse_address(&format!("{}:{}", ws_interface, 9944), cli.ws_port)?);

	config.rpc_ws_max_connections = cli.ws_max_connections;
	config.rpc_cors = cli.rpc_cors.unwrap_or_else(|| if is_dev {
		log::warn!("Running in --dev mode, RPC CORS has been disabled.");
		Cors::All
	} else {
		Cors::List(vec![
			"http://localhost:*".into(),
			"http://127.0.0.1:*".into(),
			"https://localhost:*".into(),
			"https://127.0.0.1:*".into(),
			"https://polkadot.js.org".into(),
			"https://substrate-ui.parity.io".into(),
		])
	}).into();

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

/// Creates a configuration including the database path.
pub fn create_config_with_db_path<C, G, E, S>(
	spec_factory: S, cli: &SharedParams, version: &VersionInfo,
) -> error::Result<Configuration<C, G, E>>
where
	C: Default,
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
{
	let spec = load_spec(cli, spec_factory)?;
	let base_path = base_path(cli, version);

	let mut config = service::Configuration::default_with_spec_and_base_path(spec.clone(), Some(base_path));
	config.database = DatabaseConfig::Path {
		path: config.in_chain_config_dir(DEFAULT_DB_CONFIG_PATH).expect("We provided a base_path."),
		cache_size: None,
	};

	Ok(config)
}

/// Internal trait used to cast to a dynamic type that implements Read and Seek.
trait ReadPlusSeek: Read + Seek {}

impl<T: Read + Seek> ReadPlusSeek for T {}

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

fn init_logger(pattern: &str) {
	use ansi_term::Colour;

	let mut builder = env_logger::Builder::new();
	// Disable info logging by default for some modules:
	builder.filter(Some("ws"), log::LevelFilter::Off);
	builder.filter(Some("hyper"), log::LevelFilter::Warn);
	builder.filter(Some("cranelift_wasm"), log::LevelFilter::Warn);
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

	if builder.try_init().is_err() {
		info!("Not registering Substrate logger, as there is already a global logger registered!");
	}
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
	use network::config::identity::ed25519;

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
					NodeKeyType::Ed25519 => ed25519::SecretKey::generate().as_ref().to_vec()
				};
				let params = NodeKeyParams {
					node_key_type,
					node_key: Some(format!("{:x}", H256::from_slice(sk.as_ref()))),
					node_key_file: None
				};
				node_key_config(params, &net_config_dir).and_then(|c| match c {
					NodeKeyConfig::Ed25519(network::config::Secret::Input(ref ski))
						if node_key_type == NodeKeyType::Ed25519 &&
							&sk[..] == ski.as_ref() => Ok(()),
					_ => Err(error::Error::Input("Unexpected node key config".into()))
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
					NodeKeyConfig::Ed25519(network::config::Secret::File(ref f))
						if node_key_type == NodeKeyType::Ed25519 && f == &file => Ok(()),
					_ => Err(error::Error::Input("Unexpected node key config".into()))
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
						NodeKeyConfig::Ed25519(network::config::Secret::New)
							if typ == NodeKeyType::Ed25519 => Ok(()),
						_ => Err(error::Error::Input("Unexpected node key config".into()))
					})
			})
		}

		fn some_config_dir(net_config_dir: String) -> error::Result<()> {
			with_def_params(|params| {
				let dir = PathBuf::from(net_config_dir.clone());
				let typ = params.node_key_type;
				node_key_config(params, &Some(net_config_dir.clone()))
					.and_then(move |c| match c {
						NodeKeyConfig::Ed25519(network::config::Secret::File(ref f))
							if typ == NodeKeyType::Ed25519 &&
								f == &dir.join(NODE_KEY_ED25519_FILE) => Ok(()),
						_ => Err(error::Error::Input("Unexpected node key config".into()))
				})
			})
		}

		assert!(no_config_dir().is_ok());
		assert!(some_config_dir("x".to_string()).is_ok());
	}
}
