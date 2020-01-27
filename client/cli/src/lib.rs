// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use sc_client_api::execution_extensions::ExecutionStrategies;
use sc_service::{
	config::{Configuration, DatabaseConfig, KeystoreConfig},
	ServiceBuilderCommand,
	RuntimeGenesis, ChainSpecExtension, PruningMode, ChainSpec,
};
use sc_network::{
	self,
	multiaddr::Protocol,
	config::{
		NetworkConfiguration, TransportConfig, NonReservedPeerMode, NodeKeyConfig, build_multiaddr
	},
};
use sp_core::H256;
use execution_strategy::*;

use std::{
	io::{Write, Read, Seek, Cursor, stdin, stdout, ErrorKind}, iter, fmt::Debug, fs::{self, File},
	net::{Ipv4Addr, SocketAddr}, path::{Path, PathBuf}, str::FromStr, pin::Pin, task::Poll
};

use names::{Generator, Name};
use regex::Regex;
use structopt::{StructOpt, StructOptInternal, clap::AppSettings};
#[doc(hidden)]
pub use structopt::clap::App;
use params::{
	RunCmd, PurgeChainCmd, RevertCmd, ImportBlocksCmd, ExportBlocksCmd, BuildSpecCmd,
	NetworkConfigurationParams, MergeParameters, TransactionPoolParams,
	NodeKeyParams, NodeKeyType, Cors, CheckBlockCmd,
};
pub use params::{NoCustom, CoreParams, SharedParams, ImportParams, ExecutionStrategy};
pub use traits::GetSharedParams;
use app_dirs::{AppInfo, AppDataType};
use log::info;
use lazy_static::lazy_static;
use futures::{Future, executor::block_on};
use sc_telemetry::TelemetryEndpoints;
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

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
	type Exit: Future<Output=()> + Unpin + Send + 'static;
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

/// Load spec give shared params and spec factory.
pub fn load_spec<F, G, E>(cli: &SharedParams, factory: F) -> error::Result<ChainSpec<G, E>> where
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

fn base_path(
	cli: &SharedParams,
	version: &VersionInfo,
	default_base_path: Option<PathBuf>,
) -> PathBuf {
	cli.base_path.clone()
		.or(default_base_path)
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
	CC: StructOpt + Clone + GetSharedParams,
	RP: StructOpt + Clone + StructOptInternal,
	I: IntoIterator,
	<I as IntoIterator>::Item: Into<std::ffi::OsString> + Clone,
{
	let full_version = sc_service::config::full_version_from_strs(
		version.version,
		version.commit
	);

	sp_panic_handler::set(version.support_url, &full_version);
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
	fdlimit::raise_fd_limit();

	let args = match cli_args {
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
		params::CoreParams::CheckBlock(params) => ParseAndPrepare::CheckBlock(
			CheckBlock { params, version }
		),
		params::CoreParams::PurgeChain(params) => ParseAndPrepare::PurgeChain(
			ParseAndPreparePurge { params, version }
		),
		params::CoreParams::Revert(params) => ParseAndPrepare::RevertChain(
			ParseAndPrepareRevert { params, version }
		),
		params::CoreParams::Custom(params) => ParseAndPrepare::CustomCommand(params),
	};
	init_logger(args.shared_params().and_then(|p| p.log.as_ref()).map(|v| v.as_ref()).unwrap_or(""));
	args
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
	/// Command to check a block.
	CheckBlock(CheckBlock<'a>),
	/// Command ready to purge the chain.
	PurgeChain(ParseAndPreparePurge<'a>),
	/// Command ready to revert the chain.
	RevertChain(ParseAndPrepareRevert<'a>),
	/// An additional custom command passed to `parse_and_prepare`.
	CustomCommand(CC),
}

impl<'a, CC, RP> ParseAndPrepare<'a, CC, RP> where CC: GetSharedParams {
	/// Return common set of parameters shared by all commands.
	pub fn shared_params(&self) -> Option<&SharedParams> {
		match self {
			ParseAndPrepare::Run(c) => Some(&c.params.left.shared_params),
			ParseAndPrepare::BuildSpec(c) => Some(&c.params.shared_params),
			ParseAndPrepare::ExportBlocks(c) => Some(&c.params.shared_params),
			ParseAndPrepare::ImportBlocks(c) => Some(&c.params.shared_params),
			ParseAndPrepare::CheckBlock(c) => Some(&c.params.shared_params),
			ParseAndPrepare::PurgeChain(c) => Some(&c.params.shared_params),
			ParseAndPrepare::RevertChain(c) => Some(&c.params.shared_params),
			ParseAndPrepare::CustomCommand(c) => c.shared_params(),
		}
	}
}

impl<'a, CC, RP> ParseAndPrepare<'a, CC, RP> {
	/// Convert ParseAndPrepare to Configuration
	pub fn into_configuration<C, G, E, S>(
		self,
		spec_factory: S,
		default_base_path: Option<PathBuf>,
	) -> error::Result<Option<Configuration<C, G, E>>>
	where
		C: Default,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
	{
		match self {
			ParseAndPrepare::Run(c) =>
				Some(create_run_node_config(
					c.params.left,
					spec_factory,
					c.impl_name,
					c.version,
					default_base_path,
				)).transpose(),
			ParseAndPrepare::BuildSpec(c) => {
				let spec = load_spec(&c.params.shared_params, spec_factory)?;

				Some(create_build_spec_config(
					&spec,
					&c.params.shared_params,
					c.version,
					default_base_path,
				)).transpose()
			},
			ParseAndPrepare::ExportBlocks(c) =>
				Some(create_config_with_db_path(
					spec_factory,
					&c.params.shared_params,
					c.version,
					default_base_path,
				)).transpose(),
			ParseAndPrepare::ImportBlocks(c) =>
				Some(create_config_with_db_path(
					spec_factory,
					&c.params.shared_params,
					c.version,
					default_base_path,
				)).transpose(),
			ParseAndPrepare::CheckBlock(c) =>
				Some(create_config_with_db_path(
					spec_factory,
					&c.params.shared_params,
					c.version,
					default_base_path,
				)).transpose(),
			ParseAndPrepare::PurgeChain(c) =>
				Some(create_config_with_db_path(
					spec_factory,
					&c.params.shared_params,
					c.version,
					default_base_path,
				)).transpose(),
			ParseAndPrepare::RevertChain(c) =>
				Some(create_config_with_db_path(
					spec_factory,
					&c.params.shared_params,
					c.version,
					default_base_path,
				)).transpose(),
			ParseAndPrepare::CustomCommand(_) => Ok(None),
		}
	}
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
			self.params.left.clone(),
			spec_factory,
			self.impl_name,
			self.version,
			None,
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
			let cfg = create_build_spec_config::<C, _, _>(
				&spec,
				&self.params.shared_params,
				self.version,
				None,
			)?;
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

		let json = sc_service::chain_ops::build_spec(spec, raw_output)?;

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
		B: ServiceBuilderCommand,
		<<<<B as ServiceBuilderCommand>::Block as BlockT>::Header as HeaderT>
			::Number as FromStr>::Err: Debug,
		C: Default,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		Exit: IntoExit
	{
		let mut config = create_config_with_db_path(
			spec_factory,
			&self.params.shared_params,
			self.version,
			None,
		)?;
		fill_config_keystore_in_memory(&mut config)?;

		if let DatabaseConfig::Path { ref path, .. } = &config.database {
			info!("DB path: {}", path.display());
		}
		let from = self.params.from.and_then(|f| f.parse().ok()).unwrap_or(1);
		let to = self.params.to.and_then(|t| t.parse().ok());

		let json = self.params.json;

		let file: Box<dyn Write> = match self.params.output {
			Some(filename) => Box::new(File::create(filename)?),
			None => Box::new(stdout()),
		};

		// Note: while we would like the user to handle the exit themselves, we handle it here
		// for backwards compatibility reasons.
		let (exit_send, exit_recv) = std::sync::mpsc::channel();
		let exit = exit.into_exit();
		std::thread::spawn(move || {
			block_on(exit);
			let _ = exit_send.send(());
		});

		let mut export_fut = builder(config)?
			.export_blocks(file, from.into(), to, json);
		let fut = futures::future::poll_fn(|cx| {
			if exit_recv.try_recv().is_ok() {
				return Poll::Ready(Ok(()));
			}
			Pin::new(&mut export_fut).poll(cx)
		});

		let mut runtime = tokio::runtime::Runtime::new().unwrap();
		runtime.block_on(fut)?;
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
		B: ServiceBuilderCommand,
		C: Default,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		Exit: IntoExit
	{
		let mut config = create_config_with_db_path(
			spec_factory,
			&self.params.shared_params,
			self.version,
			None,
		)?;
		fill_import_params(
			&mut config,
			&self.params.import_params,
			sc_service::Roles::FULL,
			self.params.shared_params.dev,
		)?;

		let file: Box<dyn ReadPlusSeek + Send> = match self.params.input {
			Some(filename) => Box::new(File::open(filename)?),
			None => {
				let mut buffer = Vec::new();
				stdin().read_to_end(&mut buffer)?;
				Box::new(Cursor::new(buffer))
			},
		};

		// Note: while we would like the user to handle the exit themselves, we handle it here
		// for backwards compatibility reasons.
		let (exit_send, exit_recv) = std::sync::mpsc::channel();
		let exit = exit.into_exit();
		std::thread::spawn(move || {
			block_on(exit);
			let _ = exit_send.send(());
		});

		let mut import_fut = builder(config)?
			.import_blocks(file, false);
		let fut = futures::future::poll_fn(|cx| {
			if exit_recv.try_recv().is_ok() {
				return Poll::Ready(Ok(()));
			}
			Pin::new(&mut import_fut).poll(cx)
		});

		let mut runtime = tokio::runtime::Runtime::new().unwrap();
		runtime.block_on(fut)?;
		Ok(())
	}
}

/// Command to check a block.
pub struct CheckBlock<'a> {
	params: CheckBlockCmd,
	version: &'a VersionInfo,
}

impl<'a> CheckBlock<'a> {
	/// Runs the command and imports to the chain.
	pub fn run_with_builder<C, G, E, F, B, S, Exit>(
		self,
		builder: F,
		spec_factory: S,
		_exit: Exit,
	) -> error::Result<()>
		where S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
			F: FnOnce(Configuration<C, G, E>) -> Result<B, error::Error>,
			B: ServiceBuilderCommand,
			<<B as ServiceBuilderCommand>::Block as BlockT>::Hash: FromStr,
			C: Default,
			G: RuntimeGenesis,
			E: ChainSpecExtension,
			Exit: IntoExit
	{
		let mut config = create_config_with_db_path(
			spec_factory,
			&self.params.shared_params,
			self.version,
			None,
		)?;
		fill_import_params(
			&mut config,
			&self.params.import_params,
			sc_service::Roles::FULL,
			self.params.shared_params.dev,
		)?;
		fill_config_keystore_in_memory(&mut config)?;

		let input = if self.params.input.starts_with("0x") { &self.params.input[2..] } else { &self.params.input[..] };
		let block_id = match FromStr::from_str(input) {
			Ok(hash) => BlockId::hash(hash),
			Err(_) => match self.params.input.parse::<u32>() {
				Ok(n) => BlockId::number((n as u32).into()),
				Err(_) => return Err(error::Error::Input("Invalid hash or number specified".into())),
			}
		};

		let start = std::time::Instant::now();
		let check = builder(config)?
			.check_block(block_id);
		let mut runtime = tokio::runtime::Runtime::new().unwrap();
		runtime.block_on(check)?;
		println!("Completed in {} ms.", start.elapsed().as_millis());
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
		let mut config = create_config_with_db_path::<(), _, _, _>(
			spec_factory,
			&self.params.shared_params,
			self.version,
			None,
		)?;
		fill_config_keystore_in_memory(&mut config)?;
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
		B: ServiceBuilderCommand,
		<<<<B as ServiceBuilderCommand>::Block as BlockT>::Header as HeaderT>
			::Number as FromStr>::Err: Debug,
		C: Default,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		let mut config = create_config_with_db_path(
			spec_factory,
			&self.params.shared_params,
			self.version,
			None,
		)?;
		fill_config_keystore_in_memory(&mut config)?;

		let blocks = self.params.num.parse()?;
		builder(config)?.revert_chain(blocks)?;
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
					.map(sc_network::config::Secret::File)
					.unwrap_or(sc_network::config::Secret::New)))
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

/// Parse a Ed25519 secret key from a hex string into a `sc_network::Secret`.
fn parse_ed25519_secret(hex: &String) -> error::Result<sc_network::config::Ed25519Secret> {
	H256::from_str(&hex).map_err(invalid_node_key).and_then(|bytes|
		sc_network::config::identity::ed25519::SecretKey::from_bytes(bytes)
			.map(sc_network::config::Secret::Input)
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

	config.sentry_nodes.extend(cli.sentry_nodes.into_iter());

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

#[cfg(not(target_os = "unknown"))]
fn input_keystore_password() -> Result<String, String> {
	rpassword::read_password_from_tty(Some("Keystore password: "))
		.map_err(|e| format!("{:?}", e))
}

/// Use in memory keystore config when it is not required at all.
fn fill_config_keystore_in_memory<C, G, E>(config: &mut sc_service::Configuration<C, G, E>)
	-> Result<(), String>
{
	match &mut config.keystore {
		cfg @ KeystoreConfig::None => { *cfg = KeystoreConfig::InMemory; Ok(()) },
		_ => Err("Keystore config specified when it should not be!".into()),
	}
}

/// Fill the password field of the given config instance.
fn fill_config_keystore_password_and_path<C, G, E>(
	config: &mut sc_service::Configuration<C, G, E>,
	cli: &RunCmd,
) -> Result<(), String> {
	let password = if cli.password_interactive {
		#[cfg(not(target_os = "unknown"))]
		{
			Some(input_keystore_password()?.into())
		}
		#[cfg(target_os = "unknown")]
		None
	} else if let Some(ref file) = cli.password_filename {
		Some(fs::read_to_string(file).map_err(|e| format!("{}", e))?.into())
	} else if let Some(ref password) = cli.password {
		Some(password.clone().into())
	} else {
		None
	};

	let path = cli.keystore_path.clone().or(
		config.in_chain_config_dir(DEFAULT_KEYSTORE_CONFIG_PATH)
	);

	config.keystore = KeystoreConfig::Path {
		path: path.ok_or_else(|| "No `base_path` provided to create keystore path!")?,
		password,
	};

	Ok(())
}

/// Put block import CLI params into `config` object.
pub fn fill_import_params<C, G, E>(
	config: &mut Configuration<C, G, E>,
	cli: &ImportParams,
	role: sc_service::Roles,
	is_dev: bool,
) -> error::Result<()>
	where
		C: Default,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
{
	match config.database {
		DatabaseConfig::Path { ref mut cache_size, .. } =>
			*cache_size = Some(cli.database_cache_size),
		DatabaseConfig::Custom(_) => {},
	}

	config.state_cache_size = cli.state_cache_size;

	// by default we disable pruning if the node is an authority (i.e.
	// `ArchiveAll`), otherwise we keep state for the last 256 blocks. if the
	// node is an authority and pruning is enabled explicitly, then we error
	// unless `unsafe_pruning` is set.
	config.pruning = match &cli.pruning {
		Some(ref s) if s == "archive" => PruningMode::ArchiveAll,
		None if role == sc_service::Roles::AUTHORITY => PruningMode::ArchiveAll,
		None => PruningMode::default(),
		Some(s) => {
			if role == sc_service::Roles::AUTHORITY && !cli.unsafe_pruning {
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

	let exec = &cli.execution_strategies;
	let exec_all_or = |strat: ExecutionStrategy, default: ExecutionStrategy| {
		exec.execution.unwrap_or(if strat == default && is_dev {
			ExecutionStrategy::Native
		} else {
			strat
		}).into()
	};

	config.execution_strategies = ExecutionStrategies {
		syncing: exec_all_or(exec.execution_syncing, DEFAULT_EXECUTION_SYNCING),
		importing: exec_all_or(exec.execution_import_block, DEFAULT_EXECUTION_IMPORT_BLOCK),
		block_construction:
			exec_all_or(exec.execution_block_construction, DEFAULT_EXECUTION_BLOCK_CONSTRUCTION),
		offchain_worker:
			exec_all_or(exec.execution_offchain_worker, DEFAULT_EXECUTION_OFFCHAIN_WORKER),
		other: exec_all_or(exec.execution_other, DEFAULT_EXECUTION_OTHER),
	};
	Ok(())
}

fn create_run_node_config<C, G, E, S>(
	cli: RunCmd,
	spec_factory: S,
	impl_name: &'static str,
	version: &VersionInfo,
	default_base_path: Option<PathBuf>,
) -> error::Result<Configuration<C, G, E>>
where
	C: Default,
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
{
	let mut config = create_config_with_db_path(
		spec_factory,
		&cli.shared_params,
		&version,
		default_base_path,
	)?;

	fill_config_keystore_password_and_path(&mut config, &cli)?;

	let is_dev = cli.shared_params.dev;
	let is_authority = cli.validator || cli.sentry || is_dev || cli.keyring.account.is_some();
	let role =
		if cli.light {
			sc_service::Roles::LIGHT
		} else if is_authority {
			sc_service::Roles::AUTHORITY
		} else {
			sc_service::Roles::FULL
		};

	fill_import_params(&mut config, &cli.import_params, role, is_dev)?;

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

	// set sentry mode (i.e. act as an authority but **never** actively participate)
	config.sentry_mode = cli.sentry;

	config.offchain_worker = match (cli.offchain_worker, role) {
		(params::OffchainWorkerEnabled::WhenValidating, sc_service::Roles::AUTHORITY) => true,
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

	let rpc_interface: &str = interface_str(cli.rpc_external, cli.unsafe_rpc_external, cli.validator)?;
	let ws_interface: &str = interface_str(cli.ws_external, cli.unsafe_ws_external, cli.validator)?;
	let grafana_interface: &str = if cli.grafana_external { "0.0.0.0" } else { "127.0.0.1" };

	config.rpc_http = Some(parse_address(&format!("{}:{}", rpc_interface, 9933), cli.rpc_port)?);
	config.rpc_ws = Some(parse_address(&format!("{}:{}", ws_interface, 9944), cli.ws_port)?);
	config.grafana_port = Some(
		parse_address(&format!("{}:{}", grafana_interface, 9955), cli.grafana_port)?
	);

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

	config.tracing_targets = cli.tracing_targets.into();
	config.tracing_receiver = cli.tracing_receiver.into();

	// Imply forced authoring on --dev
	config.force_authoring = cli.shared_params.dev || cli.force_authoring;

	Ok(config)
}

fn interface_str(
	is_external: bool,
	is_unsafe_external: bool,
	is_validator: bool,
) -> Result<&'static str, error::Error> {
	if is_external && is_validator {
		return Err(error::Error::Input("--rpc-external and --ws-external options shouldn't be \
		used if the node is running as a validator. Use `--unsafe-rpc-external` if you understand \
		the risks. See the options description for more information.".to_owned()));
	}

	if is_external || is_unsafe_external {
		log::warn!("It isn't safe to expose RPC publicly without a proxy server that filters \
		available set of RPC methods.");

		Ok("0.0.0.0")
	} else {
		Ok("127.0.0.1")
	}
}

/// Creates a configuration including the database path.
pub fn create_config_with_db_path<C, G, E, S>(
	spec_factory: S,
	cli: &SharedParams,
	version: &VersionInfo,
	default_base_path: Option<PathBuf>,
) -> error::Result<Configuration<C, G, E>>
where
	C: Default,
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
{
	let spec = load_spec(cli, spec_factory)?;
	let base_path = base_path(cli, version, default_base_path);

	let mut config = sc_service::Configuration::default_with_spec_and_base_path(
		spec.clone(),
		Some(base_path),
	);

	config.database = DatabaseConfig::Path {
		path: config.in_chain_config_dir(DEFAULT_DB_CONFIG_PATH).expect("We provided a base_path."),
		cache_size: None,
	};

	Ok(config)
}

/// Creates a configuration including the base path and the shared params
fn create_build_spec_config<C, G, E>(
	spec: &ChainSpec<G, E>,
	cli: &SharedParams,
	version: &VersionInfo,
	default_base_path: Option<PathBuf>,
) -> error::Result<Configuration<C, G, E>>
where
	C: Default,
	G: RuntimeGenesis,
	E: ChainSpecExtension,
{
	let base_path = base_path(&cli, version, default_base_path);
	let cfg = sc_service::Configuration::<C,_,_>::default_with_spec_and_base_path(
		spec.clone(),
		Some(base_path),
	);

	Ok(cfg)
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
	// Always log the special target `sc_tracing`, overrides global level
	builder.filter(Some("sc_tracing"), log::LevelFilter::Info);
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

		if !isatty && record.level() <= log::Level::Info && atty::is(atty::Stream::Stdout) {
			// duplicate INFO/WARN output to console
			println!("{}", output);
		}

		if !enable_color {
			output = kill_color(output.as_ref());
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
	use sc_network::config::identity::ed25519;

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
					NodeKeyConfig::Ed25519(sc_network::config::Secret::Input(ref ski))
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
				let tmp = tempfile::Builder::new().prefix("alice").tempdir()?;
				let file = tmp.path().join(format!("{}_mysecret", t)).to_path_buf();
				let params = NodeKeyParams {
					node_key_type,
					node_key: None,
					node_key_file: Some(file.clone())
				};
				node_key_config(params, &net_config_dir).and_then(|c| match c {
					NodeKeyConfig::Ed25519(sc_network::config::Secret::File(ref f))
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
						NodeKeyConfig::Ed25519(sc_network::config::Secret::New)
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
						NodeKeyConfig::Ed25519(sc_network::config::Secret::File(ref f))
							if typ == NodeKeyType::Ed25519 &&
								f == &dir.join(NODE_KEY_ED25519_FILE) => Ok(()),
						_ => Err(error::Error::Input("Unexpected node key config".into()))
				})
			})
		}

		assert!(no_config_dir().is_ok());
		assert!(some_config_dir("x".to_string()).is_ok());
	}

	#[test]
	fn keystore_path_is_generated_correctly() {
		let chain_spec = ChainSpec::from_genesis(
			"test",
			"test-id",
			|| (),
			Vec::new(),
			None,
			None,
			None,
			None,
		);

		let version_info = VersionInfo {
			name: "test",
			version: "42",
			commit: "234234",
			executable_name: "test",
			description: "cool test",
			author: "universe",
			support_url: "com",
		};

		for keystore_path in vec![None, Some("/keystore/path")] {
			let mut run_cmds = RunCmd::from_args();
			run_cmds.shared_params.base_path = Some(PathBuf::from("/test/path"));
			run_cmds.keystore_path = keystore_path.clone().map(PathBuf::from);

			let node_config = create_run_node_config::<(), _, _, _>(
				run_cmds.clone(),
				|_| Ok(Some(chain_spec.clone())),
				"test",
				&version_info,
				None,
			).unwrap();

			let expected_path = match keystore_path {
				Some(path) => PathBuf::from(path),
				None => PathBuf::from("/test/path/chains/test-id/keystore"),
			};

			assert_eq!(expected_path, node_config.keystore.path().unwrap().to_owned());
		}
	}

	#[test]
	fn parse_and_prepare_into_configuration() {
		let chain_spec = ChainSpec::from_genesis(
			"test",
			"test-id",
			|| (),
			Vec::new(),
			None,
			None,
			None,
			None,
		);
		let version = VersionInfo {
			name: "test",
			version: "42",
			commit: "234234",
			executable_name: "test",
			description: "cool test",
			author: "universe",
			support_url: "com",
		};
		let spec_factory = |_: &str| Ok(Some(chain_spec.clone()));

		let args = vec!["substrate", "--dev", "--state-cache-size=42"];
		let pnp = parse_and_prepare::<NoCustom, NoCustom, _>(&version, "test", args);
		let config = pnp.into_configuration::<(), _, _, _>(spec_factory, None).unwrap().unwrap();
		assert_eq!(config.roles, sc_service::Roles::AUTHORITY);
		assert_eq!(config.state_cache_size, 42);

		let args = vec!["substrate", "import-blocks", "--dev"];
		let pnp = parse_and_prepare::<NoCustom, NoCustom, _>(&version, "test", args);
		let config = pnp.into_configuration::<(), _, _, _>(spec_factory, None).unwrap().unwrap();
		assert_eq!(config.roles, sc_service::Roles::FULL);

		let args = vec!["substrate", "--base-path=/foo"];
		let pnp = parse_and_prepare::<NoCustom, NoCustom, _>(&version, "test", args);
		let config = pnp.into_configuration::<(), _, _, _>(spec_factory, Some("/bar".into())).unwrap().unwrap();
		assert_eq!(config.config_dir, Some("/foo".into()));
	}
}
