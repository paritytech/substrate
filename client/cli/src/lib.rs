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
	AbstractService, Roles as ServiceRoles,
};
use sc_network::{
	self,
	multiaddr::Protocol,
	config::{
		NetworkConfiguration, TransportConfig, NonReservedPeerMode, NodeKeyConfig, build_multiaddr
	},
};
use sp_core::H256;

use std::{
	io::{Write, Read, Seek, Cursor, stdin, stdout, ErrorKind}, iter, fmt::Debug, fs::{self, File},
	net::{Ipv4Addr, SocketAddr}, path::{Path, PathBuf}, str::FromStr, pin::Pin, task::Poll
};

use names::{Generator, Name};
use regex::Regex;
use structopt::{StructOpt, clap::AppSettings};
#[doc(hidden)]
pub use structopt::clap::App;
use params::{
	RunCmd, PurgeChainCmd, RevertCmd, ImportBlocksCmd, ExportBlocksCmd, BuildSpecCmd,
	NetworkConfigurationParams, TransactionPoolParams,
	NodeKeyParams, NodeKeyType, Cors, CheckBlockCmd,
};
pub use params::{NoCustom, CoreParams, SharedParams, ImportParams, ExecutionStrategy};
pub use traits::GetSharedParams;
use app_dirs::{AppInfo, AppDataType};
use log::info;
use lazy_static::lazy_static;
use futures::{Future, compat::Future01CompatExt, executor::block_on, future, future::FutureExt};
use sc_telemetry::TelemetryEndpoints;
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use futures::select;
use futures::pin_mut;

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

pub fn run<F, G, E, F2, F3, F4, T1, T2, T3, T5>(
	core_params: CoreParams,
	new_light: F2,
	new_full: F3,
	spec_factory: F,
	builder: F4,
	impl_name: &'static str,
	version: &VersionInfo,
) -> error::Result<()>
where
	F: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
	F2: FnOnce(Configuration<G, E>) -> Result<T1, sc_service::error::Error>,
	F3: FnOnce(Configuration<G, E>) -> Result<T2, sc_service::error::Error>,
	F4: FnOnce(Configuration<G, E>) -> Result<T3, sc_service::error::Error>,
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	T1: AbstractService + std::marker::Unpin,
	T2: AbstractService + std::marker::Unpin,
	T3: ServiceBuilderCommand<Block = T5> + std::marker::Unpin,
	T5: sp_runtime::traits::Block + Debug,
	<<<T5 as sp_runtime::traits::Block>::Header as sp_runtime::traits::Header>::Number as
	std::str::FromStr>::Err: std::fmt::Debug,
{
	let full_version = sc_service::config::full_version_from_strs(
		version.version,
		version.commit
	);

	sp_panic_handler::set(version.support_url, &full_version);
	/*
	let matches = CoreParams::clap()
		.name(version.executable_name)
		.author(version.author)
		.about(version.description)
		.version(&(full_version + "\n")[..])
		.setting(AppSettings::GlobalVersion)
		.setting(AppSettings::ArgsNegateSubcommands)
		.setting(AppSettings::SubcommandsNegateReqs)
		.get_matches_from(args);
	*/
	//let cli_args = CoreParams::from_clap(&matches);
	fdlimit::raise_fd_limit();
	init_logger(core_params.get_shared_params().log.as_ref().map(|v| v.as_ref()).unwrap_or(""));

	match &core_params {
		CoreParams::Run(_params) => {
			let config = get_config(&core_params, spec_factory, impl_name, &version)?;

			info!("{}", version.name);
			info!("  version {}", config.full_version());
			info!("  by {}, 2017, 2018", version.author);
			info!("Chain specification: {}", config.chain_spec.name());
			info!("Node name: {}", config.name);
			info!("Roles: {}", display_role(&config));
			match config.roles {
				ServiceRoles::LIGHT => run_service_until_exit(
					new_light(config)?,
				),
				_ => run_service_until_exit(
					new_full(config)?,
				),
			}
		},
		CoreParams::BuildSpec(params) => {
			info!("Building chain spec");
			let raw_output = params.raw;
			let mut spec = load_spec(&params.shared_params, spec_factory)?;

			if spec.boot_nodes().is_empty() && !params.disable_default_bootnode {
				let cfg = create_build_spec_config(
					&spec,
					&params.shared_params,
					version,
				)?;
				let node_key = node_key_config(
					params.node_key_params.clone(),
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
		},
		CoreParams::ExportBlocks(params) => {
			let config = get_config(&core_params, spec_factory, impl_name, &version)?;

			if let DatabaseConfig::Path { ref path, .. } = &config.database {
				info!("DB path: {}", path.display());
			}
			let from = params.from.as_ref().and_then(|f| f.parse().ok()).unwrap_or(1);
			let to = params.to.as_ref().and_then(|t| t.parse().ok());

			let json = params.json;

			let file: Box<dyn Write> = match &params.output {
				Some(filename) => Box::new(File::create(filename)?),
				None => Box::new(stdout()),
			};

			let f = builder(config)?
				.export_blocks(file, from.into(), to, json)
				.compat();
			let f = f.fuse();
			pin_mut!(f);

			run_until_exit(f)
		},
		CoreParams::ImportBlocks(params) => {
			let mut config = get_config(&core_params, spec_factory, impl_name, &version)?;
			fill_import_params(&mut config, &params.import_params, sc_service::Roles::FULL)?;

			let file: Box<dyn ReadPlusSeek + Send> = match &params.input {
				Some(filename) => Box::new(File::open(filename)?),
				None => {
					let mut buffer = Vec::new();
					stdin().read_to_end(&mut buffer)?;
					Box::new(Cursor::new(buffer))
				},
			};

			let f = builder(config)?
				.import_blocks(file, false)
				.compat();
			let f = f.fuse();
			pin_mut!(f);

			run_until_exit(f)
		},
		/*
		CoreParams::CheckBlock(params) =>
		CoreParams::PurgeChain(params) =>
		CoreParams::Revert(params) =>
		*/
		/*
		ParseAndPrepare::ExportBlocks(cmd) => cmd.run_with_builder(|config: Configuration<_, G, E>|
			Ok(new_full_start!(config).0), load_spec, exit),
		ParseAndPrepare::ImportBlocks(cmd) => cmd.run_with_builder(|config: Configuration<_, G, E>|
			Ok(new_full_start!(config).0), load_spec, exit),
		ParseAndPrepare::CheckBlock(cmd) => cmd.run_with_builder(|config: Configuration<_, G, E>|
			Ok(new_full_start!(config).0), load_spec, exit),
		ParseAndPrepare::PurgeChain(cmd) => cmd.run(load_spec),
		ParseAndPrepare::RevertChain(cmd) => cmd.run_with_builder(|config: Configuration<_, G, E>|
			Ok(new_full_start!(config).0), load_spec),
		*/
		_ => todo!(),
	};

	Ok(())
}

struct Runtime<F, E: 'static>(F)
where
	F: Future<Output = Result<(), E>> + future::FusedFuture + Unpin,
	E: std::error::Error;

impl<F, E: 'static> Runtime<F, E>
where
    F: Future<Output = Result<(), E>> + future::FusedFuture + Unpin,
	E: std::error::Error,
{
    #[tokio::main]
    async fn run(self) -> Result<(), Box<dyn std::error::Error>>
    {
		use tokio::signal::unix::{signal, SignalKind};

        let mut stream_int = signal(SignalKind::interrupt())?;
        let mut stream_term = signal(SignalKind::terminate())?;

        let t1 = stream_int.recv().fuse();
        let t2 = stream_term.recv().fuse();
        let mut t3 = self.0;

        pin_mut!(t1, t2);

        select! {
            _ = t1 => println!("Caught SIGINT"),
            _ = t2 => println!("Caught SIGTERM"),
            res = t3 => res?,
        }

        Ok(())
    }
}

fn run_service_until_exit<T>(
	service: T,
) -> error::Result<()>
where
	T: AbstractService + std::marker::Unpin,
{
	let runtime = Runtime(service.compat().fuse());
	runtime.run().map_err(|e| e.to_string())?;

	Ok(())
}

fn run_until_exit<F, E: 'static>(
	future: F,
) -> error::Result<()>
where
	F: Future<Output = Result<(), E>> + future::FusedFuture + Unpin,
	E: std::error::Error
{
	let runtime = Runtime(future);
	runtime.run().map_err(|e| e.to_string())?;

	Ok(())
}

/*
	//use futures::Stream;
	use futures::{TryFutureExt, future::select};

	let (exit_send, exit) = oneshot::channel();

	let informant = informant::build(&service);

	let future = select(exit, informant)
		.map(|_| Ok(()))
		.compat();

	runtime.spawn(future);

	// we eagerly drop the service so that the internal exit future is fired,
	// but we need to keep holding a reference to the global telemetry guard
	let _telemetry = service.telemetry();

	let service_res = {
		let exit = e.into_exit();
		let service = service
			.map_err(|err| error::Error::Service(err))
			.compat();
		let select = select(service, exit)
			.map(|_| Ok(()));
			//.compat();
		runtime.block_on(select)
	};

	let _ = exit_send.send(());

	// TODO [andre]: timeout this future #1318

	//use futures01::Future;

	//let _ = runtime.shutdown_on_idle().wait();

	service_res
}
*/

/// Returns a string displaying the node role, special casing the sentry mode
/// (returning `SENTRY`), since the node technically has an `AUTHORITY` role but
/// doesn't participate.
pub fn display_role<G, E>(config: &Configuration<G, E>) -> String {
	if config.sentry_mode {
		"SENTRY".to_string()
	} else {
		format!("{:?}", config.roles)
	}
}

/// Output of calling `parse_and_prepare`.
#[must_use]
pub enum ParseAndPrepare<'a> {
	/// Command ready to run the main client.
	Run(ParseAndPrepareRun<'a>),
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
}

impl<'a> ParseAndPrepare<'a> {
	/// Return common set of parameters shared by all commands.
	pub fn shared_params(&self) -> Option<&SharedParams> {
		match self {
			ParseAndPrepare::Run(c) => Some(&c.params.shared_params),
			ParseAndPrepare::BuildSpec(c) => Some(&c.params.shared_params),
			ParseAndPrepare::ExportBlocks(c) => Some(&c.params.shared_params),
			ParseAndPrepare::ImportBlocks(c) => Some(&c.params.shared_params),
			ParseAndPrepare::CheckBlock(c) => Some(&c.params.shared_params),
			ParseAndPrepare::PurgeChain(c) => Some(&c.params.shared_params),
			ParseAndPrepare::RevertChain(c) => Some(&c.params.shared_params),
		}
	}
}

pub fn get_config<G, E, F>(
	core_params: &CoreParams,
	spec_factory: F,
	impl_name: &'static str,
	version: &VersionInfo,
) -> error::Result<Configuration<G, E>>
where
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	F: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
{
	match core_params {
		CoreParams::Run(params) =>
			create_run_node_config(
				params.clone(),
				spec_factory,
				impl_name,
				version
			),
		CoreParams::BuildSpec(params) => {
			let spec = load_spec(&params.shared_params, spec_factory)?;

			create_build_spec_config(
				&spec,
				&params.shared_params,
				version,
			)
		},
		CoreParams::ExportBlocks(params) =>
			create_config_with_db_path(
				spec_factory,
				&params.shared_params,
				version,
			),
		CoreParams::ImportBlocks(params) =>
			create_config_with_db_path(
				spec_factory,
				&params.shared_params,
				version,
			),
		CoreParams::CheckBlock(params) =>
			create_config_with_db_path(
				spec_factory,
				&params.shared_params,
				version,
			),
		CoreParams::PurgeChain(params) =>
			create_config_with_db_path(
				spec_factory,
				&params.shared_params,
				version
			),
		CoreParams::Revert(params) =>
			create_config_with_db_path(
				spec_factory,
				&params.shared_params,
				version,
			),
	}
}

/// Command ready to run the main client.
pub struct ParseAndPrepareRun<'a> {
	params: RunCmd,
	impl_name: &'static str,
	version: &'a VersionInfo,
}

/// Command ready to build chain specs.
pub struct ParseAndPrepareBuildSpec<'a> {
	params: BuildSpecCmd,
	version: &'a VersionInfo,
}

/// Command ready to export the chain.
pub struct ParseAndPrepareExport<'a> {
	params: ExportBlocksCmd,
	version: &'a VersionInfo,
}

/// Command ready to import the chain.
pub struct ParseAndPrepareImport<'a> {
	params: ImportBlocksCmd,
	version: &'a VersionInfo,
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
			F: FnOnce(Configuration<G, E>) -> Result<B, error::Error>,
			B: ServiceBuilderCommand,
			<<B as ServiceBuilderCommand>::Block as BlockT>::Hash: FromStr,
			C: Default,
			G: RuntimeGenesis,
			E: ChainSpecExtension,
			Exit: IntoExit
	{
		let mut config = create_config_with_db_path(spec_factory, &self.params.shared_params, self.version)?;
		fill_import_params(&mut config, &self.params.import_params, sc_service::Roles::FULL)?;

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
			.check_block(block_id)
			.compat();
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
		let config = create_config_with_db_path(
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
		F: FnOnce(Configuration<G, E>) -> Result<B, error::Error>,
		B: ServiceBuilderCommand,
		<<<<B as ServiceBuilderCommand>::Block as BlockT>::Header as HeaderT>
			::Number as FromStr>::Err: Debug,
		C: Default,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		let config = create_config_with_db_path(
			spec_factory, &self.params.shared_params, self.version
		)?;
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
fn fill_transaction_pool_configuration<G, E>(
	options: &mut Configuration<G, E>,
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

/// Fill the password field of the given config instance.
fn fill_config_keystore_password_and_path<G, E>(
	config: &mut sc_service::Configuration<G, E>,
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
pub fn fill_import_params<G, E>(
	config: &mut Configuration<G, E>,
	cli: &ImportParams,
	role: sc_service::Roles,
) -> error::Result<()>
	where
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
	let exec_all_or = |strat: ExecutionStrategy| exec.execution.unwrap_or(strat).into();
	config.execution_strategies = ExecutionStrategies {
		syncing: exec_all_or(exec.execution_syncing),
		importing: exec_all_or(exec.execution_import_block),
		block_construction: exec_all_or(exec.execution_block_construction),
		offchain_worker: exec_all_or(exec.execution_offchain_worker),
		other: exec_all_or(exec.execution_other),
	};
	Ok(())
}

fn create_run_node_config<G, E, S>(
	cli: RunCmd, spec_factory: S, impl_name: &'static str, version: &VersionInfo,
) -> error::Result<Configuration<G, E>>
where
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
{
	let mut config = create_config_with_db_path(spec_factory, &cli.shared_params, &version)?;

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

	fill_import_params(&mut config, &cli.import_params, role)?;

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
pub fn create_config_with_db_path<G, E, S>(
	spec_factory: S, cli: &SharedParams, version: &VersionInfo,
) -> error::Result<Configuration<G, E>>
where
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	S: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
{
	let spec = load_spec(cli, spec_factory)?;
	let base_path = base_path(cli, version);

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
fn create_build_spec_config<G, E>(
	spec: &ChainSpec<G, E>,
	cli: &SharedParams,
	version: &VersionInfo,
) -> error::Result<Configuration<G, E>>
where
	G: RuntimeGenesis,
	E: ChainSpecExtension,
{
	let base_path = base_path(&cli, version);
	let cfg = sc_service::Configuration::default_with_spec_and_base_path(
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

		let args = vec!["substrate", "run", "--dev", "--state-cache-size=42"];
		let pnp = parse_and_prepare(&version, "test", args);
		let config = pnp.into_configuration::<(), _, _, _>(spec_factory).unwrap().unwrap();
		assert_eq!(config.roles, sc_service::Roles::AUTHORITY);
		assert_eq!(config.state_cache_size, 42);

		let args = vec!["substrate", "import-blocks", "--dev"];
		let pnp = parse_and_prepare(&version, "test", args);
		let config = pnp.into_configuration::<(), _, _, _>(spec_factory).unwrap().unwrap();
		assert_eq!(config.roles, sc_service::Roles::FULL);
	}
}
