// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use std::path::PathBuf;
use std::net::SocketAddr;
use std::fs;
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use log::info;
use structopt::{StructOpt, clap::arg_enum};
use regex::Regex;
use chrono::prelude::*;
use sc_service::{
	AbstractService, Configuration, ChainSpecExtension, RuntimeGenesis, ChainSpec, Roles,
	config::{DatabaseConfig, KeystoreConfig, NetworkConfiguration},
};
use sc_telemetry::TelemetryEndpoints;

use crate::{SubstrateCLI, CliConfiguration};
use crate::error;
use crate::params::ImportParams;
use crate::params::SharedParams;
use crate::params::NetworkConfigurationParams;
use crate::params::TransactionPoolParams;
use crate::params::KeystoreParams;
use crate::runtime::run_service_until_exit;

arg_enum! {
	/// Whether off-chain workers are enabled.
	#[allow(missing_docs)]
	#[derive(Debug, Clone)]
	pub enum OffchainWorkerEnabled {
		Always,
		Never,
		WhenValidating,
	}
}

/// The `run` command used to run a node.
#[derive(Debug, StructOpt, Clone)]
pub struct RunCmd {
	/// Enable validator mode.
	///
	/// The node will be started with the authority role and actively
	/// participate in any consensus task that it can (e.g. depending on
	/// availability of local keys).
	#[structopt(
		long = "validator",
		conflicts_with_all = &[ "sentry" ]
	)]
	pub validator: bool,

	/// Enable sentry mode.
	///
	/// The node will be started with the authority role and participate in
	/// consensus tasks as an "observer", it will never actively participate
	/// regardless of whether it could (e.g. keys are available locally). This
	/// mode is useful as a secure proxy for validators (which would run
	/// detached from the network), since we want this node to participate in
	/// the full consensus protocols in order to have all needed consensus data
	/// available to relay to private nodes.
	#[structopt(
		long = "sentry",
		conflicts_with_all = &[ "validator", "light" ]
	)]
	pub sentry: bool,

	/// Disable GRANDPA voter when running in validator mode, otherwise disables the GRANDPA observer.
	#[structopt(long = "no-grandpa")]
	pub no_grandpa: bool,

	/// Experimental: Run in light client mode.
	#[structopt(long = "light", conflicts_with = "sentry")]
	pub light: bool,

	/// Listen to all RPC interfaces.
	///
	/// Default is local. Note: not all RPC methods are safe to be exposed publicly. Use a RPC proxy
	/// server to filter out dangerous methods. More details: https://github.com/paritytech/substrate/wiki/Public-RPC.
	/// Use `--unsafe-rpc-external` to suppress the warning if you understand the risks.
	#[structopt(long = "rpc-external")]
	pub rpc_external: bool,

	/// Listen to all RPC interfaces.
	///
	/// Same as `--rpc-external`.
	#[structopt(long = "unsafe-rpc-external")]
	pub unsafe_rpc_external: bool,

	/// Listen to all Websocket interfaces.
	///
	/// Default is local. Note: not all RPC methods are safe to be exposed publicly. Use a RPC proxy
	/// server to filter out dangerous methods. More details: https://github.com/paritytech/substrate/wiki/Public-RPC.
	/// Use `--unsafe-ws-external` to suppress the warning if you understand the risks.
	#[structopt(long = "ws-external")]
	pub ws_external: bool,

	/// Listen to all Websocket interfaces.
	///
	/// Same as `--ws-external` but doesn't warn you about it.
	#[structopt(long = "unsafe-ws-external")]
	pub unsafe_ws_external: bool,

	/// Listen to all Prometheus data source interfaces.
	///
	/// Default is local.
	#[structopt(long = "prometheus-external")]
	pub prometheus_external: bool,

	/// Specify HTTP RPC server TCP port.
	#[structopt(long = "rpc-port", value_name = "PORT")]
	pub rpc_port: Option<u16>,

	/// Specify WebSockets RPC server TCP port.
	#[structopt(long = "ws-port", value_name = "PORT")]
	pub ws_port: Option<u16>,

	/// Maximum number of WS RPC server connections.
	#[structopt(long = "ws-max-connections", value_name = "COUNT")]
	pub ws_max_connections: Option<usize>,

	/// Specify browser Origins allowed to access the HTTP & WS RPC servers.
	///
	/// A comma-separated list of origins (protocol://domain or special `null`
	/// value). Value of `all` will disable origin validation. Default is to
	/// allow localhost, https://polkadot.js.org and
	/// https://substrate-ui.parity.io origins. When running in --dev mode the
	/// default is to allow all origins.
	#[structopt(long = "rpc-cors", value_name = "ORIGINS", parse(try_from_str = parse_cors))]
	pub rpc_cors: Option<Cors>,

	/// Specify Prometheus data source server TCP Port.
	#[structopt(long = "prometheus-port", value_name = "PORT")]
	pub prometheus_port: Option<u16>,

	/// Do not expose a Prometheus metric endpoint.
	///
	/// Prometheus metric endpoint is enabled by default.
	#[structopt(long = "no-prometheus")]
	pub no_prometheus: bool,

	/// The human-readable name for this node.
	///
	/// The node name will be reported to the telemetry server, if enabled.
	#[structopt(long = "name", value_name = "NAME")]
	pub name: Option<String>,

	/// Disable connecting to the Substrate telemetry server.
	///
	/// Telemetry is on by default on global chains.
	#[structopt(long = "no-telemetry")]
	pub no_telemetry: bool,

	/// The URL of the telemetry server to connect to.
	///
	/// This flag can be passed multiple times as a mean to specify multiple
	/// telemetry endpoints. Verbosity levels range from 0-9, with 0 denoting
	/// the least verbosity. If no verbosity level is specified the default is
	/// 0.
	#[structopt(long = "telemetry-url", value_name = "URL VERBOSITY", parse(try_from_str = parse_telemetry_endpoints))]
	pub telemetry_endpoints: Vec<(String, u8)>,

	/// Should execute offchain workers on every block.
	///
	/// By default it's only enabled for nodes that are authoring new blocks.
	#[structopt(
		long = "offchain-worker",
		value_name = "ENABLED",
		possible_values = &OffchainWorkerEnabled::variants(),
		case_insensitive = true,
		default_value = "WhenValidating"
	)]
	pub offchain_worker: OffchainWorkerEnabled,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub import_params: ImportParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub network_config: NetworkConfigurationParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pool_config: TransactionPoolParams,

	/// Shortcut for `--name Alice --validator` with session keys for `Alice` added to keystore.
	#[structopt(long, conflicts_with_all = &["bob", "charlie", "dave", "eve", "ferdie", "one", "two"])]
	pub alice: bool,

	/// Shortcut for `--name Bob --validator` with session keys for `Bob` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "charlie", "dave", "eve", "ferdie", "one", "two"])]
	pub bob: bool,

	/// Shortcut for `--name Charlie --validator` with session keys for `Charlie` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "bob", "dave", "eve", "ferdie", "one", "two"])]
	pub charlie: bool,

	/// Shortcut for `--name Dave --validator` with session keys for `Dave` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "bob", "charlie", "eve", "ferdie", "one", "two"])]
	pub dave: bool,

	/// Shortcut for `--name Eve --validator` with session keys for `Eve` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "bob", "charlie", "dave", "ferdie", "one", "two"])]
	pub eve: bool,

	/// Shortcut for `--name Ferdie --validator` with session keys for `Ferdie` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "bob", "charlie", "dave", "eve", "one", "two"])]
	pub ferdie: bool,

	/// Shortcut for `--name One --validator` with session keys for `One` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "bob", "charlie", "dave", "eve", "ferdie", "two"])]
	pub one: bool,

	/// Shortcut for `--name Two --validator` with session keys for `Two` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "bob", "charlie", "dave", "eve", "ferdie", "one"])]
	pub two: bool,

	/// Enable authoring even when offline.
	#[structopt(long = "force-authoring")]
	pub force_authoring: bool,

	#[structopt(flatten)]
	pub keystore_params: KeystoreParams,
}

impl RunCmd {
	/// Get the `Sr25519Keyring` matching one of the flag
	pub fn get_keyring(&self) -> Option<sp_keyring::Sr25519Keyring> {
		use sp_keyring::Sr25519Keyring::*;

		if self.alice { Some(Alice) }
		else if self.bob { Some(Bob) }
		else if self.charlie { Some(Charlie) }
		else if self.dave { Some(Dave) }
		else if self.eve { Some(Eve) }
		else if self.ferdie { Some(Ferdie) }
		else if self.one { Some(One) }
		else if self.two { Some(Two) }
		else { None }
	}

	/// Update and prepare a `Configuration` with command line parameters of `RunCmd` and `VersionInfo`
	pub fn update_config<C: SubstrateCLI<G, E>, G, E>(
		&self,
		mut config: &mut Configuration<G, E>,
	) -> error::Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		let keyring = self.get_keyring();
		let is_dev = self.shared_params.dev;
		let is_light = self.light;
		let is_authority = (self.validator || self.sentry || is_dev || keyring.is_some())
			&& !is_light;
		let role =
			if is_light {
				sc_service::Roles::LIGHT
			} else if is_authority {
				sc_service::Roles::AUTHORITY
			} else {
				sc_service::Roles::FULL
			};

		self.import_params.update_config(&mut config, role, is_dev)?;

		// set sentry mode (i.e. act as an authority but **never** actively participate)
		config.sentry_mode = self.sentry;

		config.offchain_worker = match (&self.offchain_worker, role) {
			(OffchainWorkerEnabled::WhenValidating, sc_service::Roles::AUTHORITY) => true,
			(OffchainWorkerEnabled::Always, _) => true,
			(OffchainWorkerEnabled::Never, _) => false,
			(OffchainWorkerEnabled::WhenValidating, _) => false,
		};

		config.roles = role;
		config.disable_grandpa = self.no_grandpa;

		self.pool_config.update_config(&mut config)?;

		if config.rpc_http.is_none() || self.rpc_port.is_some() {
			let rpc_interface: &str = interface_str(self.rpc_external, self.unsafe_rpc_external, self.validator)?;
			config.rpc_http = Some(parse_address(&format!("{}:{}", rpc_interface, 9933), self.rpc_port)?);
		}
		if config.rpc_ws.is_none() || self.ws_port.is_some() {
			let ws_interface: &str = interface_str(self.ws_external, self.unsafe_ws_external, self.validator)?;
			config.rpc_ws = Some(parse_address(&format!("{}:{}", ws_interface, 9944), self.ws_port)?);
		}

		config.rpc_ws_max_connections = self.ws_max_connections;
		config.rpc_cors = self.rpc_cors.clone().unwrap_or_else(|| if is_dev {
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
		if self.no_telemetry {
			config.telemetry_endpoints = None;
		} else if !self.telemetry_endpoints.is_empty() {
			config.telemetry_endpoints = Some(
				TelemetryEndpoints::new(self.telemetry_endpoints.clone())
			);
		}

		// Override prometheus
		if self.no_prometheus {
			config.prometheus_port = None;
		} else if config.prometheus_port.is_none() {
			let prometheus_interface: &str = if self.prometheus_external { "0.0.0.0" } else { "127.0.0.1" };
			config.prometheus_port = Some(
			parse_address(&format!("{}:{}", prometheus_interface, 9615), self.prometheus_port)?);
		}

		config.tracing_targets = self.import_params.tracing_targets.clone().into();
		config.tracing_receiver = self.import_params.tracing_receiver.clone().into();

		// Imply forced authoring on --dev
		config.force_authoring = self.shared_params.dev || self.force_authoring;

		Ok(())
	}

	/// Run the command that runs the node
	pub fn run<C: SubstrateCLI<G, E>, G, E, FNL, FNF, SL, SF>(
		config: Configuration<G, E>,
		new_light: FNL,
		new_full: FNF,
	) -> error::Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		FNL: FnOnce(Configuration<G, E>) -> Result<SL, sc_service::error::Error>,
		FNF: FnOnce(Configuration<G, E>) -> Result<SF, sc_service::error::Error>,
		SL: AbstractService + Unpin,
		SF: AbstractService + Unpin,
	{
		info!("{}", C::get_impl_name());
		info!("  version {}", C::get_impl_version());
		//info!("  by {}, {}-{}", version.author, version.copyright_start_year, Local::today().year());
		info!("Chain specification: {}", config.chain_spec.name());
		info!("Node name: {}", config.name);
		info!("Roles: {}", config.display_role());

		match config.roles {
			Roles::LIGHT => run_service_until_exit(
				config,
				new_light,
			),
			_ => run_service_until_exit(
				config,
				new_full,
			),
		}
	}
}

impl CliConfiguration for RunCmd
{
	fn get_base_path(&self) -> Option<&PathBuf> {
		self.shared_params.base_path.as_ref()
	}
	fn get_is_dev(&self) -> bool {
		self.shared_params.dev
	}
	fn get_chain_spec<C: SubstrateCLI<G, E>, G, E>(&self) -> error::Result<ChainSpec<G, E>>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		self.shared_params.get_chain_spec::<C, G, E>()
	}
	fn get_network_config<G, E>(&self, chain_spec: &ChainSpec<G, E>, is_dev: bool, base_path: &PathBuf, client_id: &str) -> error::Result<NetworkConfiguration>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		self.network_config.get_network_config(chain_spec, client_id, is_dev, base_path)
	}
	fn get_keystore_config(&self, base_path: &PathBuf) -> error::Result<KeystoreConfig> {
		self.keystore_params.get_keystore_config(base_path)
	}
	fn get_database_config(&self, base_path: &PathBuf) -> DatabaseConfig { self.shared_params.get_database_config(base_path) }
	fn get_name(&self) -> error::Result<String> {
		let name: String = match (self.name.as_ref(), self.get_keyring()) {
			(Some(name), _) => name.to_string(),
			(_, Some(keyring)) => keyring.to_string(),
			(None, None) => crate::generate_node_name(),
		};

		if let Err(msg) = is_node_name_valid(&name) {
			return Err(error::Error::Input(
				format!("Invalid node name '{}'. Reason: {}. If unsure, use none.", name, msg)
			));
		}

		Ok(name)
	}
	fn get_dev_key_seed(&self, is_dev: bool) -> Option<String> {
		self.get_keyring()
			.map(|a| format!("//{}", a)).or_else(|| {
				if is_dev && !self.light {
					Some("//Alice".into())
				} else {
					None
				}
			})
	}
	fn init<C: SubstrateCLI<G, E>, G, E>(&self) -> error::Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{ self.shared_params.init::<C, G, E>() }
}

/// Check whether a node name is considered as valid
pub fn is_node_name_valid(_name: &str) -> Result<(), &str> {
	let name = _name.to_string();
	if name.chars().count() >= crate::NODE_NAME_MAX_LENGTH {
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

/// Default to verbosity level 0, if none is provided.
fn parse_telemetry_endpoints(s: &str) -> Result<(String, u8), Box<dyn std::error::Error>> {
	let pos = s.find(' ');
	match pos {
		None => {
			Ok((s.to_owned(), 0))
		},
		Some(pos_) => {
			let verbosity = s[pos_ + 1..].parse()?;
			let url = s[..pos_].parse()?;
			Ok((url, verbosity))
		}
	}
}

/// CORS setting
///
/// The type is introduced to overcome `Option<Option<T>>`
/// handling of `structopt`.
#[derive(Clone, Debug)]
pub enum Cors {
	/// All hosts allowed
	All,
	/// Only hosts on the list are allowed.
	List(Vec<String>),
}

impl From<Cors> for Option<Vec<String>> {
	fn from(cors: Cors) -> Self {
		match cors {
			Cors::All => None,
			Cors::List(list) => Some(list),
		}
	}
}

/// Parse cors origins
fn parse_cors(s: &str) -> Result<Cors, Box<dyn std::error::Error>> {
	let mut is_all = false;
	let mut origins = Vec::new();
	for part in s.split(',') {
		match part {
			"all" | "*" => {
				is_all = true;
				break;
			},
			other => origins.push(other.to_owned()),
		}
	}

	Ok(if is_all { Cors::All } else { Cors::List(origins) })
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_service::config::DatabaseConfig;

	const TEST_VERSION_INFO: &'static VersionInfo = &VersionInfo {
		name: "node-test",
		version: "0.1.0",
		commit: "some_commit",
		executable_name: "node-test",
		description: "description",
		author: "author",
		support_url: "http://example.org",
		copyright_start_year: 2020,
	};

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
	fn keystore_path_is_generated_correctly() {
		let chain_spec = ChainSpec::from_genesis(
			"test",
			"test-id",
			|| (),
			Vec::new(),
			None,
			None,
			None,
			None::<()>,
		);

		for keystore_path in vec![None, Some("/keystore/path")] {
			let args: Vec<&str> = vec![];
			let mut cli = RunCmd::from_iter(args);
			cli.keystore_path = keystore_path.clone().map(PathBuf::from);

			let mut config = Configuration::default();
			config.config_dir = Some(PathBuf::from("/test/path"));
			config.chain_spec = Some(chain_spec.clone());
			let chain_spec = chain_spec.clone();
			cli.update_config(&mut config, move |_| Ok(Some(chain_spec)), TEST_VERSION_INFO).unwrap();

			let expected_path = match keystore_path {
				Some(path) => PathBuf::from(path),
				None => PathBuf::from("/test/path/chains/test-id/keystore"),
			};

			assert_eq!(expected_path, config.keystore.path().unwrap().to_owned());
		}
	}

	#[test]
	fn ensure_load_spec_provide_defaults() {
		let chain_spec = ChainSpec::from_genesis(
			"test",
			"test-id",
			|| (),
			vec!["boo".to_string()],
			Some(TelemetryEndpoints::new(vec![("foo".to_string(), 42)])),
			None,
			None,
			None::<()>,
		);

		let args: Vec<&str> = vec![];
		let cli = RunCmd::from_iter(args);

		let mut config = Configuration::from_version(TEST_VERSION_INFO);
		cli.update_config(&mut config, |_| Ok(Some(chain_spec)), TEST_VERSION_INFO).unwrap();

		assert!(config.chain_spec.is_some());
		assert!(!config.network.boot_nodes.is_empty());
		assert!(config.telemetry_endpoints.is_some());
	}

	#[test]
	fn ensure_update_config_for_running_node_provides_defaults() {
		let chain_spec = ChainSpec::from_genesis(
			"test",
			"test-id",
			|| (),
			vec![],
			None,
			None,
			None,
			None::<()>,
		);

		let args: Vec<&str> = vec![];
		let cli = RunCmd::from_iter(args);

		let mut config = Configuration::from_version(TEST_VERSION_INFO);
		cli.init(&TEST_VERSION_INFO).unwrap();
		cli.update_config(&mut config, |_| Ok(Some(chain_spec)), TEST_VERSION_INFO).unwrap();

		assert!(config.config_dir.is_some());
		assert!(config.database.is_some());
		if let Some(DatabaseConfig::Path { ref cache_size, .. }) = config.database {
			assert!(cache_size.is_some());
		} else {
			panic!("invalid config.database variant");
		}
		assert!(!config.name.is_empty());
		assert!(config.network.config_path.is_some());
		assert!(!config.network.listen_addresses.is_empty());
	}
}
