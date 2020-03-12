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

//! Service configuration.

pub use sc_client::ExecutionStrategies;
pub use sc_client_db::{kvdb::KeyValueDB, PruningMode};
pub use sc_network::config::{ExtTransport, NetworkConfiguration, Roles};
pub use sc_executor::WasmExecutionMethod;

use std::{future::Future, path::{PathBuf, Path}, pin::Pin, net::SocketAddr, sync::Arc};
pub use sc_transaction_pool::txpool::Options as TransactionPoolOptions;
use sc_chain_spec::ChainSpec;
use sp_core::crypto::Protected;
use target_info::Target;
use sc_telemetry::TelemetryEndpoints;
use prometheus_endpoint::Registry;

/// Executable version. Used to pass version information from the root crate.
#[derive(Clone)]
pub struct VersionInfo {
	/// Implementation name.
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
	/// Copyright starting year (x-current year)
	pub copyright_start_year: i32,
}

/// Service configuration.
pub struct Configuration {
	/// Implementation name
	pub impl_name: &'static str,
	/// Implementation version
	pub impl_version: &'static str,
	/// Git commit if any.
	pub impl_commit: &'static str,
	/// Node roles.
	pub roles: Roles,
	/// How to spawn background tasks. Mandatory, otherwise creating a `Service` will error.
	pub task_executor: Option<Arc<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>) + Send + Sync>>,
	/// Extrinsic pool configuration.
	pub transaction_pool: TransactionPoolOptions,
	/// Network configuration.
	pub network: NetworkConfiguration,
	/// Path to the base configuration directory.
	pub config_dir: Option<PathBuf>,
	/// Configuration for the keystore.
	pub keystore: KeystoreConfig,
	/// Configuration for the database.
	pub database: Option<DatabaseConfig>,
	/// Size of internal state cache in Bytes
	pub state_cache_size: usize,
	/// Size in percent of cache size dedicated to child tries
	pub state_cache_child_ratio: Option<usize>,
	/// Pruning settings.
	pub pruning: PruningMode,
	/// Chain configuration.
	pub chain_spec: Option<Box<dyn ChainSpec>>,
	/// Node name.
	pub name: String,
	/// Wasm execution method.
	pub wasm_method: WasmExecutionMethod,
	/// Execution strategies.
	pub execution_strategies: ExecutionStrategies,
	/// RPC over HTTP binding address. `None` if disabled.
	pub rpc_http: Option<SocketAddr>,
	/// RPC over Websockets binding address. `None` if disabled.
	pub rpc_ws: Option<SocketAddr>,
	/// Maximum number of connections for WebSockets RPC server. `None` if default.
	pub rpc_ws_max_connections: Option<usize>,
	/// CORS settings for HTTP & WS servers. `None` if all origins are allowed.
	pub rpc_cors: Option<Vec<String>>,
	/// Prometheus endpoint configuration. `None` if disabled.
	pub prometheus_config: Option<PrometheusConfig>,
	/// Telemetry service URL. `None` if disabled.
	pub telemetry_endpoints: Option<TelemetryEndpoints>,
	/// External WASM transport for the telemetry. If `Some`, when connection to a telemetry
	/// endpoint, this transport will be tried in priority before all others.
	pub telemetry_external_transport: Option<ExtTransport>,
	/// The default number of 64KB pages to allocate for Wasm execution
	pub default_heap_pages: Option<u64>,
	/// Should offchain workers be executed.
	pub offchain_worker: bool,
	/// Sentry mode is enabled, the node's role is AUTHORITY but it should not
	/// actively participate in consensus (i.e. no keystores should be passed to
	/// consensus modules).
	pub sentry_mode: bool,
	/// Enable authoring even when offline.
	pub force_authoring: bool,
	/// Disable GRANDPA when running in validator mode
	pub disable_grandpa: bool,
	/// Development key seed.
	///
	/// When running in development mode, the seed will be used to generate authority keys by the keystore.
	///
	/// Should only be set when `node` is running development mode.
	pub dev_key_seed: Option<String>,
	/// Tracing targets
	pub tracing_targets: Option<String>,
	/// Tracing receiver
	pub tracing_receiver: sc_tracing::TracingReceiver,
	/// The size of the instances cache.
	///
	/// The default value is 8.
	pub max_runtime_instances: usize,
}

/// Configuration of the client keystore.
#[derive(Clone)]
pub enum KeystoreConfig {
	/// No config supplied.
	None,
	/// Keystore at a path on-disk. Recommended for native nodes.
	Path {
		/// The path of the keystore.
		path: PathBuf,
		/// Node keystore's password.
		password: Option<Protected<String>>
	},
	/// In-memory keystore. Recommended for in-browser nodes.
	InMemory,
}

impl KeystoreConfig {
	/// Returns the path for the keystore.
	pub fn path(&self) -> Option<&Path> {
		match self {
			Self::Path { path, .. } => Some(&path),
			Self::None | Self::InMemory => None,
		}
	}
}

/// Configuration of the database of the client.
#[derive(Clone)]
pub enum DatabaseConfig {
	/// Database file at a specific path. Recommended for most uses.
	Path {
		/// Path to the database.
		path: PathBuf,
		/// Cache Size for internal database in MiB
		cache_size: Option<u32>,
	},

	/// A custom implementation of an already-open database.
	Custom(Arc<dyn KeyValueDB>),
}

/// Configuration of the Prometheus endpoint.
#[derive(Clone)]
pub struct PrometheusConfig {
	/// Port to use.
	pub port: SocketAddr,
	/// A metrics registry to use. Useful for setting the metric prefix.
	pub registry: Registry,
}

impl PrometheusConfig {
	/// Create a new config using the default registry.
	///
	/// The default registry prefixes metrics with `substrate`.
	pub fn new_with_default_registry(port: SocketAddr) -> Self {
		Self {
			port,
			registry: Registry::new_custom(Some("substrate".into()), None)
				.expect("this can only fail if the prefix is empty")
		}
	}
}

impl Default for Configuration {
	/// Create a default config
	fn default() -> Self {
		Configuration {
			impl_name: "parity-substrate",
			impl_version: "0.0.0",
			impl_commit: "",
			chain_spec: None,
			config_dir: None,
			name: Default::default(),
			roles: Roles::FULL,
			task_executor: None,
			transaction_pool: Default::default(),
			network: Default::default(),
			keystore: KeystoreConfig::None,
			database: None,
			state_cache_size: Default::default(),
			state_cache_child_ratio: Default::default(),
			pruning: PruningMode::default(),
			wasm_method: WasmExecutionMethod::Interpreted,
			execution_strategies: Default::default(),
			rpc_http: None,
			rpc_ws: None,
			rpc_ws_max_connections: None,
			rpc_cors: Some(vec![]),
			prometheus_config: None,
			telemetry_endpoints: None,
			telemetry_external_transport: None,
			default_heap_pages: None,
			offchain_worker: Default::default(),
			sentry_mode: false,
			force_authoring: false,
			disable_grandpa: false,
			dev_key_seed: None,
			tracing_targets: Default::default(),
			tracing_receiver: Default::default(),
			max_runtime_instances: 8,
		}
	}
}

impl Configuration {
	/// Create a default config using `VersionInfo`
	pub fn from_version(version: &VersionInfo) -> Self {
		let mut config = Configuration::default();
		config.impl_name = version.name;
		config.impl_version = version.version;
		config.impl_commit = version.commit;

		config
	}

	/// Returns full version string of this configuration.
	pub fn full_version(&self) -> String {
		full_version_from_strs(self.impl_version, self.impl_commit)
	}

	/// Implementation id and version.
	pub fn client_id(&self) -> String {
		format!("{}/v{}", self.impl_name, self.full_version())
	}

	/// Generate a PathBuf to sub in the chain configuration directory
	/// if given
	pub fn in_chain_config_dir(&self, sub: &str) -> Option<PathBuf> {
		self.config_dir.clone().map(|mut path| {
			path.push("chains");
			path.push(self.expect_chain_spec().id());
			path.push(sub);
			path
		})
	}

	/// Return a reference to the `ChainSpec` of this `Configuration`.
	///
	/// ### Panics
	///
	/// This method panic if the `chain_spec` is `None`
	pub fn expect_chain_spec(&self) -> &dyn ChainSpec {
		&**self.chain_spec.as_ref().expect("chain_spec must be specified")
	}

	/// Return a reference to the `DatabaseConfig` of this `Configuration`.
	///
	/// ### Panics
	///
	/// This method panic if the `database` is `None`
	pub fn expect_database(&self) -> &DatabaseConfig {
		self.database.as_ref().expect("database must be specified")
	}

	/// Returns a string displaying the node role, special casing the sentry mode
	/// (returning `SENTRY`), since the node technically has an `AUTHORITY` role but
	/// doesn't participate.
	pub fn display_role(&self) -> String {
		if self.sentry_mode {
			"SENTRY".to_string()
		} else {
			self.roles.to_string()
		}
	}

	/// Use in memory keystore config when it is not required at all.
	///
	/// This function returns an error if the keystore is already set to something different than
	/// `KeystoreConfig::None`.
	pub fn use_in_memory_keystore(&mut self) -> Result<(), String> {
		match &mut self.keystore {
			cfg @ KeystoreConfig::None => { *cfg = KeystoreConfig::InMemory; Ok(()) },
			_ => Err("Keystore config specified when it should not be!".into()),
		}
	}
}

/// Returns platform info
pub fn platform() -> String {
	let env = Target::env();
	let env_dash = if env.is_empty() { "" } else { "-" };
	format!("{}-{}{}{}", Target::arch(), Target::os(), env_dash, env)
}

/// Returns full version string, using supplied version and commit.
pub fn full_version_from_strs(impl_version: &str, impl_commit: &str) -> String {
	let commit_dash = if impl_commit.is_empty() { "" } else { "-" };
	format!("{}{}{}-{}", impl_version, commit_dash, impl_commit, platform())
}
