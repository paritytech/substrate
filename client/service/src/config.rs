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

//! Service configuration.

pub use client::ExecutionStrategies;
pub use client_db::{kvdb::KeyValueDB, PruningMode};
pub use network::config::{ExtTransport, NetworkConfiguration, Roles};
pub use sc_executor::WasmExecutionMethod;

use std::{path::PathBuf, net::SocketAddr, sync::Arc};
pub use txpool::txpool::Options as TransactionPoolOptions;
use chain_spec::{ChainSpec, RuntimeGenesis, Extension, NoExtension};
use primitives::crypto::Protected;
use target_info::Target;
use tel::TelemetryEndpoints;

/// Service configuration.
#[derive(Clone)]
pub struct Configuration<C, G, E = NoExtension> {
	/// Implementation name
	pub impl_name: &'static str,
	/// Implementation version
	pub impl_version: &'static str,
	/// Git commit if any.
	pub impl_commit: &'static str,
	/// Node roles.
	pub roles: Roles,
	/// Extrinsic pool configuration.
	pub transaction_pool: TransactionPoolOptions,
	/// Network configuration.
	pub network: NetworkConfiguration,
	/// Path to the base configuration directory.
	pub config_dir: Option<PathBuf>,
	/// Path to key files.
	pub keystore_path: Option<PathBuf>,
	/// Configuration for the database.
	pub database: DatabaseConfig,
	/// Size of internal state cache in Bytes
	pub state_cache_size: usize,
	/// Size in percent of cache size dedicated to child tries
	pub state_cache_child_ratio: Option<usize>,
	/// Pruning settings.
	pub pruning: PruningMode,
	/// Chain configuration.
	pub chain_spec: ChainSpec<G, E>,
	/// Custom configuration.
	pub custom: C,
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
	/// Grafana data source http port. `None` if disabled.
	pub grafana_port: Option<SocketAddr>,
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
	/// Node keystore's password
	pub keystore_password: Option<Protected<String>>,
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

impl<C, G, E> Configuration<C, G, E> where
	C: Default,
	G: RuntimeGenesis,
	E: Extension,
{
	/// Create a default config for given chain spec and path to configuration dir
	pub fn default_with_spec_and_base_path(chain_spec: ChainSpec<G, E>, config_dir: Option<PathBuf>) -> Self {
		let mut configuration = Configuration {
			impl_name: "parity-substrate",
			impl_version: "0.0.0",
			impl_commit: "",
			chain_spec,
			config_dir: config_dir.clone(),
			name: Default::default(),
			roles: Roles::FULL,
			transaction_pool: Default::default(),
			network: Default::default(),
			keystore_path: config_dir.map(|c| c.join("keystore")),
			database: DatabaseConfig::Path {
				path: Default::default(),
				cache_size: Default::default(),
			},
			state_cache_size: Default::default(),
			state_cache_child_ratio: Default::default(),
			custom: Default::default(),
			pruning: PruningMode::default(),
			wasm_method: WasmExecutionMethod::Interpreted,
			execution_strategies: Default::default(),
			rpc_http: None,
			rpc_ws: None,
			rpc_ws_max_connections: None,
			rpc_cors: Some(vec![]),
			grafana_port: None,
			telemetry_endpoints: None,
			telemetry_external_transport: None,
			default_heap_pages: None,
			offchain_worker: Default::default(),
			sentry_mode: false,
			force_authoring: false,
			disable_grandpa: false,
			keystore_password: None,
			dev_key_seed: None,
			tracing_targets: Default::default(),
			tracing_receiver: Default::default(),
		};
		configuration.network.boot_nodes = configuration.chain_spec.boot_nodes().to_vec();

		configuration.telemetry_endpoints = configuration.chain_spec.telemetry_endpoints().clone();

		configuration
	}

}

impl<C, G, E> Configuration<C, G, E> {
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
			path.push(self.chain_spec.id());
			path.push(sub);
			path
		})
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
