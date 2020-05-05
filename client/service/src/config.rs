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

pub use sc_client_db::{Database, PruningMode, DatabaseSettingsSrc as DatabaseConfig};
pub use sc_network::Multiaddr;
pub use sc_network::config::{ExtTransport, MultiaddrWithPeerId, NetworkConfiguration, Role, NodeKeyConfig};
pub use sc_executor::WasmExecutionMethod;
use sc_client_api::execution_extensions::ExecutionStrategies;

use std::{future::Future, path::{PathBuf, Path}, pin::Pin, net::SocketAddr, sync::Arc};
pub use sc_transaction_pool::txpool::Options as TransactionPoolOptions;
use sc_chain_spec::ChainSpec;
use sp_core::crypto::Protected;
pub use sc_telemetry::TelemetryEndpoints;
use prometheus_endpoint::Registry;

/// Service configuration.
pub struct Configuration {
	/// Implementation name
	pub impl_name: &'static str,
	/// Implementation version (see sc-cli to see an example of format)
	pub impl_version: &'static str,
	/// Node role.
	pub role: Role,
	/// How to spawn background tasks. Mandatory, otherwise creating a `Service` will error.
	pub task_executor: Arc<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>, TaskType) + Send + Sync>,
	/// Extrinsic pool configuration.
	pub transaction_pool: TransactionPoolOptions,
	/// Network configuration.
	pub network: NetworkConfiguration,
	/// Configuration for the keystore.
	pub keystore: KeystoreConfig,
	/// Configuration for the database.
	pub database: DatabaseConfig,
	/// Size of internal state cache in Bytes
	pub state_cache_size: usize,
	/// Size in percent of cache size dedicated to child tries
	pub state_cache_child_ratio: Option<usize>,
	/// Pruning settings.
	pub pruning: PruningMode,
	/// Chain configuration.
	pub chain_spec: Box<dyn ChainSpec>,
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
	/// RPC methods to expose (by default only a safe subset or all of them).
	pub rpc_methods: RpcMethods,
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
	pub offchain_worker: OffchainWorkerConfig,
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
	/// Announce block automatically after they have been imported
	pub announce_block: bool,
}

/// Type for tasks spawned by the executor.
#[derive(PartialEq)]
pub enum TaskType {
	/// Regular non-blocking futures. Polling the task is expected to be a lightweight operation.
	Async,
	/// The task might perform a lot of expensive CPU operations and/or call `thread::sleep`.
	Blocking,
}

/// Configuration of the client keystore.
#[derive(Clone)]
pub enum KeystoreConfig {
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
			Self::Path { path, .. } => Some(path),
			Self::InMemory => None,
		}
	}
}
/// Configuration of the database of the client.
#[derive(Clone, Default)]
pub struct OffchainWorkerConfig {
	/// If this is allowed.
	pub enabled: bool,
	/// allow writes from the runtime to the offchain worker database.
	pub indexing_enabled: bool,
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

impl Configuration {
	/// Returns a string displaying the node role.
	pub fn display_role(&self) -> String {
		self.role.to_string()
	}
}

/// Available RPC methods.
#[derive(Debug, Copy, Clone)]
pub enum RpcMethods {
	/// Expose every RPC method only when RPC is listening on `localhost`,
	/// otherwise serve only safe RPC methods.
	Auto,
	/// Allow only a safe subset of RPC methods.
	Safe,
	/// Expose every RPC method (even potentially unsafe ones).
	Unsafe,
}

impl Default for RpcMethods {
	fn default() -> RpcMethods {
		RpcMethods::Auto
	}
}
