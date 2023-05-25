// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Service configuration.

pub use sc_client_api::execution_extensions::{ExecutionStrategies, ExecutionStrategy};
pub use sc_client_db::{BlocksPruning, Database, DatabaseSource, PruningMode};
pub use sc_executor::{WasmExecutionMethod, WasmtimeInstantiationStrategy};
pub use sc_network::{
	config::{
		MultiaddrWithPeerId, NetworkConfiguration, NodeKeyConfig, NonDefaultSetConfig, ProtocolId,
		Role, SetConfig, SyncMode, TransportConfig,
	},
	request_responses::{
		IncomingRequest, OutgoingResponse, ProtocolConfig as RequestResponseConfig,
	},
	Multiaddr,
};

use prometheus_endpoint::Registry;
use sc_chain_spec::ChainSpec;
pub use sc_telemetry::TelemetryEndpoints;
pub use sc_transaction_pool::Options as TransactionPoolOptions;
use sp_core::crypto::SecretString;
use std::{
	io, iter,
	net::SocketAddr,
	path::{Path, PathBuf},
};
use tempfile::TempDir;

/// Service configuration.
#[derive(Debug)]
pub struct Configuration {
	/// Implementation name
	pub impl_name: String,
	/// Implementation version (see sc-cli to see an example of format)
	pub impl_version: String,
	/// Node role.
	pub role: Role,
	/// Handle to the tokio runtime. Will be used to spawn futures by the task manager.
	pub tokio_handle: tokio::runtime::Handle,
	/// Extrinsic pool configuration.
	pub transaction_pool: TransactionPoolOptions,
	/// Network configuration.
	pub network: NetworkConfiguration,
	/// Configuration for the keystore.
	pub keystore: KeystoreConfig,
	/// Remote URI to connect to for async keystore support
	pub keystore_remote: Option<String>,
	/// Configuration for the database.
	pub database: DatabaseSource,
	/// Maximum size of internal trie cache in bytes.
	///
	/// If `None` is given the cache is disabled.
	pub trie_cache_maximum_size: Option<usize>,
	/// State pruning settings.
	pub state_pruning: Option<PruningMode>,
	/// Number of blocks to keep in the db.
	///
	/// NOTE: only finalized blocks are subject for removal!
	pub blocks_pruning: BlocksPruning,
	/// Chain configuration.
	pub chain_spec: Box<dyn ChainSpec>,
	/// Wasm execution method.
	pub wasm_method: WasmExecutionMethod,
	/// Directory where local WASM runtimes live. These runtimes take precedence
	/// over on-chain runtimes when the spec version matches. Set to `None` to
	/// disable overrides (default).
	pub wasm_runtime_overrides: Option<PathBuf>,
	/// Execution strategies.
	pub execution_strategies: ExecutionStrategies,
	/// RPC over HTTP binding address. `None` if disabled.
	pub rpc_http: Option<SocketAddr>,
	/// RPC over Websockets binding address. `None` if disabled.
	pub rpc_ws: Option<SocketAddr>,
	/// RPC over IPC binding path. `None` if disabled.
	pub rpc_ipc: Option<String>,
	/// Maximum number of connections for WebSockets RPC server. `None` if default.
	pub rpc_ws_max_connections: Option<usize>,
	/// CORS settings for HTTP & WS servers. `None` if all origins are allowed.
	pub rpc_cors: Option<Vec<String>>,
	/// RPC methods to expose (by default only a safe subset or all of them).
	pub rpc_methods: RpcMethods,
	/// Maximum payload of rpc request/responses.
	pub rpc_max_payload: Option<usize>,
	/// Maximum payload of a rpc request
	pub rpc_max_request_size: Option<usize>,
	/// Maximum payload of a rpc request
	pub rpc_max_response_size: Option<usize>,
	/// Custom JSON-RPC subscription ID provider.
	///
	/// Default: [`crate::RandomStringSubscriptionId`].
	pub rpc_id_provider: Option<Box<dyn crate::RpcSubscriptionIdProvider>>,
	/// Maximum allowed subscriptions per rpc connection
	///
	/// Default: 1024.
	pub rpc_max_subs_per_conn: Option<usize>,
	/// Maximum size of the output buffer capacity for websocket connections.
	pub ws_max_out_buffer_capacity: Option<usize>,
	/// Prometheus endpoint configuration. `None` if disabled.
	pub prometheus_config: Option<PrometheusConfig>,
	/// Telemetry service URL. `None` if disabled.
	pub telemetry_endpoints: Option<TelemetryEndpoints>,
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
	/// When running in development mode, the seed will be used to generate authority keys by the
	/// keystore.
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
	/// Base path of the configuration
	pub base_path: Option<BasePath>,
	/// Configuration of the output format that the informant uses.
	pub informant_output_format: sc_informant::OutputFormat,
	/// Maximum number of different runtime versions that can be cached.
	pub runtime_cache_size: u8,
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
#[derive(Debug, Clone)]
pub enum KeystoreConfig {
	/// Keystore at a path on-disk. Recommended for native nodes.
	Path {
		/// The path of the keystore.
		path: PathBuf,
		/// Node keystore's password.
		password: Option<SecretString>,
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
#[derive(Debug, Clone, Default)]
pub struct OffchainWorkerConfig {
	/// If this is allowed.
	pub enabled: bool,
	/// allow writes from the runtime to the offchain worker database.
	pub indexing_enabled: bool,
}

/// Configuration of the Prometheus endpoint.
#[derive(Debug, Clone)]
pub struct PrometheusConfig {
	/// Port to use.
	pub port: SocketAddr,
	/// A metrics registry to use. Useful for setting the metric prefix.
	pub registry: Registry,
}

impl PrometheusConfig {
	/// Create a new config using the default registry.
	pub fn new_with_default_registry(port: SocketAddr, chain_id: String) -> Self {
		let param = iter::once((String::from("chain"), chain_id)).collect();
		Self {
			port,
			registry: Registry::new_custom(None, Some(param))
				.expect("this can only fail if the prefix is empty"),
		}
	}
}

impl Configuration {
	/// Returns a string displaying the node role.
	pub fn display_role(&self) -> String {
		self.role.to_string()
	}

	/// Returns the prometheus metrics registry, if available.
	pub fn prometheus_registry(&self) -> Option<&Registry> {
		self.prometheus_config.as_ref().map(|config| &config.registry)
	}

	/// Returns the network protocol id from the chain spec, or the default.
	pub fn protocol_id(&self) -> ProtocolId {
		let protocol_id_full = match self.chain_spec.protocol_id() {
			Some(pid) => pid,
			None => {
				log::warn!(
					"Using default protocol ID {:?} because none is configured in the \
					chain specs",
					crate::DEFAULT_PROTOCOL_ID
				);
				crate::DEFAULT_PROTOCOL_ID
			},
		};
		ProtocolId::from(protocol_id_full)
	}

	/// Returns true if the genesis state writting will be skipped while initializing the genesis
	/// block.
	pub fn no_genesis(&self) -> bool {
		matches!(self.network.sync_mode, SyncMode::Fast { .. } | SyncMode::Warp { .. })
	}

	/// Returns the database config for creating the backend.
	pub fn db_config(&self) -> sc_client_db::DatabaseSettings {
		sc_client_db::DatabaseSettings {
			trie_cache_maximum_size: self.trie_cache_maximum_size,
			state_pruning: self.state_pruning.clone(),
			source: self.database.clone(),
			blocks_pruning: self.blocks_pruning,
		}
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

#[static_init::dynamic(drop, lazy)]
static mut BASE_PATH_TEMP: Option<TempDir> = None;

/// The base path that is used for everything that needs to be written on disk to run a node.
#[derive(Debug)]
pub struct BasePath {
	path: PathBuf,
}

impl BasePath {
	/// Create a `BasePath` instance using a temporary directory prefixed with "substrate" and use
	/// it as base path.
	///
	/// Note: The temporary directory will be created automatically and deleted when the program
	/// exits. Every call to this function will return the same path for the lifetime of the
	/// program.
	pub fn new_temp_dir() -> io::Result<BasePath> {
		let mut temp = BASE_PATH_TEMP.write();

		match &*temp {
			Some(p) => Ok(Self::new(p.path())),
			None => {
				let temp_dir = tempfile::Builder::new().prefix("substrate").tempdir()?;
				let path = PathBuf::from(temp_dir.path());

				*temp = Some(temp_dir);
				Ok(Self::new(path))
			},
		}
	}

	/// Create a `BasePath` instance based on an existing path on disk.
	///
	/// Note: this function will not ensure that the directory exist nor create the directory. It
	/// will also not delete the directory when the instance is dropped.
	pub fn new<P: Into<PathBuf>>(path: P) -> BasePath {
		Self { path: path.into() }
	}

	/// Create a base path from values describing the project.
	pub fn from_project(qualifier: &str, organization: &str, application: &str) -> BasePath {
		BasePath::new(
			directories::ProjectDirs::from(qualifier, organization, application)
				.expect("app directories exist on all supported platforms; qed")
				.data_local_dir(),
		)
	}

	/// Retrieve the base path.
	pub fn path(&self) -> &Path {
		&self.path
	}

	/// Returns the configuration directory inside this base path.
	///
	/// The path looks like `$base_path/chains/$chain_id`
	pub fn config_dir(&self, chain_id: &str) -> PathBuf {
		self.path().join("chains").join(chain_id)
	}
}

impl From<PathBuf> for BasePath {
	fn from(path: PathBuf) -> Self {
		BasePath::new(path)
	}
}
