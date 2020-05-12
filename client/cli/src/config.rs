// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Configuration trait for a CLI based on substrate

use crate::arg_enums::Database;
use crate::error::Result;
use crate::{
	init_logger, DatabaseParams, ImportParams, KeystoreParams, NetworkParams, NodeKeyParams,
	OffchainWorkerParams, PruningParams, SharedParams, SubstrateCli,
};
use app_dirs::{AppDataType, AppInfo};
use names::{Generator, Name};
use sc_client_api::execution_extensions::ExecutionStrategies;
use sc_service::config::{
	Configuration, DatabaseConfig, ExtTransport, KeystoreConfig, NetworkConfiguration,
	NodeKeyConfig, OffchainWorkerConfig, PrometheusConfig, PruningMode, Role, RpcMethods,
	TaskType, TelemetryEndpoints, TransactionPoolOptions, WasmExecutionMethod,
};
use sc_service::{ChainSpec, TracingReceiver};
use std::future::Future;
use std::net::SocketAddr;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::Arc;

/// The maximum number of characters for a node name.
pub(crate) const NODE_NAME_MAX_LENGTH: usize = 32;

/// default sub directory to store network config
pub(crate) const DEFAULT_NETWORK_CONFIG_PATH: &'static str = "network";

/// A trait that allows converting an object to a Configuration
pub trait CliConfiguration: Sized {
	/// Get the SharedParams for this object
	fn shared_params(&self) -> &SharedParams;

	/// Get the ImportParams for this object
	fn import_params(&self) -> Option<&ImportParams> {
		None
	}

	/// Get the PruningParams for this object
	fn pruning_params(&self) -> Option<&PruningParams> {
		self.import_params().map(|x| &x.pruning_params)
	}

	/// Get the KeystoreParams for this object
	fn keystore_params(&self) -> Option<&KeystoreParams> {
		None
	}

	/// Get the NetworkParams for this object
	fn network_params(&self) -> Option<&NetworkParams> {
		None
	}

	/// Get a reference to `OffchainWorkerParams` for this object.
	fn offchain_worker_params(&self) -> Option<&OffchainWorkerParams> {
		None
	}

	/// Get the NodeKeyParams for this object
	fn node_key_params(&self) -> Option<&NodeKeyParams> {
		self.network_params().map(|x| &x.node_key_params)
	}

	/// Get the DatabaseParams for this object
	fn database_params(&self) -> Option<&DatabaseParams> {
		self.import_params().map(|x| &x.database_params)
	}

	/// Get the base path of the configuration (if any)
	///
	/// By default this is retrieved from `SharedParams`.
	fn base_path(&self) -> Result<Option<PathBuf>> {
		Ok(self.shared_params().base_path())
	}

	/// Returns `true` if the node is for development or not
	///
	/// By default this is retrieved from `SharedParams`.
	fn is_dev(&self) -> Result<bool> {
		Ok(self.shared_params().is_dev())
	}

	/// Gets the role
	///
	/// By default this is `Role::Full`.
	fn role(&self, _is_dev: bool) -> Result<Role> {
		Ok(Role::Full)
	}

	/// Get the transaction pool options
	///
	/// By default this is `TransactionPoolOptions::default()`.
	fn transaction_pool(&self) -> Result<TransactionPoolOptions> {
		Ok(Default::default())
	}

	/// Get the network configuration
	///
	/// By default this is retrieved from `NetworkParams` if it is available otherwise it creates
	/// a default `NetworkConfiguration` based on `node_name`, `client_id`, `node_key` and
	/// `net_config_dir`.
	fn network_config(
		&self,
		chain_spec: &Box<dyn ChainSpec>,
		is_dev: bool,
		net_config_dir: PathBuf,
		client_id: &str,
		node_name: &str,
		node_key: NodeKeyConfig,
	) -> Result<NetworkConfiguration> {
		Ok(if let Some(network_params) = self.network_params() {
			network_params.network_config(
				chain_spec,
				is_dev,
				Some(net_config_dir),
				client_id,
				node_name,
				node_key,
			)
		} else {
			NetworkConfiguration::new(
				node_name,
				client_id,
				node_key,
				Some(net_config_dir),
			)
		})
	}

	/// Get the keystore configuration.
	///
	/// Bu default this is retrieved from `KeystoreParams` if it is available. Otherwise it uses
	/// `KeystoreConfig::InMemory`.
	fn keystore_config(&self, base_path: &PathBuf) -> Result<KeystoreConfig> {
		self.keystore_params()
			.map(|x| x.keystore_config(base_path))
			.unwrap_or(Ok(KeystoreConfig::InMemory))
	}

	/// Get the database cache size.
	///
	/// By default this is retrieved from `DatabaseParams` if it is available. Otherwise its `None`.
	fn database_cache_size(&self) -> Result<Option<usize>> {
		Ok(self.database_params()
			.map(|x| x.database_cache_size())
			.unwrap_or(Default::default()))
	}

	/// Get the database backend variant.
	///
	/// By default this is retrieved from `DatabaseParams` if it is available. Otherwise its `None`.
	fn database(&self) -> Result<Option<Database>> {
		Ok(self.database_params().and_then(|x| x.database()))
	}

	/// Get the database configuration object for the parameters provided
	fn database_config(
		&self,
		base_path: &PathBuf,
		cache_size: usize,
		database: Database,
	) -> Result<DatabaseConfig> {
		Ok(match database {
			Database::RocksDb => DatabaseConfig::RocksDb {
				path: base_path.join("db"),
				cache_size,
			},
			Database::SubDb => DatabaseConfig::SubDb {
				path: base_path.join("subdb"),
			},
			Database::ParityDb => DatabaseConfig::ParityDb {
				path: base_path.join("paritydb"),
			},
		})
	}

	/// Get the state cache size.
	///
	/// By default this is retrieved from `ImportParams` if it is available. Otherwise its `0`.
	fn state_cache_size(&self) -> Result<usize> {
		Ok(self.import_params()
			.map(|x| x.state_cache_size())
			.unwrap_or(Default::default()))
	}

	/// Get the state cache child ratio (if any).
	///
	/// By default this is `None`.
	fn state_cache_child_ratio(&self) -> Result<Option<usize>> {
		Ok(Default::default())
	}

	/// Get the pruning mode.
	///
	/// By default this is retrieved from `PruningMode` if it is available. Otherwise its
	/// `PruningMode::default()`.
	fn pruning(&self, unsafe_pruning: bool, role: &Role) -> Result<PruningMode> {
		self.pruning_params()
			.map(|x| x.pruning(unsafe_pruning, role))
			.unwrap_or(Ok(Default::default()))
	}

	/// Get the chain ID (string).
	///
	/// By default this is retrieved from `SharedParams`.
	fn chain_id(&self, is_dev: bool) -> Result<String> {
		Ok(self.shared_params().chain_id(is_dev))
	}

	/// Get the name of the node.
	///
	/// By default a random name is generated.
	fn node_name(&self) -> Result<String> {
		Ok(generate_node_name())
	}

	/// Get the WASM execution method.
	///
	/// By default this is retrieved from `ImportParams` if it is available. Otherwise its
	/// `WasmExecutionMethod::default()`.
	fn wasm_method(&self) -> Result<WasmExecutionMethod> {
		Ok(self.import_params()
			.map(|x| x.wasm_method())
			.unwrap_or(Default::default()))
	}

	/// Get the execution strategies.
	///
	/// By default this is retrieved from `ImportParams` if it is available. Otherwise its
	/// `ExecutionStrategies::default()`.
	fn execution_strategies(&self, is_dev: bool) -> Result<ExecutionStrategies> {
		Ok(self.import_params()
			.map(|x| x.execution_strategies(is_dev))
			.unwrap_or(Default::default()))
	}

	/// Get the RPC HTTP address (`None` if disabled).
	///
	/// By default this is `None`.
	fn rpc_http(&self) -> Result<Option<SocketAddr>> {
		Ok(Default::default())
	}

	/// Get the RPC websocket address (`None` if disabled).
	///
	/// By default this is `None`.
	fn rpc_ws(&self) -> Result<Option<SocketAddr>> {
		Ok(Default::default())
	}

	/// Returns the RPC method set to expose.
	///
	/// By default this is `RpcMethods::Auto` (unsafe RPCs are denied iff
	/// `{rpc,ws}_external` returns true, respectively).
	fn rpc_methods(&self) -> Result<RpcMethods> {
		Ok(Default::default())
	}

	/// Get the RPC websockets maximum connections (`None` if unlimited).
	///
	/// By default this is `None`.
	fn rpc_ws_max_connections(&self) -> Result<Option<usize>> {
		Ok(Default::default())
	}

	/// Get the RPC cors (`None` if disabled)
	///
	/// By default this is `None`.
	fn rpc_cors(&self, _is_dev: bool) -> Result<Option<Vec<String>>> {
		Ok(Some(Vec::new()))
	}

	/// Get the prometheus configuration (`None` if disabled)
	///
	/// By default this is `None`.
	fn prometheus_config(&self) -> Result<Option<PrometheusConfig>> {
		Ok(Default::default())
	}

	/// Get the telemetry endpoints (if any)
	///
	/// By default this is retrieved from the chain spec loaded by `load_spec`.
	fn telemetry_endpoints(
		&self,
		chain_spec: &Box<dyn ChainSpec>,
	) -> Result<Option<TelemetryEndpoints>> {
		Ok(chain_spec.telemetry_endpoints().clone())
	}

	/// Get the telemetry external transport
	///
	/// By default this is `None`.
	fn telemetry_external_transport(&self) -> Result<Option<ExtTransport>> {
		Ok(Default::default())
	}

	/// Get the default value for heap pages
	///
	/// By default this is `None`.
	fn default_heap_pages(&self) -> Result<Option<u64>> {
		Ok(Default::default())
	}

	/// Returns an offchain worker config wrapped in `Ok(_)`
	///
	/// By default offchain workers are disabled.
	fn offchain_worker(&self, role: &Role) -> Result<OffchainWorkerConfig> {
		self.offchain_worker_params()
			.map(|x| x.offchain_worker(role))
			.unwrap_or_else(|| Ok(OffchainWorkerConfig::default()))
	}

	/// Returns `Ok(true)` if authoring should be forced
	///
	/// By default this is `false`.
	fn force_authoring(&self) -> Result<bool> {
		Ok(Default::default())
	}

	/// Returns `Ok(true)` if grandpa should be disabled
	///
	/// By default this is `false`.
	fn disable_grandpa(&self) -> Result<bool> {
		Ok(Default::default())
	}

	/// Get the development key seed from the current object
	///
	/// By default this is `None`.
	fn dev_key_seed(&self, _is_dev: bool) -> Result<Option<String>> {
		Ok(Default::default())
	}

	/// Get the tracing targets from the current object (if any)
	///
	/// By default this is retrieved from `ImportParams` if it is available. Otherwise its
	/// `None`.
	fn tracing_targets(&self) -> Result<Option<String>> {
		Ok(self.import_params()
			.map(|x| x.tracing_targets())
			.unwrap_or(Default::default()))
	}

	/// Get the TracingReceiver value from the current object
	///
	/// By default this is retrieved from `ImportParams` if it is available. Otherwise its
	/// `TracingReceiver::default()`.
	fn tracing_receiver(&self) -> Result<TracingReceiver> {
		Ok(self.import_params()
			.map(|x| x.tracing_receiver())
			.unwrap_or(Default::default()))
	}

	/// Get the node key from the current object
	///
	/// By default this is retrieved from `NodeKeyParams` if it is available. Otherwise its
	/// `NodeKeyConfig::default()`.
	fn node_key(&self, net_config_dir: &PathBuf) -> Result<NodeKeyConfig> {
		self.node_key_params()
			.map(|x| x.node_key(net_config_dir))
			.unwrap_or(Ok(Default::default()))
	}

	/// Get maximum runtime instances
	///
	/// By default this is `None`.
	fn max_runtime_instances(&self) -> Result<Option<usize>> {
		Ok(Default::default())
	}

	/// Activate or not the automatic announcing of blocks after import
	///
	/// By default this is `false`.
	fn announce_block(&self) -> Result<bool> {
		Ok(true)
	}

	/// Create a Configuration object from the current object
	fn create_configuration<C: SubstrateCli>(
		&self,
		cli: &C,
		task_executor: Arc<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>, TaskType) + Send + Sync>,
	) -> Result<Configuration> {
		let is_dev = self.is_dev()?;
		let chain_id = self.chain_id(is_dev)?;
		let chain_spec = cli.load_spec(chain_id.as_str())?;
		let config_dir = self
			.base_path()?
			.unwrap_or_else(|| {
				app_dirs::get_app_root(
					AppDataType::UserData,
					&AppInfo {
						name: C::executable_name(),
						author: C::author(),
					},
				)
				.expect("app directories exist on all supported platforms; qed")
			})
			.join("chains")
			.join(chain_spec.id());
		let net_config_dir = config_dir.join(DEFAULT_NETWORK_CONFIG_PATH);
		let client_id = C::client_id();
		let database_cache_size = self.database_cache_size()?.unwrap_or(128);
		let database = self.database()?.unwrap_or(Database::RocksDb);
		let node_key = self.node_key(&net_config_dir)?;
		let role = self.role(is_dev)?;
		let max_runtime_instances = self.max_runtime_instances()?.unwrap_or(8);

		let unsafe_pruning = self
			.import_params()
			.map(|p| p.unsafe_pruning)
			.unwrap_or(false);

		Ok(Configuration {
			impl_name: C::impl_name(),
			impl_version: C::impl_version(),
			task_executor,
			transaction_pool: self.transaction_pool()?,
			network: self.network_config(
				&chain_spec,
				is_dev,
				net_config_dir,
				client_id.as_str(),
				self.node_name()?.as_str(),
				node_key,
			)?,
			keystore: self.keystore_config(&config_dir)?,
			database: self.database_config(&config_dir, database_cache_size, database)?,
			state_cache_size: self.state_cache_size()?,
			state_cache_child_ratio: self.state_cache_child_ratio()?,
			pruning: self.pruning(unsafe_pruning, &role)?,
			wasm_method: self.wasm_method()?,
			execution_strategies: self.execution_strategies(is_dev)?,
			rpc_http: self.rpc_http()?,
			rpc_ws: self.rpc_ws()?,
			rpc_methods: self.rpc_methods()?,
			rpc_ws_max_connections: self.rpc_ws_max_connections()?,
			rpc_cors: self.rpc_cors(is_dev)?,
			prometheus_config: self.prometheus_config()?,
			telemetry_endpoints: self.telemetry_endpoints(&chain_spec)?,
			telemetry_external_transport: self.telemetry_external_transport()?,
			default_heap_pages: self.default_heap_pages()?,
			offchain_worker: self.offchain_worker(&role)?,
			force_authoring: self.force_authoring()?,
			disable_grandpa: self.disable_grandpa()?,
			dev_key_seed: self.dev_key_seed(is_dev)?,
			tracing_targets: self.tracing_targets()?,
			tracing_receiver: self.tracing_receiver()?,
			chain_spec,
			max_runtime_instances,
			announce_block: self.announce_block()?,
			role,
		})
	}

	/// Get the filters for the logging.
	///
	/// This should be a list of comma-separated values.
	/// Example: `foo=trace,bar=debug,baz=info`
	///
	/// By default this is retrieved from `SharedParams`.
	fn log_filters(&self) -> Result<String> {
		Ok(self.shared_params().log_filters().join(","))
	}

	/// Initialize substrate. This must be done only once.
	///
	/// This method:
	///
	/// 1. Set the panic handler
	/// 2. Raise the FD limit
	/// 3. Initialize the logger
	fn init<C: SubstrateCli>(&self) -> Result<()> {
		let logger_pattern = self.log_filters()?;

		sp_panic_handler::set(C::support_url(), C::impl_version());

		fdlimit::raise_fd_limit();
		init_logger(&logger_pattern);

		Ok(())
	}
}

/// Generate a valid random name for the node
pub fn generate_node_name() -> String {
	loop {
		let node_name = Generator::with_naming(Name::Numbered)
			.next()
			.expect("RNG is available on all supported platforms; qed");
		let count = node_name.chars().count();

		if count < NODE_NAME_MAX_LENGTH {
			return node_name;
		}
	};
}
