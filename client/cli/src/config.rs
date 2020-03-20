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

use crate::error::Result;
use crate::SubstrateCLI;
use app_dirs::{AppDataType, AppInfo};
use names::{Generator, Name};
use sc_service::config::{
	Configuration, DatabaseConfig, ExecutionStrategies, ExtTransport, KeystoreConfig,
	NetworkConfiguration, NodeKeyConfig, PruningMode, Roles, TelemetryEndpoints,
	TransactionPoolOptions, WasmExecutionMethod,
};
use sc_service::{ChainSpec, ChainSpecExtension, RuntimeGenesis};
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
	/// Get the base path of the configuration (if any)
	fn get_base_path(&self) -> Result<Option<&PathBuf>>;

	/// Returns `true` if the node is for development or not
	fn get_is_dev(&self) -> Result<bool> {
		Ok(false)
	}

	/// Get the roles
	fn get_roles(&self, _is_dev: bool) -> Result<Roles> {
		Ok(Roles::FULL)
	}

	/// Get the transaction pool options
	fn get_transaction_pool(&self) -> Result<TransactionPoolOptions> {
		Ok(Default::default())
	}

	/// Get the network configuration
	fn get_network_config<G, E>(
		&self,
		_chain_spec: &ChainSpec<G, E>,
		_is_dev: bool,
		net_config_dir: &PathBuf,
		client_id: &str,
		node_name: &str,
		node_key: NodeKeyConfig,
	) -> Result<NetworkConfiguration>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		Ok(NetworkConfiguration::new(
			node_name,
			client_id,
			node_key,
			net_config_dir,
		))
	}

	/// Get the keystore configuration
	fn get_keystore_config(&self, _base_path: &PathBuf) -> Result<KeystoreConfig> {
		Ok(KeystoreConfig::InMemory)
	}

	/// Get the database cache size (None for default)
	fn get_database_cache_size(&self) -> Result<Option<usize>> {
		Ok(Default::default())
	}

	/// Get the database configuration
	fn get_database_config(
		&self,
		base_path: &PathBuf,
		cache_size: Option<usize>,
	) -> Result<DatabaseConfig>;

	/// Get the state cache size
	fn get_state_cache_size(&self) -> Result<usize> {
		Ok(Default::default())
	}

	/// Get the state cache child ratio (if any)
	fn get_state_cache_child_ratio(&self) -> Result<Option<usize>> {
		Ok(Default::default())
	}

	/// Get the pruning mode
	fn get_pruning(&self, _is_dev: bool, _roles: Roles) -> Result<PruningMode> {
		Ok(Default::default())
	}

	/// Get the chain spec
	fn get_chain_spec<C: SubstrateCLI<G, E>, G, E>(&self) -> Result<ChainSpec<G, E>>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension;

	/// Get the name of the node
	fn get_node_name(&self) -> Result<String> {
		Ok(generate_node_name())
	}

	/// Get the WASM execution method
	fn get_wasm_method(&self) -> Result<WasmExecutionMethod> {
		Ok(Default::default())
	}

	/// Get the execution strategies
	fn get_execution_strategies(&self, _is_dev: bool) -> Result<ExecutionStrategies> {
		Ok(Default::default())
	}

	/// Get the RPC HTTP address (`None` if disabled)
	fn get_rpc_http(&self) -> Result<Option<SocketAddr>> {
		Ok(Default::default())
	}

	/// Get the RPC websocket address (`None` if disabled)
	fn get_rpc_ws(&self) -> Result<Option<SocketAddr>> {
		Ok(Default::default())
	}

	/// Get the RPC websockets maximum connections (`None` if unlimited)
	fn get_rpc_ws_max_connections(&self) -> Result<Option<usize>> {
		Ok(Default::default())
	}

	/// Get the RPC cors (`None` if disabled)
	fn get_rpc_cors(&self, _is_dev: bool) -> Result<Option<Vec<String>>> {
		Ok(Some(Vec::new()))
	}

	/// Get the prometheus port (`None` if disabled)
	fn get_prometheus_port(&self) -> Result<Option<SocketAddr>> {
		Ok(Default::default())
	}

	/// Get the telemetry endpoints (if any)
	fn get_telemetry_endpoints<G, E>(
		&self,
		chain_spec: &ChainSpec<G, E>,
	) -> Result<Option<TelemetryEndpoints>> {
		Ok(chain_spec.telemetry_endpoints().clone())
	}

	/// Get the telemetry external transport
	fn get_telemetry_external_transport(&self) -> Result<Option<ExtTransport>> {
		Ok(Default::default())
	}

	/// Get the default value for heap pages
	fn get_default_heap_pages(&self) -> Result<Option<u64>> {
		Ok(Default::default())
	}

	/// Returns `Ok(true)` if offchain worker should be used
	fn get_offchain_worker(&self, _roles: Roles) -> Result<bool> {
		Ok(Default::default())
	}

	/// Get sentry mode (i.e. act as an authority but **never** actively participate)
	fn get_sentry_mode(&self) -> Result<bool> {
		Ok(Default::default())
	}

	/// Returns `Ok(true)` if authoring should be forced
	fn get_force_authoring(&self) -> Result<bool> {
		Ok(Default::default())
	}

	/// Returns `Ok(true)` if grandpa should be disabled
	fn get_disable_grandpa(&self) -> Result<bool> {
		Ok(Default::default())
	}

	/// Get the development key seed from the current object
	fn get_dev_key_seed(&self, _is_dev: bool) -> Result<Option<String>> {
		Ok(Default::default())
	}

	/// Get the tracing targets from the current object (if any)
	fn get_tracing_targets(&self) -> Result<Option<String>> {
		Ok(Default::default())
	}

	/// Get the TracingReceiver value from the current object
	fn get_tracing_receiver(&self) -> Result<sc_tracing::TracingReceiver> {
		Ok(Default::default())
	}

	/// Get the node key from the current object
	fn get_node_key(&self, _net_config_dir: &PathBuf) -> Result<NodeKeyConfig> {
		Ok(Default::default())
	}

	/// Create a Configuration object from the current object
	fn create_configuration<C: SubstrateCLI<G, E>, G, E>(
		&self,
		task_executor: Arc<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>) + Send + Sync>,
	) -> Result<Configuration<G, E>>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		let chain_spec = self.get_chain_spec::<C, G, E>()?;
		let is_dev = self.get_is_dev()?;
		let default_config_dir = app_dirs::get_app_root(
			AppDataType::UserData,
			&AppInfo {
				name: C::get_executable_name(),
				author: C::get_author(),
			},
		)
		.expect("app directories exist on all supported platforms; qed");
		let config_dir = self
			.get_base_path()?
			.unwrap_or(&default_config_dir)
			.join("chains")
			.join(chain_spec.id());
		let net_config_dir = config_dir.join(DEFAULT_NETWORK_CONFIG_PATH);
		let client_id = C::client_id();
		// TODO: this parameter is really optional, shouldn't we leave it to None?
		let database_cache_size = Some(self.get_database_cache_size()?.unwrap_or(32));
		let node_key = self.get_node_key(&net_config_dir)?;
		let roles = self.get_roles(is_dev)?;

		Ok(Configuration {
			impl_name: C::get_impl_name(),
			impl_version: C::get_impl_version(),
			roles,
			task_executor,
			transaction_pool: self.get_transaction_pool()?,
			network: self.get_network_config(
				&chain_spec,
				is_dev,
				&net_config_dir,
				client_id.as_str(),
				self.get_node_name()?.as_str(),
				node_key,
			)?,
			keystore: self.get_keystore_config(&config_dir)?,
			database: self.get_database_config(&config_dir, database_cache_size)?,
			state_cache_size: self.get_state_cache_size()?,
			state_cache_child_ratio: self.get_state_cache_child_ratio()?,
			pruning: self.get_pruning(is_dev, roles)?,
			wasm_method: self.get_wasm_method()?,
			execution_strategies: self.get_execution_strategies(is_dev)?,
			rpc_http: self.get_rpc_http()?,
			rpc_ws: self.get_rpc_ws()?,
			rpc_ws_max_connections: self.get_rpc_ws_max_connections()?,
			rpc_cors: self.get_rpc_cors(is_dev)?,
			prometheus_port: self.get_prometheus_port()?,
			telemetry_endpoints: self.get_telemetry_endpoints(&chain_spec)?,
			telemetry_external_transport: self.get_telemetry_external_transport()?,
			default_heap_pages: self.get_default_heap_pages()?,
			offchain_worker: self.get_offchain_worker(roles)?,
			sentry_mode: self.get_sentry_mode()?,
			force_authoring: self.get_force_authoring()?,
			disable_grandpa: self.get_disable_grandpa()?,
			dev_key_seed: self.get_dev_key_seed(is_dev)?,
			tracing_targets: self.get_tracing_targets()?,
			tracing_receiver: self.get_tracing_receiver()?,
			chain_spec,
		})
	}

	/// Initialize substrate. This must be done only once.
	///
	/// This method:
	///
	/// 1. Set the panic handler
	/// 2. Raise the FD limit
	/// 3. Initialize the logger
	fn init<C: SubstrateCLI<G, E>, G, E>(&self) -> Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension;
}

/// Generate a valid random name for the node
pub fn generate_node_name() -> String {
	let result = loop {
		let node_name = Generator::with_naming(Name::Numbered).next().unwrap();
		let count = node_name.chars().count();

		if count < NODE_NAME_MAX_LENGTH {
			break node_name;
		}
	};

	result
}
