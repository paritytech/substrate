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
	NetworkConfiguration, PruningMode, Roles, TransactionPoolOptions, WasmExecutionMethod,
};
use sc_service::{ChainSpec, ChainSpecExtension, RuntimeGenesis};
use sc_telemetry::TelemetryEndpoints;
use std::future::Future;
use std::net::SocketAddr;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::Arc;

/// The maximum number of characters for a node name.
pub(crate) const NODE_NAME_MAX_LENGTH: usize = 32;

// TODO: all getters should probably return a Result no matter what
pub trait CliConfiguration: Sized {
	fn get_base_path(&self) -> Option<&PathBuf>;
	fn get_is_dev(&self) -> bool;
	fn get_roles(&self) -> Roles {
		Roles::FULL
	}
	fn get_transaction_pool(&self) -> Result<TransactionPoolOptions> {
		Ok(Default::default())
	}
	fn get_network_config<G, E>(
		&self,
		_chain_spec: &ChainSpec<G, E>,
		_is_dev: bool,
		_base_path: &PathBuf,
		_client_id: &str,
	) -> Result<NetworkConfiguration>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		Ok(Default::default())
	}
	fn get_keystore_config(&self, base_path: &PathBuf) -> Result<KeystoreConfig>;
	fn get_database_cache_size(&self) -> Option<usize> { Default::default() }
	fn get_database_config(&self, base_path: &PathBuf, cache_size: Option<usize>) -> DatabaseConfig;
	fn get_state_cache_size(&self) -> usize {
		Default::default()
	}
	fn get_state_cache_child_ratio(&self) -> Option<usize> {
		Default::default()
	}
	fn get_pruning(&self, is_dev: bool) -> Result<PruningMode> {
		Ok(Default::default())
	}
	fn get_chain_spec<C: SubstrateCLI<G, E>, G, E>(&self) -> Result<ChainSpec<G, E>>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension;
	fn get_name(&self) -> Result<String> {
		Ok(generate_node_name())
	}
	fn get_wasm_method(&self) -> WasmExecutionMethod {
		WasmExecutionMethod::Interpreted
	}
	fn get_execution_strategies(&self, _is_dev: bool) -> Result<ExecutionStrategies> {
		Ok(Default::default())
	}
	fn get_rpc_http(&self) -> Result<Option<SocketAddr>> {
		Ok(Default::default())
	}
	fn get_rpc_ws(&self) -> Result<Option<SocketAddr>> {
		Ok(Default::default())
	}
	fn get_rpc_ws_max_connections(&self) -> Option<usize> {
		Default::default()
	}
	fn get_rpc_cors(&self, _is_dev: bool) -> Option<Vec<String>> {
		Some(Vec::new())
	}
	fn get_prometheus_port(&self) -> Result<Option<SocketAddr>> {
		Ok(Default::default())
	}
	fn get_telemetry_endpoints<G, E>(
		&self,
		chain_spec: &ChainSpec<G, E>,
	) -> Option<TelemetryEndpoints> {
		chain_spec.telemetry_endpoints().clone()
	}
	fn get_telemetry_external_transport(&self) -> Option<ExtTransport> {
		Default::default()
	}
	fn get_default_heap_pages(&self) -> Option<u64> {
		Default::default()
	}
	fn get_offchain_worker(&self) -> bool {
		Default::default()
	}

	/// set sentry mode (i.e. act as an authority but **never** actively participate)
	fn get_sentry_mode(&self) -> bool {
		Default::default()
	}

	fn get_force_authoring(&self) -> bool {
		Default::default()
	}
	fn get_disable_grandpa(&self) -> bool {
		Default::default()
	}
	fn get_dev_key_seed(&self, _is_dev: bool) -> Option<String> {
		Default::default()
	}
	fn get_tracing_targets(&self) -> Option<String> {
		Default::default()
	}
	fn get_tracing_receiver(&self) -> sc_tracing::TracingReceiver {
		Default::default()
	}

	fn create_configuration<C: SubstrateCLI<G, E>, G, E>(
		&self,
		task_executor: Arc<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>) + Send + Sync>,
	) -> Result<Configuration<G, E>>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		let chain_spec = self.get_chain_spec::<C, G, E>()?;
		let is_dev = self.get_is_dev(); // TODO: probably not a good thing to have this getter
		let default_config_dir = app_dirs::get_app_root(
			AppDataType::UserData,
			&AppInfo {
				name: C::get_executable_name(),
				author: C::get_author(),
			},
		)
		.expect("app directories exist on all supported platforms; qed");
		let config_dir = self.get_base_path().unwrap_or(&default_config_dir);
		let client_id = C::client_id();
		// TODO: this parameter is really optional, shouldn't we leave it to None?
		let database_cache_size = Some(self.get_database_cache_size().unwrap_or(1024));

		Ok(Configuration {
			impl_name: C::get_impl_name(),
			impl_version: C::get_impl_version(),
			roles: self.get_roles(),
			task_executor,
			transaction_pool: self.get_transaction_pool()?,
			network: self.get_network_config(
				&chain_spec,
				is_dev,
				&config_dir,
				client_id.as_str(),
			)?,
			keystore: self.get_keystore_config(config_dir)?,
			database: self.get_database_config(&config_dir, database_cache_size),
			state_cache_size: self.get_state_cache_size(),
			state_cache_child_ratio: self.get_state_cache_child_ratio(),
			pruning: self.get_pruning(is_dev)?,
			name: self.get_name()?,
			wasm_method: self.get_wasm_method(),
			execution_strategies: self.get_execution_strategies(is_dev)?,
			rpc_http: self.get_rpc_http()?,
			rpc_ws: self.get_rpc_ws()?,
			rpc_ws_max_connections: self.get_rpc_ws_max_connections(),
			rpc_cors: self.get_rpc_cors(is_dev),
			prometheus_port: self.get_prometheus_port()?,
			telemetry_endpoints: self.get_telemetry_endpoints(&chain_spec),
			telemetry_external_transport: self.get_telemetry_external_transport(),
			default_heap_pages: self.get_default_heap_pages(),
			offchain_worker: self.get_offchain_worker(),
			sentry_mode: self.get_sentry_mode(),
			force_authoring: self.get_force_authoring(),
			disable_grandpa: self.get_disable_grandpa(),
			dev_key_seed: self.get_dev_key_seed(is_dev),
			tracing_targets: self.get_tracing_targets(),
			tracing_receiver: self.get_tracing_receiver(),
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
