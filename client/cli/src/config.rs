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

use std::sync::Arc;
use std::pin::Pin;
use std::future::Future;
use std::net::SocketAddr;
use sc_service::config::{
	Configuration, TransactionPoolOptions, DatabaseConfig, KeystoreConfig, PruningMode,
	ExtTransport, NetworkConfiguration, Roles, WasmExecutionMethod, ExecutionStrategies,
};
use sc_service::{ChainSpec, RuntimeGenesis, ChainSpecExtension};
use sc_telemetry::TelemetryEndpoints;
use crate::SubstrateCLI;

pub trait IntoConfiguration<G, E, S>: Sized
where
	G: RuntimeGenesis,
	E: ChainSpecExtension,
	S: SubstrateCLI<G, E>,
{
	fn get_impl_name(&self) -> &'static str { V::impl_name() }
	fn get_impl_version(&self) -> &'static str { V::impl_version() }
	fn get_impl_commit(&self) -> &'static str { V::impl_commit() }
	fn get_roles(&self) -> Roles { Roles::FULL }
	fn get_task_executor(&self) -> Arc<dyn Fn(Pin<Box<dyn Future<Output = ()> + Send>>) + Send + Sync>;
	fn get_transaction_pool(&self) -> TransactionPoolOptions { Default::default() }
	fn get_network(&self) -> NetworkConfiguration;
	fn get_keystore(&self) -> KeystoreConfig;
	fn get_database(&self) -> DatabaseConfig;
	fn get_state_cache_size(&self) -> usize { Default::default() }
	fn get_state_cache_child_ratio(&self) -> Option<usize> { Default::default() }
	fn get_pruning(&self) -> PruningMode { Default::default() }
	fn get_chain_spec(&self) -> ChainSpec<G, E>;
	fn get_name(&self) -> String { Default::default() }
	fn get_wasm_method(&self) -> WasmExecutionMethod { WasmExecutionMethod::Interpreted }
	fn get_execution_strategies(&self) -> ExecutionStrategies { Default::default() }
	fn get_rpc_http(&self) -> Option<SocketAddr> { Default::default() }
	fn get_rpc_ws(&self) -> Option<SocketAddr> { Default::default() }
	fn get_rpc_ws_max_connections(&self) -> Option<usize> { Default::default() }
	fn get_rpc_cors(&self) -> Option<Vec<String>> { Some(Vec::new()) }
	fn get_prometheus_port(&self) -> Option<SocketAddr> { Default::default() }
	fn get_telemetry_endpoints(&self) -> Option<TelemetryEndpoints> { Default::default() }
	fn get_telemetry_external_transport(&self) -> Option<ExtTransport> { Default::default() }
	fn get_default_heap_pages(&self) -> Option<u64> { Default::default() }
	fn get_offchain_worker(&self) -> bool { Default::default() }
	fn get_sentry_mode(&self) -> bool { Default::default() }
	fn get_force_authoring(&self) -> bool { Default::default() }
	fn get_disable_grandpa(&self) -> bool { Default::default() }
	fn get_dev_key_seed(&self) -> Option<String> { Default::default() }
	fn get_tracing_targets(&self) -> Option<String> { Default::default() }
	fn get_tracing_receiver(&self) -> sc_tracing::TracingReceiver { Default::default() }

	fn into_configuration(self) -> Configuration<G, E> {
		Configuration {
			impl_name: self.get_impl_name(),
			impl_version: self.get_impl_version(),
			impl_commit: self.get_impl_commit(),
			roles: self.get_roles(),
			task_executor: self.get_task_executor(),
			transaction_pool: self.get_transaction_pool(),
			network: self.get_network(),
			keystore: self.get_keystore(),
			database: self.get_database(),
			state_cache_size: self.get_state_cache_size(),
			state_cache_child_ratio: self.get_state_cache_child_ratio(),
			pruning: self.get_pruning(),
			chain_spec: self.get_chain_spec(),
			name: self.get_name(),
			wasm_method: self.get_wasm_method(),
			execution_strategies: self.get_execution_strategies(),
			rpc_http: self.get_rpc_http(),
			rpc_ws: self.get_rpc_ws(),
			rpc_ws_max_connections: self.get_rpc_ws_max_connections(),
			rpc_cors: self.get_rpc_cors(),
			prometheus_port: self.get_prometheus_port(),
			telemetry_endpoints: self.get_telemetry_endpoints(),
			telemetry_external_transport: self.get_telemetry_external_transport(),
			default_heap_pages: self.get_default_heap_pages(),
			offchain_worker: self.get_offchain_worker(),
			sentry_mode: self.get_sentry_mode(),
			force_authoring: self.get_force_authoring(),
			disable_grandpa: self.get_disable_grandpa(),
			dev_key_seed: self.get_dev_key_seed(),
			tracing_targets: self.get_tracing_targets(),
			tracing_receiver: self.get_tracing_receiver(),
		}
	}
}
