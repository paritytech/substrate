// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use sc_client_api::execution_extensions::ExecutionStrategies;
use sc_executor::WasmExecutionMethod;
use sc_informant::OutputFormat;
use sc_network::{
	config::{NetworkConfiguration, Role, TransportConfig},
	multiaddr,
};
use sc_service::{
	config::KeystoreConfig, BasePath, ChainSpec, Configuration, DatabaseSource, KeepBlocks,
	TransactionStorageMode,
};
use sp_keyring::sr25519::Keyring::Alice;
use tokio::runtime::Handle;

pub use sc_cli::build_runtime;

/// Base db path gotten from env
pub fn base_path() -> BasePath {
	if let Some(base) = std::env::var("DB_BASE_PATH").ok() {
		BasePath::new(base)
	} else {
		BasePath::new_temp_dir().expect("couldn't create a temp dir")
	}
}

/// Produces a default configuration object, suitable for use with most set ups.
pub fn default_config(tokio_handle: Handle, mut chain_spec: Box<dyn ChainSpec>) -> Configuration {
	let base_path = base_path();
	let root_path = base_path.path().to_path_buf().join("chains").join(chain_spec.id());

	let storage = chain_spec
		.as_storage_builder()
		.build_storage()
		.expect("could not build storage");

	chain_spec.set_storage(storage);
	let key_seed = Alice.to_seed();

	let mut network_config = NetworkConfiguration::new(
		format!("Test Node for: {}", key_seed),
		"network/test/0.1",
		Default::default(),
		None,
	);
	let informant_output_format = OutputFormat { enable_color: false };
	network_config.allow_non_globals_in_dht = true;

	network_config.listen_addresses.push(multiaddr::Protocol::Memory(0).into());

	network_config.transport = TransportConfig::MemoryOnly;

	Configuration {
		impl_name: "test-node".to_string(),
		impl_version: "0.1".to_string(),
		role: Role::Authority,
		tokio_handle,
		transaction_pool: Default::default(),
		network: network_config,
		keystore: KeystoreConfig::Path { path: root_path.join("key"), password: None },
		database: DatabaseSource::RocksDb { path: root_path.join("db"), cache_size: 128 },
		state_cache_size: 16777216,
		state_cache_child_ratio: None,
		chain_spec,
		wasm_method: WasmExecutionMethod::Interpreted,
		execution_strategies: ExecutionStrategies {
			syncing: sc_client_api::ExecutionStrategy::AlwaysWasm,
			importing: sc_client_api::ExecutionStrategy::AlwaysWasm,
			block_construction: sc_client_api::ExecutionStrategy::AlwaysWasm,
			offchain_worker: sc_client_api::ExecutionStrategy::AlwaysWasm,
			other: sc_client_api::ExecutionStrategy::AlwaysWasm,
		},
		rpc_http: None,
		rpc_ws: None,
		rpc_ipc: None,
		rpc_ws_max_connections: None,
		rpc_cors: None,
		rpc_methods: Default::default(),
		rpc_max_payload: None,
		prometheus_config: None,
		telemetry_endpoints: None,
		default_heap_pages: None,
		offchain_worker: Default::default(),
		force_authoring: false,
		disable_grandpa: false,
		dev_key_seed: Some(key_seed),
		tracing_targets: None,
		tracing_receiver: Default::default(),
		max_runtime_instances: 8,
		announce_block: true,
		base_path: Some(base_path),
		wasm_runtime_overrides: None,
		informant_output_format,
		disable_log_reloading: false,
		keystore_remote: None,
		keep_blocks: KeepBlocks::All,
		state_pruning: Default::default(),
		transaction_storage: TransactionStorageMode::BlockBody,
	}
}
