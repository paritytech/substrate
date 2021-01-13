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

use crate::ChainInfo;
use futures::{Sink, SinkExt};
use sc_client_api::execution_extensions::ExecutionStrategies;
use sc_executor::WasmExecutionMethod;
use sc_informant::OutputFormat;
use sc_network::{
	config::{NetworkConfiguration, TransportConfig},
	multiaddr,
};
use sc_service::config::KeystoreConfig;
use sc_service::{BasePath, Configuration, DatabaseConfig, Role, TaskExecutor};
use sp_keyring::Sr25519Keyring;
use std::fmt;
use std::io::Write;

/// Used to create `Configuration` object for the node.
pub fn config<Node>(task_executor: TaskExecutor) -> Configuration
where
	Node: ChainInfo,
{
	let mut chain_spec = Node::load_spec().expect("failed to load chain specification");
	let base_path = if let Some(base) = Node::base_path() {
		BasePath::new(base)
	} else {
		BasePath::new_temp_dir().expect("couldn't create a temp dir")
	};
	let root_path = base_path.path().to_path_buf().join("chains").join(chain_spec.id());

	let role = Role::Authority {
		sentry_nodes: Vec::new(),
	};
	let key_seed = Sr25519Keyring::Alice.to_seed();
	let storage = chain_spec
		.as_storage_builder()
		.build_storage()
		.expect("could not build storage");

	chain_spec.set_storage(storage);

	let mut network_config = NetworkConfiguration::new(
		format!("Test Node for: {}", key_seed),
		"network/test/0.1",
		Default::default(),
		None,
	);
	let informant_output_format = OutputFormat { enable_color: false };

	network_config.allow_non_globals_in_dht = true;

	network_config
		.listen_addresses
		.push(multiaddr::Protocol::Memory(rand::random()).into());

	network_config.transport = TransportConfig::MemoryOnly;

	Configuration {
		impl_name: "test-node".to_string(),
		impl_version: "0.1".to_string(),
		role,
		task_executor,
		transaction_pool: Default::default(),
		network: network_config,
		keystore: KeystoreConfig::Path {
			path: root_path.join("key"),
			password: None,
		},
		database: DatabaseConfig::RocksDb {
			path: root_path.join("db"),
			cache_size: 128,
		},
		state_cache_size: 16777216,
		state_cache_child_ratio: None,
		pruning: Default::default(),
		chain_spec,
		wasm_method: WasmExecutionMethod::Interpreted,
		// NOTE: we enforce the use of the wasm runtime to make use of the signature overrides
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
		prometheus_config: None,
		telemetry_endpoints: None,
		telemetry_external_transport: None,
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
	}
}

/// Builds the global logger.
pub fn logger<LogSink>(executor: tokio::runtime::Handle, log_sink: LogSink)
where
	LogSink: Sink<String> + Clone + Unpin + Send + Sync + 'static,
	LogSink::Error: Send + Sync + fmt::Debug,
{
	let ignore = [
		"yamux",
		"multistream_select",
		"libp2p",
		"jsonrpc_client_transports",
		"sc_network",
		"tokio_reactor",
		"parity-db",
		"sub-libp2p",
		"sync",
		"peerset",
		"ws",
		"sc_network",
		"sc_service",
		"sc_basic_authorship",
		"sc_peerset",
		"rpc",
	];
	let mut builder = env_logger::builder();
	builder.format(move |buf: &mut env_logger::fmt::Formatter, record: &log::Record| {
		let entry = format!("{} {} {}", record.level(), record.target(), record.args());
		let res = writeln!(buf, "{}", entry);

		let mut log_sink_clone = log_sink.clone();
		let _ = executor.spawn(async move {
			log_sink_clone.send(entry).await.expect("log_stream is dropped");
		});
		res
	});
	builder.write_style(env_logger::WriteStyle::Always);
	builder.filter_level(log::LevelFilter::Debug);
	builder.filter_module("runtime", log::LevelFilter::Trace);
	builder.filter_module("babe", log::LevelFilter::Info);
	builder.filter_module("sc_service", log::LevelFilter::Trace);
	for module in &ignore {
		builder.filter_module(module, log::LevelFilter::Info);
	}
	let _ = builder.is_test(true).try_init();
}
