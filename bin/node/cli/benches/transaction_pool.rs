// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use node_cli::service::{create_extrinsic, FullClient};
use node_runtime::{constants::currency::*, BalancesCall, SudoCall, UncheckedExtrinsic};
use sc_client_api::execution_extensions::ExecutionStrategies;
use sc_service::{
	config::{
		DatabaseSource, KeepBlocks, KeystoreConfig, MultiaddrWithPeerId, NetworkConfiguration,
		OffchainWorkerConfig, PruningMode, TransactionStorageMode, WasmExecutionMethod,
	},
	BasePath, ChainSpec, Configuration, Error as ServiceError, PartialComponents, Role,
	RpcHandlers, TFullBackend, TaskManager,
};
use sp_core::{crypto::Pair, sr25519};
use sp_keyring::Sr25519Keyring;
use std::sync::Arc;
use tokio::runtime::Handle;

fn new_node(tokio_handle: Handle) -> node_cli::service::NewFullBase {
	let base_path = BasePath::new_temp_dir().expect("Creates base path");
	let root = base_path.path().to_path_buf();

	let network_config = NetworkConfiguration::new(
		Sr25519Keyring::Alice.to_seed(),
		"network/test/0.1",
		Default::default(),
		None,
	);

	let spec = Box::new(node_cli::chain_spec::development_config());

	let config = Configuration {
		impl_name: "BenchmarkImpl".into(),
		impl_version: "1.0".into(),
		role: Role::Authority,
		tokio_handle,
		transaction_pool: Default::default(),
		network: network_config,
		keystore: KeystoreConfig::InMemory,
		keystore_remote: Default::default(),
		database: DatabaseSource::RocksDb { path: root.join("db"), cache_size: 128 },
		state_cache_size: 67108864,
		state_cache_child_ratio: None,
		state_pruning: PruningMode::ArchiveAll,
		keep_blocks: KeepBlocks::All,
		transaction_storage: TransactionStorageMode::BlockBody,
		chain_spec: spec,
		wasm_method: WasmExecutionMethod::Interpreted,
		// NOTE: we enforce the use of the native runtime to make the errors more debuggable
		execution_strategies: ExecutionStrategies {
			syncing: sc_client_api::ExecutionStrategy::NativeWhenPossible,
			importing: sc_client_api::ExecutionStrategy::NativeWhenPossible,
			block_construction: sc_client_api::ExecutionStrategy::NativeWhenPossible,
			offchain_worker: sc_client_api::ExecutionStrategy::NativeWhenPossible,
			other: sc_client_api::ExecutionStrategy::NativeWhenPossible,
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
		offchain_worker: OffchainWorkerConfig { enabled: true, indexing_enabled: false },
		force_authoring: false,
		disable_grandpa: false,
		dev_key_seed: Some(Sr25519Keyring::Alice.to_seed()),
		tracing_targets: None,
		tracing_receiver: Default::default(),
		max_runtime_instances: 8,
		announce_block: true,
		base_path: Some(base_path),
		informant_output_format: Default::default(),
		wasm_runtime_overrides: None,
		disable_log_reloading: false,
	};

	node_cli::service::new_full_base(config, |_, _| ()).expect("Creates node")
}

fn create_accounts(num: usize) -> Vec<sr25519::Pair> {
	(0..num)
		.map(|i| {
			Pair::from_string(&format!("{}/{}", Sr25519Keyring::Alice.to_seed(), i), None)
				.expect("Creates account pair")
		})
		.collect()
}

/// Create the extrinsics that will initialize the accounts from the sudo account (Alice).
///
/// `start_nonce` is the current nonce of Alice.
fn create_account_extrinsics(
	client: Arc<FullClient>,
	accounts: &[sr25519::Pair],
	start_nonce: u32,
) -> Vec<UncheckedExtrinsic> {
	accounts
		.iter()
		.enumerate()
		.map(|(i, a)| {
			create_extrinsic(
				client.clone(),
				Sr25519Keyring::Alice.pair(),
				SudoCall::sudo(Box::new(BalancesCall::set_balance(
					a.public().into(),
					1_000_000 * DOLLARS,
					0,
				))),
				Some(start_nonce + (i as u32)),
			)
		})
		.collect()
}

fn create_benchmark_extrinsics(
	client: Arc<FullClient>,
	accounts: &[sr25519::Pair],
	extrinsics_per_account: usize,
) -> Vec<UncheckedExtrinsic> {
	(0..extrinsics_per_account)
		.map(|nonce| {
			accounts.iter().map(|a| {
				create_extrinsic(
					client.clone(),
					a.clone(),
					BalancesCall::transfer(
						Sr25519Keyring::Bob.to_account_id(),
						1 * DOLLARS,
					),
					Some(nonce as u32),
				)
			})
		})
		.flatten()
		.collect()
}

fn transaction_pool_benchmarks(c: &mut Criterion) {
	let runtime = tokio::runtime::Runtime::new().expect("Creates tokio runtime");
	let tokio_handle = runtime.handle().clone();

	c.to_async(runtime)
}

criterion_group!(benches, transaction_pool_benchmarks);
criterion_main!(benches);
