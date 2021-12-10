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

use criterion::{criterion_group, criterion_main, BatchSize, Criterion, Throughput};

use node_cli::service::{create_extrinsic, FullClient};
use node_runtime::{constants::currency::*, BalancesCall};
use sc_block_builder::{BlockBuilderProvider, BuiltBlock, RecordProof};
use sc_client_api::execution_extensions::ExecutionStrategies;
use sc_consensus::{
	block_import::{BlockImportParams, ForkChoiceStrategy},
	BlockImport, StateAction,
};
use sc_service::{
	config::{
		DatabaseSource, KeepBlocks, KeystoreConfig, NetworkConfiguration, OffchainWorkerConfig,
		PruningMode, TransactionStorageMode, WasmExecutionMethod,
	},
	BasePath, Configuration, Role,
};
use sp_blockchain::{ApplyExtrinsicFailed::Validity, Error::ApplyExtrinsicFailed};
use sp_consensus::BlockOrigin;
use sp_keyring::Sr25519Keyring;
use sp_runtime::{
	generic::BlockId,
	transaction_validity::{InvalidTransaction, TransactionValidityError},
	AccountId32, MultiAddress, OpaqueExtrinsic,
};
use tokio::runtime::Handle;

fn new_node(tokio_handle: Handle) -> node_cli::service::NewFullBase {
	let base_path = BasePath::new_temp_dir()
		.expect("getting the base path of a temporary path doesn't fail; qed");
	let root = base_path.path().to_path_buf();

	let network_config = NetworkConfiguration::new(
		Sr25519Keyring::Alice.to_seed(),
		"network/test/0.1",
		Default::default(),
		None,
	);

	let spec = Box::new(node_cli::chain_spec::development_config());

	// NOTE: We enforce the use of the WASM runtime to benchmark block production using WASM.
	let execution_strategy = sc_client_api::ExecutionStrategy::AlwaysWasm;

	let config = Configuration {
		impl_name: "BenchmarkImpl".into(),
		impl_version: "1.0".into(),
		// We don't use the authority role since that would start producing blocks
		// in the background which would mess with our benchmark.
		role: Role::Full,
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
		wasm_method: WasmExecutionMethod::Compiled,
		execution_strategies: ExecutionStrategies {
			syncing: execution_strategy,
			importing: execution_strategy,
			block_construction: execution_strategy,
			offchain_worker: execution_strategy,
			other: execution_strategy,
		},
		rpc_http: None,
		rpc_ws: None,
		rpc_ipc: None,
		rpc_ws_max_connections: None,
		rpc_cors: None,
		rpc_methods: Default::default(),
		rpc_max_payload: None,
		ws_max_out_buffer_capacity: None,
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
		runtime_cache_size: 2,
		announce_block: true,
		base_path: Some(base_path),
		informant_output_format: Default::default(),
		wasm_runtime_overrides: None,
	};

	node_cli::service::new_full_base(config, |_, _| ()).expect("creating a full node doesn't fail")
}

fn extrinsic_set_time(now: u64) -> OpaqueExtrinsic {
	node_runtime::UncheckedExtrinsic {
		signature: None,
		function: node_runtime::Call::Timestamp(pallet_timestamp::Call::set { now }),
	}
	.into()
}

fn import_block(
	mut client: &FullClient,
	built: BuiltBlock<
		node_primitives::Block,
		<FullClient as sp_api::CallApiAt<node_primitives::Block>>::StateBackend,
	>,
) {
	let mut params = BlockImportParams::new(BlockOrigin::File, built.block.header);
	params.state_action =
		StateAction::ApplyChanges(sc_consensus::StorageChanges::Changes(built.storage_changes));
	params.fork_choice = Some(ForkChoiceStrategy::LongestChain);
	futures::executor::block_on(client.import_block(params, Default::default()))
		.expect("importing a block doesn't fail");
}

fn prepare_benchmark(client: &FullClient) -> (usize, Vec<OpaqueExtrinsic>) {
	const MINIMUM_PERIOD_FOR_BLOCKS: u64 = 1500;

	let mut max_transfer_count = 0;
	let mut extrinsics = Vec::new();
	let mut block_builder = client.new_block(Default::default()).unwrap();

	// Every block needs one timestamp extrinsic.
	let extrinsic_set_time = extrinsic_set_time(1 + MINIMUM_PERIOD_FOR_BLOCKS);
	block_builder.push(extrinsic_set_time.clone()).unwrap();
	extrinsics.push(extrinsic_set_time);

	// Creating those is surprisingly costly, so let's only do it once and later just `clone` them.
	let src = Sr25519Keyring::Alice.pair();
	let dst: MultiAddress<AccountId32, u32> = Sr25519Keyring::Bob.to_account_id().into();

	// Add as many tranfer extrinsics as possible into a single block.
	for nonce in 0.. {
		let extrinsic: OpaqueExtrinsic = create_extrinsic(
			client,
			src.clone(),
			BalancesCall::transfer { dest: dst.clone(), value: 1 * DOLLARS },
			Some(nonce),
		)
		.into();

		match block_builder.push(extrinsic.clone()) {
			Ok(_) => {},
			Err(ApplyExtrinsicFailed(Validity(TransactionValidityError::Invalid(
				InvalidTransaction::ExhaustsResources,
			)))) => break,
			Err(error) => panic!("{}", error),
		}

		extrinsics.push(extrinsic);
		max_transfer_count += 1;
	}

	(max_transfer_count, extrinsics)
}

fn block_production(c: &mut Criterion) {
	sp_tracing::try_init_simple();

	let runtime = tokio::runtime::Runtime::new().expect("creating tokio runtime doesn't fail; qed");
	let tokio_handle = runtime.handle().clone();

	let node = new_node(tokio_handle.clone());
	let client = &*node.client;

	// Buliding the very first block is around ~30x slower than any subsequent one,
	// so let's make sure it's built and imported before we benchmark anything.
	let mut block_builder = client.new_block(Default::default()).unwrap();
	block_builder.push(extrinsic_set_time(1)).unwrap();
	import_block(client, block_builder.build().unwrap());

	let (max_transfer_count, extrinsics) = prepare_benchmark(&client);
	log::info!("Maximum transfer count: {}", max_transfer_count);

	let mut group = c.benchmark_group("Block production");

	group.sample_size(10);
	group.throughput(Throughput::Elements(max_transfer_count as u64));

	let block_id = BlockId::Hash(client.chain_info().best_hash);

	group.bench_function(format!("{} transfers (no proof)", max_transfer_count), |b| {
		b.iter_batched(
			|| extrinsics.clone(),
			|extrinsics| {
				let mut block_builder =
					client.new_block_at(&block_id, Default::default(), RecordProof::No).unwrap();
				for extrinsic in extrinsics {
					block_builder.push(extrinsic).unwrap();
				}
				block_builder.build().unwrap()
			},
			BatchSize::SmallInput,
		)
	});

	group.bench_function(format!("{} transfers (with proof)", max_transfer_count), |b| {
		b.iter_batched(
			|| extrinsics.clone(),
			|extrinsics| {
				let mut block_builder =
					client.new_block_at(&block_id, Default::default(), RecordProof::Yes).unwrap();
				for extrinsic in extrinsics {
					block_builder.push(extrinsic).unwrap();
				}
				block_builder.build().unwrap()
			},
			BatchSize::SmallInput,
		)
	});
}

criterion_group!(benches, block_production);
criterion_main!(benches);
