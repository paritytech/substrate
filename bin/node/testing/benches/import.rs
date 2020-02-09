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

//! Block import benchmark.
//!
//! This benchmark is expected to measure block import operation of
//! some full block.
//!
//! As we also want to protect against cold-cache attacks, this
//! benchmark should not rely on any caching - database or otherwise
//! (except those that DO NOT depend on user input).
//!
//! This is why we populate block with transactions to random accounts
//! and set state_cache_size to 0.
//!
//! This is supposed to be very simple benchmark and is not subject
//! to much configuring - just block full of randomized transactions.
//! It is not supposed to measure runtime modules weight correctness
//! (there is a dedicated benchmarking mode for this).

use std::{sync::Arc, path::Path};

use node_primitives::Block;
use node_testing::client::{Client, Backend};
use node_testing::keyring::*;
use sc_client_db::PruningMode;
use sc_executor::{NativeExecutor, WasmExecutionMethod};
use sp_consensus::{
	BlockOrigin, BlockImport, BlockImportParams,
	ForkChoiceStrategy, ImportResult, ImportedAux
};
use sp_runtime::{
	generic::BlockId,
	OpaqueExtrinsic,
	traits::{Block as BlockT, Verify, Zero, IdentifyAccount},
};
use codec::{Decode, Encode};
use node_runtime::{
	Call,
	CheckedExtrinsic,
	constants::currency::DOLLARS,
	UncheckedExtrinsic,
	MinimumPeriod,
	BalancesCall,
	AccountId,
	Signature,
};
use sp_core::ExecutionContext;
use sp_api::ProvideRuntimeApi;
use sp_block_builder::BlockBuilder;
use sp_inherents::InherentData;
use sc_client_api::{
	Backend as _, ExecutionStrategy,
	execution_extensions::{ExecutionExtensions, ExecutionStrategies},
};
use sp_core::{Pair, Public, sr25519};

use criterion::{Criterion, criterion_group, criterion_main};

criterion_group!(
	name = benches;
	config = Criterion::default().sample_size(10);
	targets = bench_block_import
);
criterion_group!(
	name = profile;
	config = Criterion::default().sample_size(10);
	targets = profile_block_import
);
criterion_main!(benches, profile);

fn genesis() -> node_runtime::GenesisConfig {
	node_testing::genesis::config(false, Some(node_runtime::WASM_BINARY))
}

fn sign(xt: CheckedExtrinsic, genesis_hash: [u8; 32], version: u32) -> UncheckedExtrinsic {
	node_testing::keyring::sign(xt, version, genesis_hash)
}

#[derive(Clone, Copy, Debug)]
enum Profile {
	Native,
	Wasm,
}

impl Profile {
	fn into_execution_strategies(self) -> ExecutionStrategies {
		match self {
			Profile::Wasm => ExecutionStrategies {
				syncing: ExecutionStrategy::AlwaysWasm,
				importing: ExecutionStrategy::AlwaysWasm,
				block_construction: ExecutionStrategy::AlwaysWasm,
				offchain_worker: ExecutionStrategy::AlwaysWasm,
				other: ExecutionStrategy::AlwaysWasm,
			},
			Profile::Native => ExecutionStrategies {
				syncing: ExecutionStrategy::NativeElseWasm,
				importing: ExecutionStrategy::NativeElseWasm,
				block_construction: ExecutionStrategy::NativeElseWasm,
				offchain_worker: ExecutionStrategy::NativeElseWasm,
				other: ExecutionStrategy::NativeElseWasm,
			}
		}
	}
}

// This should return client that is doing everything that full node
// is doing.
//
// - This client should not cache anything.
//     (TODO: configure zero rocksdb block cache)
// - This client should use best wasm execution method.
// - This client should work with real database only.
fn bench_client(dir: &std::path::Path, profile: Profile) -> (Client, std::sync::Arc<Backend>) {
	let db_config = sc_client_db::DatabaseSettings {
		state_cache_size: 0,
		state_cache_child_ratio: Some((0, 100)),
		pruning: PruningMode::ArchiveAll,
		source: sc_client_db::DatabaseSettingsSrc::Path {
			path: dir.into(),
			cache_size: Some(0),
		},
	};

	let (client, backend) = sc_client_db::new_client(
		db_config,
		NativeExecutor::new(WasmExecutionMethod::Compiled, None),
		&genesis(),
		None,
		None,
		ExecutionExtensions::new(profile.into_execution_strategies(), None),
	).expect("Should not fail");

	(client, backend)
}

struct Guard(tempdir::TempDir);

struct BenchContext {
	client: Client,
	backend: Arc<Backend>,
	db_guard: Guard,
}

impl BenchContext {
	fn new(profile: Profile) -> BenchContext {

		let dir = tempdir::TempDir::new("sub-bench").expect("temp dir creation failed");
		log::trace!(
			target: "bench-logistics",
			"Created seed db at {}",
			dir.path().to_string_lossy(),
		);
		let (client, backend) = bench_client(dir.path(), profile);
		let db_guard = Guard(dir);

		BenchContext { client, backend, db_guard }
	}

	fn new_from_seed(profile: Profile, seed_dir: &Path) -> BenchContext {
		let dir = tempdir::TempDir::new("sub-bench").expect("temp dir creation failed");

		log::trace!(
			target: "bench-logistics",
			"Copying seed db from {} to {}",
			seed_dir.to_string_lossy(),
			dir.path().to_string_lossy(),
		);
		let seed_db_files = std::fs::read_dir(seed_dir)
			.expect("failed to list file in seed dir")
			.map(|f_result|
				f_result.expect("failed to read file in seed db")
					.path()
					.clone()
			).collect();
		fs_extra::copy_items(
			&seed_db_files,
			dir.path(),
			&fs_extra::dir::CopyOptions::new(),
		).expect("Copy of seed database is ok");

		let (client, backend) = bench_client(dir.path(), profile);
		let db_guard = Guard(dir);

		BenchContext { client, backend, db_guard }
	}

	fn keep_db(self) -> Guard {
		self.db_guard
	}
}

type AccountPublic = <Signature as Verify>::Signer;

pub fn get_from_seed<TPublic: Public>(seed: &str) -> <TPublic::Pair as Pair>::Public {
	TPublic::Pair::from_string(&format!("//{}", seed), None)
		.expect("static values are valid; qed")
		.public()
}

pub fn get_account_id_from_seed<TPublic: Public>(seed: &str) -> AccountId
where
	AccountPublic: From<<TPublic::Pair as Pair>::Public>
{
	AccountPublic::from(get_from_seed::<TPublic>(seed)).into_account()
}

// Full block generation.
fn generate_block_import(client: &Client) -> Block {
	let version = client.runtime_version_at(&BlockId::number(0))
		.expect("There should be runtime version at 0")
		.spec_version;
	let genesis_hash = client.block_hash(Zero::zero())
		.expect("Database error?")
		.expect("Genesis block always exists; qed")
		.into();

	let mut block = client
		.new_block(Default::default())
		.expect("Block creation failed");

	let timestamp = 1 * MinimumPeriod::get();

	let mut inherent_data = InherentData::new();
	inherent_data.put_data(sp_timestamp::INHERENT_IDENTIFIER, &timestamp)
		.expect("Put timestamb failed");
	inherent_data.put_data(sp_finality_tracker::INHERENT_IDENTIFIER, &0)
		.expect("Put finality tracker failed");

	for extrinsic in client.runtime_api()
		.inherent_extrinsics_with_context(
			&BlockId::number(0),
			ExecutionContext::BlockConstruction,
			inherent_data,
		).expect("Get inherents failed")
	{
		block.push(extrinsic).expect("Push inherent failed");
	}

	let mut nonce = 0u32;
	let start = std::time::Instant::now();
	loop {
		let signed = sign(
			CheckedExtrinsic {
				signed: Some((charlie(), signed_extra(nonce, 1*DOLLARS))),
				function: Call::Balances(
					BalancesCall::transfer(
						pallet_indices::address::Address::Id(
							get_account_id_from_seed::<sr25519::Public>(&format!("user//{}", nonce))
						),
						1*DOLLARS
					)
				),
			}, genesis_hash, version);
		let encoded = Encode::encode(&signed);

		let opaque = OpaqueExtrinsic::decode(&mut &encoded[..])
			.expect("Failed  to decode opaque");

		match block.push(opaque) {
			Err(sp_blockchain::Error::ApplyExtrinsicFailed(
					sp_blockchain::ApplyExtrinsicFailed::Validity(e)
			)) if e.exhausted_resources() => {
				break;
			},
			Err(err) => panic!("Error pushing transaction: {:?}", err),
			Ok(_) => {},
		}
		nonce += 1;
	}
	let block = block.build().expect("Block build failed").block;

	log::info!(
		target: "bench-logistics",
		"Block construction: {:#?} ({} tx)",
		start.elapsed(), block.extrinsics.len()
	);

	block
}

// Import generated block.
fn import_block(client: &mut Client, block: Block) {
	let import_params = BlockImportParams {
		origin: BlockOrigin::NetworkBroadcast,
		header: block.header().clone(),
		post_digests: Default::default(),
		body: Some(block.extrinsics().to_vec()),
		storage_changes: Default::default(),
		finalized: false,
		justification: Default::default(),
		auxiliary: Default::default(),
		intermediates: Default::default(),
		fork_choice: Some(ForkChoiceStrategy::LongestChain),
		allow_missing_state: false,
		import_existing: false,
	};

	assert_eq!(client.chain_info().best_number, 0);

	assert_eq!(
		client.import_block(import_params, Default::default())
			.expect("Failed to import block"),
		ImportResult::Imported(
			ImportedAux {
				header_only: false,
				clear_justification_requests: false,
				needs_justification: false,
				bad_justification: false,
				needs_finality_proof: false,
				is_new_best: true,
			}
		)
	);

	assert_eq!(client.chain_info().best_number, 1);
}

fn bench_block_import(c: &mut Criterion) {
	sc_cli::init_logger("");
	// for future uses, uncomment if something wrong.
	// sc_cli::init_logger("sc_client=debug");

	let (block, guard) = {
		let context = BenchContext::new(Profile::Wasm);
		let block = generate_block_import(&context.client);
		(block, context.keep_db())
	};

	log::trace!(
		target: "bench-logistics",
		"Seed database directory: {}",
		guard.0.path().to_string_lossy(),
	);

	c.bench_function_over_inputs("import block",
		move |bencher, profile| {
			bencher.iter_batched(
				|| {
					let context = BenchContext::new_from_seed(
						*profile,
						guard.0.path(),
					);

					// mostly to just launch compiler before benching!
					let version = context.client.runtime_version_at(&BlockId::Number(0))
						.expect("Failed to get runtime version")
						.spec_version;

					log::trace!(
						target: "bench-logistics",
						"Next iteration database directory: {}, runtime version: {}",
						context.db_guard.0.path().to_string_lossy(), version,
					);

					context
				},
				|mut context| {
					let start = std::time::Instant::now();
					import_block(&mut context.client, block.clone());
					let elapsed = start.elapsed();

					log::info!(
						target: "bench-logistics",
						"imported block with {} tx, took: {:#?}",
						block.extrinsics.len(),
						elapsed,
					);

					log::info!(
						target: "bench-logistics",
						"usage info: {}",
						context.backend.usage_info()
							.expect("RocksDB backend always provides usage info!"),
					)
				},
				criterion::BatchSize::PerIteration,
			);
		},
		vec![Profile::Wasm, Profile::Native],
	);
}


// This is not an actual benchmark, so don't use it to measure anything.
//   It just produces special pattern of cpu load that allows easy picking
//   the part of block import for the profiling in the tool of choice.
fn profile_block_import(c: &mut Criterion) {
	sc_cli::init_logger("");

	let (block, guard) = {
		let context = BenchContext::new(Profile::Wasm);
		let block = generate_block_import(&context.client);
		(block, context.keep_db())
	};

	c.bench_function("profile block",
		move |bencher| {
			bencher.iter_batched(
				|| {
					let context = BenchContext::new_from_seed(
						Profile::Native,
						guard.0.path(),
					);
					context
				},
				|mut context| {
					// until better osx signpost/callgrind signal is possible to use
					// in rust, we just pause everything completely to help choosing
					// actual profiling interval
					std::thread::park_timeout(std::time::Duration::from_secs(2));
					import_block(&mut context.client, block.clone());
					// and here as well
					std::thread::park_timeout(std::time::Duration::from_secs(2));
					log::info!(
						target: "bench-logistics",
						"imported block, usage info: {}",
						context.backend.usage_info()
							.expect("RocksDB backend always provides usage info!"),
					)
				},
				criterion::BatchSize::PerIteration,
			);
		},
	);
}