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
//! some more or less full block.
//!
//! As we also want to protect against cold-cache attacks, this
//! benchmark should not rely on any caching (except those that
//! DO NOT depend on user input). Thus block generation should be
//! based on randomized operation.
//!
//! This is supposed to be very simple benchmark and is not subject
//! to much configuring - just block full of randomized transactions.
//! It is not supposed to measure runtime modules weight correctness

use std::{sync::Arc, path::Path, collections::BTreeMap};

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
	config = Criterion::default().sample_size(50).warm_up_time(std::time::Duration::from_secs(20));
	targets = bench_block_import
);
criterion_group!(
	name = profile;
	config = Criterion::default().sample_size(10);
	targets = profile_block_import
);
criterion_main!(benches, profile);

fn genesis(keyring: &BenchKeyring) -> node_runtime::GenesisConfig {
	node_testing::genesis::config_endowed(
		false,
		Some(node_runtime::WASM_BINARY),
		keyring.collect_account_ids(),
	)
}

// this is deterministic keyring of ordered accounts
//     //endowed-user//00
//     //endowed-user//01
//      ...
//     //endowed-user//N
#[derive(Clone)]
struct BenchKeyring {
	accounts: BTreeMap<AccountId, sr25519::Pair>,
}

// This is prepared database with genesis and keyring
// that can be cloned and then used for any benchmarking.
struct BenchDb {
	keyring: BenchKeyring,
	directory_guard: Guard,
}

impl Clone for BenchDb {
	fn clone(&self) -> Self {
		let keyring = self.keyring.clone();
		let dir = tempdir::TempDir::new("sub-bench").expect("temp dir creation failed");

		let seed_dir = self.directory_guard.0.path();

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

		BenchDb { keyring, directory_guard: Guard(dir) }
	}
}

impl BenchDb {
	fn new(keyring_length: usize) -> Self {
		let keyring = BenchKeyring::new(keyring_length);

		let dir = tempdir::TempDir::new("sub-bench").expect("temp dir creation failed");
		log::trace!(
			target: "bench-logistics",
			"Created seed db at {}",
			dir.path().to_string_lossy(),
		);
		let (_client, _backend) = bench_client(dir.path(), Profile::Native, &keyring);
		let directory_guard = Guard(dir);

		BenchDb { keyring, directory_guard }
	}

	fn generate_block(&mut self) -> Block {
		let (client, _backend) = bench_client(
			self.directory_guard.path(),
			Profile::Wasm,
			&self.keyring,
		);

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
			.expect("Put timestamp failed");
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

		let mut iteration = 0;
		let start = std::time::Instant::now();
		for _ in 0..100 {

			let sender = self.keyring.at(iteration);
			let receiver = get_account_id_from_seed::<sr25519::Public>(
				&format!("random-user//{}", iteration)
			);

			let signed = self.keyring.sign(
				CheckedExtrinsic {
					signed: Some((sender, signed_extra(0, 1*DOLLARS))),
					function: Call::Balances(
						BalancesCall::transfer(
							pallet_indices::address::Address::Id(receiver),
							1*DOLLARS
						)
					),
				},
				version,
				genesis_hash,
			);

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
			iteration += 1;
		}
		let block = block.build().expect("Block build failed").block;

		log::info!(
			target: "bench-logistics",
			"Block construction: {:#?} ({} tx)",
			start.elapsed(), block.extrinsics.len()
		);

		block
	}

	fn path(&self) -> &Path {
		self.directory_guard.path()
	}

	fn create_context(&self, profile: Profile) -> BenchContext {
		let BenchDb { directory_guard, keyring } = self.clone();
		let (client, backend) = bench_client(directory_guard.path(), profile, &keyring);

		BenchContext {
			client, backend, db_guard: directory_guard,
		}
	}
}

impl BenchKeyring {
	// `length` is the number of random accounts generated.
	fn new(length: usize) -> Self {
		let mut accounts = BTreeMap::new();

		for n in 0..length {
			let seed = format!("//endowed-user/{}", n);
			let pair = sr25519::Pair::from_string(&seed, None).expect("failed to generate pair");
			let account_id = AccountPublic::from(pair.public()).into_account();
			accounts.insert(account_id, pair);
		}

		Self { accounts }
	}

	fn collect_account_ids(&self) -> Vec<AccountId> {
		self.accounts.keys().cloned().collect()
	}

	fn at(&self, index: usize) -> AccountId {
		self.accounts.keys().nth(index).expect("Failed to get account").clone()
	}

	fn sign(&self, xt: CheckedExtrinsic, version: u32, genesis_hash: [u8; 32]) -> UncheckedExtrinsic {
		match xt.signed {
			Some((signed, extra)) => {
				let payload = (xt.function, extra.clone(), version, genesis_hash, genesis_hash);
				let key = self.accounts.get(&signed).expect("Account id not found in keyring");
				let signature = payload.using_encoded(|b| {
					if b.len() > 256 {
						key.sign(&sp_io::hashing::blake2_256(b))
					} else {
						key.sign(b)
					}
				}).into();
				UncheckedExtrinsic {
					signature: Some((pallet_indices::address::Address::Id(signed), signature, extra)),
					function: payload.0,
				}
			}
			None => UncheckedExtrinsic {
				signature: None,
				function: xt.function,
			},
		}
	}
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
// - This client should use best wasm execution method.
// - This client should work with real database only.
fn bench_client(dir: &std::path::Path, profile: Profile, keyring: &BenchKeyring) -> (Client, std::sync::Arc<Backend>) {
	let db_config = sc_client_db::DatabaseSettings {
		state_cache_size: 16*1024*1024,
		state_cache_child_ratio: Some((0, 100)),
		pruning: PruningMode::ArchiveAll,
		source: sc_client_db::DatabaseSettingsSrc::Path {
			path: dir.into(),
			cache_size: None,
		},
	};

	let (client, backend) = sc_client_db::new_client(
		db_config,
		NativeExecutor::new(WasmExecutionMethod::Compiled, None),
		&genesis(keyring),
		None,
		None,
		ExecutionExtensions::new(profile.into_execution_strategies(), None),
	).expect("Should not fail");

	(client, backend)
}

struct Guard(tempdir::TempDir);

impl Guard {
	fn path(&self) -> &Path {
		self.0.path()
	}
}

struct BenchContext {
	client: Client,
	backend: Arc<Backend>,
	db_guard: Guard,
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

// Import generated block.
fn import_block(client: &mut Client, block: Block) {
	let mut import_params = BlockImportParams::new(BlockOrigin::NetworkBroadcast, block.header.clone());
	import_params.body = Some(block.extrinsics().to_vec());
	import_params.fork_choice = Some(ForkChoiceStrategy::LongestChain);

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

	let mut bench_db = BenchDb::new(128);
	let block = bench_db.generate_block();

	log::trace!(
		target: "bench-logistics",
		"Seed database directory: {}",
		bench_db.path().display(),
	);

	c.bench_function_over_inputs("import block",
		move |bencher, profile| {
			bencher.iter_batched(
				|| {
					let context = bench_db.create_context(*profile);

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
					);
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

	let mut bench_db = BenchDb::new(128);
	let block = bench_db.generate_block();

	c.bench_function("profile block",
		move |bencher| {
			bencher.iter_batched(
				|| {
					bench_db.create_context(Profile::Native)
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
