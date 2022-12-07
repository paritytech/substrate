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

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use rand::{distributions::Uniform, rngs::StdRng, Rng, SeedableRng};
use sc_client_api::{Backend as _, BlockImportOperation, NewBlockState, StateBackend};
use sc_client_db::{Backend, BlocksPruning, DatabaseSettings, DatabaseSource, PruningMode};
use sp_core::H256;
use sp_runtime::{
	testing::{Block as RawBlock, ExtrinsicWrapper, Header},
	StateVersion, Storage,
};
use std::time::Duration;
use tempfile::TempDir;

pub(crate) type Block = RawBlock<ExtrinsicWrapper<u64>>;

fn get_polkadot_storage_keys() -> Vec<Vec<u8>> {
	// This is a dump of all of the keys from Polkadot block
	// `ad2fedfc2e6da47289b41cc24617915d4bce0638ca41bd0c4e4864ebb869f2dd`.
	let path: std::path::PathBuf = env!("CARGO_MANIFEST_DIR").into();
	let compressed_blob = std::fs::read(path.join("benches").join("keys.bin.zst")).unwrap();
	let blob = zstd::bulk::decompress(&compressed_blob, 153917787).unwrap();
	let keys: Vec<Vec<u8>> = codec::Decode::decode(&mut &blob[..]).unwrap();
	assert_eq!(keys.len(), 1872246);
	keys
}

fn get_account_keys(all_keys: &[Vec<u8>]) -> Vec<Vec<u8>> {
	let prefix = [
		0x26, 0xaa, 0x39, 0x4e, 0xea, 0x56, 0x30, 0xe0, 0x7c, 0x48, 0xae, 0x0c, 0x95, 0x58, 0xce,
		0xf7, 0xb9, 0x9d, 0x88, 0x0e, 0xc6, 0x81, 0x79, 0x9c, 0x0c, 0xf3, 0x0e, 0x88, 0x86, 0x37,
		0x1d, 0xa9,
	];
	all_keys.iter().filter(|key| key.starts_with(&prefix)).cloned().collect()
}

fn get_shuffled_keys(all_keys: &[Vec<u8>]) -> Vec<Vec<u8>> {
	use rand::seq::SliceRandom;
	let mut rng = StdRng::seed_from_u64(353893213);
	let mut keys = all_keys.to_vec();
	keys.shuffle(&mut rng);
	keys
}

fn insert_blocks(db: &Backend<Block>, storage: Vec<(Vec<u8>, Vec<u8>)>) -> H256 {
	let mut op = db.begin_operation().unwrap();
	let mut header = Header {
		number: 0,
		parent_hash: Default::default(),
		state_root: Default::default(),
		digest: Default::default(),
		extrinsics_root: Default::default(),
	};

	header.state_root = op
		.set_genesis_state(
			Storage {
				top: vec![(
					sp_core::storage::well_known_keys::CODE.to_vec(),
					kitchensink_runtime::wasm_binary_unwrap().to_vec(),
				)]
				.into_iter()
				.collect(),
				children_default: Default::default(),
			},
			true,
			StateVersion::V1,
		)
		.unwrap();

	op.set_block_data(header.clone(), Some(vec![]), None, None, NewBlockState::Best)
		.unwrap();

	db.commit_operation(op).unwrap();

	let mut number = 1;
	let mut parent_hash = header.hash();

	let mut keys_inserted = 0;
	while keys_inserted < storage.len() {
		let mut op = db.begin_operation().unwrap();

		db.begin_state_operation(&mut op, parent_hash).unwrap();

		let mut header = Header {
			number,
			parent_hash,
			state_root: Default::default(),
			digest: Default::default(),
			extrinsics_root: Default::default(),
		};

		let changes = storage
			.iter()
			.skip(keys_inserted)
			.take(100_000)
			.map(|(k, v)| (k.clone(), Some(v.clone())))
			.collect::<Vec<_>>();

		keys_inserted += changes.len();

		let (state_root, tx) = db.state_at(parent_hash).unwrap().storage_root(
			changes.iter().map(|(k, v)| (k.as_slice(), v.as_deref())),
			StateVersion::V1,
		);
		header.state_root = state_root;

		op.update_db_storage(tx).unwrap();
		op.update_storage(changes.clone(), Default::default()).unwrap();

		op.set_block_data(header.clone(), Some(vec![]), None, None, NewBlockState::Best)
			.unwrap();

		db.commit_operation(op).unwrap();

		number += 1;
		parent_hash = header.hash();
	}

	parent_hash
}

#[derive(Copy, Clone)]
enum BenchmarkConfig {
	NoCache,
	TrieNodeCache,
}

#[derive(Copy, Clone)]
enum AccessType {
	Storage,
	StorageHash,
}

fn create_backend(config: BenchmarkConfig, temp_dir: &TempDir) -> Backend<Block> {
	// To prevent a "Database file is in use" error, since backend's
	// deinitialization is not synchronous.
	//
	// Technically we could recreate everything for each benchmark,
	// but that takes forever as we'd have to repopulate the database
	// on disk from scratch every time. It's a lot faster if we just
	// wait for it to close and reopen it.
	std::thread::sleep(Duration::from_millis(1000));

	let path = temp_dir.path().to_owned();

	let trie_cache_maximum_size = match config {
		BenchmarkConfig::NoCache => None,
		BenchmarkConfig::TrieNodeCache => Some(2 * 1024 * 1024 * 1024),
	};

	let settings = DatabaseSettings {
		trie_cache_maximum_size,
		state_pruning: Some(PruningMode::ArchiveAll),
		source: DatabaseSource::ParityDb { path },
		blocks_pruning: BlocksPruning::KeepAll,
	};

	Backend::new(settings, 100).expect("Creates backend")
}

/// Generate the storage that will be used for the benchmark
///
/// Returns the `Vec<key>` and the `Vec<(key, value)>`
fn generate_storage() -> (Vec<Vec<u8>>, Vec<(Vec<u8>, Vec<u8>)>) {
	let mut rng = StdRng::seed_from_u64(353893213);

	let mut storage = Vec::new();
	let keys = get_polkadot_storage_keys();

	for key in &keys {
		if key == sp_core::storage::well_known_keys::CODE {
			continue
		}

		let value_len: usize = rng.gen_range(20..60);
		let value = (&mut rng)
			.sample_iter(Uniform::new_inclusive(0, 255))
			.take(value_len)
			.collect::<Vec<u8>>();

		storage.push((key.clone(), value));
	}

	(keys, storage)
}

fn state_access_benchmarks(c: &mut Criterion) {
	sp_tracing::try_init_simple();

	let (all_keys, storage) = generate_storage();
	let account_keys = get_account_keys(&all_keys);
	let shuffled_keys = get_shuffled_keys(&all_keys);

	let path = TempDir::new().expect("Creates temporary directory");

	let block_hash = {
		let backend = create_backend(BenchmarkConfig::NoCache, &path);
		insert_blocks(&backend, storage.clone())
	};

	let run_benchmark = |group: &mut criterion::BenchmarkGroup<
		criterion::measurement::WallTime,
	>,
	                     config: BenchmarkConfig,
	                     desc: &str,
	                     keys: &[Vec<u8>],
	                     repeat_shared: usize,
	                     repeat_local: usize,
	                     kind: AccessType| {
		group.bench_function(desc, |b| {
			if repeat_shared == 1 {
				b.iter_batched(
					|| {
						let backend = create_backend(config, &path);
						backend.state_at(block_hash).expect("Creates state")
					},
					|state| {
						for key in keys.iter().cycle().take(keys.len() * repeat_local) {
							match kind {
								AccessType::Storage => {
									let _ = state.storage(&key).expect("Doesn't fail").unwrap();
								},
								AccessType::StorageHash => {
									let _ =
										state.storage_hash(&key).expect("Doesn't fail").unwrap();
								},
							}
						}
					},
					BatchSize::SmallInput,
				)
			} else {
				b.iter_batched(
					|| create_backend(config, &path),
					|backend| {
						for _ in 0..repeat_shared {
							// This resets the local cache and merges it with the shared cache.
							let state = backend.state_at(block_hash).expect("Creates state");

							for key in keys.iter().cycle().take(keys.len() * repeat_local) {
								match kind {
									AccessType::Storage => {
										let _ = state.storage(&key).expect("Doesn't fail").unwrap();
									},
									AccessType::StorageHash => {
										let _ = state
											.storage_hash(&key)
											.expect("Doesn't fail")
											.unwrap();
									},
								}
							}
						}
					},
					BatchSize::SmallInput,
				)
			}
		});
	};

	let run_benchmark_with_and_without_cache =
		|mut group: criterion::BenchmarkGroup<criterion::measurement::WallTime>,
		 keys: &[Vec<u8>],
		 repeat_shared: usize,
		 repeat_local: usize,
		 kind: AccessType| {
			run_benchmark(
				&mut group,
				BenchmarkConfig::TrieNodeCache,
				"with trie node cache",
				&keys,
				repeat_shared,
				repeat_local,
				kind,
			);

			run_benchmark(
				&mut group,
				BenchmarkConfig::NoCache,
				"without cache",
				&keys,
				repeat_shared,
				repeat_local,
				kind,
			);
			group.finish();
		};

	// This tests iterating over the accounts with an empty shared cache.
	//
	// This will essentially achieve the best case of what the local cache alone can do
	// when iterating over unique values since only the very bottom of the trie will
	// have to be constantly fetched from storage (in other words, all keys have the same prefix).
	//
	// The time this takes is linear so there's not much point in going through more than this.
	let mut group = c.benchmark_group("Read 100000 account keys once");
	group.sample_size(10);
	group.measurement_time(Duration::from_secs(20));
	run_benchmark_with_and_without_cache(group, &account_keys[..100000], 1, 1, AccessType::Storage);

	// This tests iterating over random keys with an empty shared cache.
	//
	// This will essentially achieve the worst-ish case of what the local cache alone can do
	// when iterating over unique values since more than just the very bottom of the trie will
	// have to be constantly fetched from the storage (in other words, keys will have different
	// prefixes).
	let mut group = c.benchmark_group("Read 10000 shuffled keys once");
	group.sample_size(10);
	group.measurement_time(Duration::from_secs(15));
	run_benchmark_with_and_without_cache(group, &shuffled_keys[..10000], 1, 1, AccessType::Storage);

	// This tests iterating over random keys with a shared cache.
	//
	// The first iteration will be slow, but queries from any subsequent iterations will get
	// serviced by the shared cache speeding things up significantly.
	let mut group = c.benchmark_group("Read 10000 shuffled keys multiple times");
	group.sample_size(10);
	group.measurement_time(Duration::from_secs(30));
	run_benchmark_with_and_without_cache(
		group,
		&shuffled_keys[..10000],
		20,
		1,
		AccessType::Storage,
	);

	// Read a single value once. There should be no difference here between the cache and no cache
	// variants.
	let mut group = c.benchmark_group("Read a single value once");
	group.sample_size(20);
	group.measurement_time(Duration::from_secs(30));
	run_benchmark_with_and_without_cache(group, &all_keys[..1], 1, 1, AccessType::Storage);

	// Read a single value many times, with an empty shared cache but populated local cache (except
	// the first time).
	let mut group = c.benchmark_group("Read a single value 1024 times (local cache only)");
	group.sample_size(20);
	group.measurement_time(Duration::from_secs(30));
	run_benchmark_with_and_without_cache(group, &all_keys[..1], 1, 1024, AccessType::Storage);

	// Read a single value many times, with a populated shared cache but empty local cache (except
	// the first time).
	let mut group = c.benchmark_group("Read a single value 1024 times (shared cache only)");
	group.sample_size(20);
	group.measurement_time(Duration::from_secs(30));
	run_benchmark_with_and_without_cache(group, &all_keys[..1], 1024, 1, AccessType::Storage);

	// Read a single value many times, with a populated shared cache and populated local cache
	// (except the first time).
	let mut group = c.benchmark_group("Read a single value 1024 times (both caches)");
	group.sample_size(20);
	group.measurement_time(Duration::from_secs(30));
	run_benchmark_with_and_without_cache(group, &all_keys[..1], 32, 32, AccessType::Storage);

	let mut group = c.benchmark_group("Hash a value once");
	group.sample_size(20);
	group.measurement_time(Duration::from_secs(30));
	run_benchmark_with_and_without_cache(group, &all_keys[..1], 1, 1, AccessType::StorageHash);

	let mut group = c.benchmark_group("Hash a value 1024 times");
	group.sample_size(20);
	group.measurement_time(Duration::from_secs(30));
	run_benchmark_with_and_without_cache(group, &all_keys[..1], 1, 1024, AccessType::StorageHash);

	let mut group = c.benchmark_group("Hash `:code`");
	group.sample_size(20);
	group.measurement_time(Duration::from_secs(30));
	run_benchmark_with_and_without_cache(
		group,
		&[sp_core::storage::well_known_keys::CODE.to_vec()],
		1,
		1,
		AccessType::StorageHash,
	);
}

criterion_group!(benches, state_access_benchmarks);
criterion_main!(benches);
