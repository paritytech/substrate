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

use criterion::{black_box, criterion_group, criterion_main, measurement::WallTime, Criterion};
use rand::{distributions::Uniform, rngs::StdRng, Rng, SeedableRng};
use rayon::prelude::*;
use sc_client_api::{Backend as _, BlockImportOperation, NewBlockState, StateBackend};
use sc_client_db::{Backend, BlocksPruning, DatabaseSettings, DatabaseSource, PruningMode};
use sp_core::{twox_128, H256};
use sp_runtime::{
	testing::{Block as RawBlock, ExtrinsicWrapper, Header},
	StateVersion, Storage,
};
use std::{
	ffi::OsString,
	path::{Path, PathBuf},
	time::{Duration, Instant},
};
use tempfile::TempDir;

pub(crate) type Block = RawBlock<ExtrinsicWrapper<u64>>;

fn get_polkadot_storage_keys() -> Vec<Vec<u8>> {
	// This is a dump of all of the keys from Polkadot block
	// `ad2fedfc2e6da47289b41cc24617915d4bce0638ca41bd0c4e4864ebb869f2dd`.
	let compressed_blob = include_bytes!("keys.bin.zst");
	let blob = zstd::bulk::decompress(&compressed_blob[..], 153917787).unwrap();
	let keys: Vec<Vec<u8>> = codec::Decode::decode(&mut &blob[..]).unwrap();
	assert_eq!(keys.len(), 1872246);
	keys
}

fn get_account_keys_prefix() -> Vec<u8> {
	let mut prefix = Vec::new();
	prefix.extend(twox_128(b"System"));
	prefix.extend(twox_128(b"Account"));

	assert_eq!(
		prefix,
		[
			0x26, 0xaa, 0x39, 0x4e, 0xea, 0x56, 0x30, 0xe0, 0x7c, 0x48, 0xae, 0x0c, 0x95, 0x58,
			0xce, 0xf7, 0xb9, 0x9d, 0x88, 0x0e, 0xc6, 0x81, 0x79, 0x9c, 0x0c, 0xf3, 0x0e, 0x88,
			0x86, 0x37, 0x1d, 0xa9,
		]
	);

	prefix
}

fn get_account_keys(all_keys: &[Vec<u8>]) -> Vec<Vec<u8>> {
	let account_prefix = get_account_keys_prefix();
	let account_keys: Vec<_> = all_keys
		.iter()
		.filter(|key| key.starts_with(&account_prefix))
		.cloned()
		.collect();

	assert_eq!(account_keys.len(), 1158203);
	account_keys
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
enum CacheConfig {
	NoCache,
	WithCache,
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum BenchKind {
	Storage,
	StorageHash,
}

fn create_backend(config: CacheConfig, path: PathBuf) -> Backend<Block> {
	let trie_cache_maximum_size = match config {
		CacheConfig::WithCache => None,
		CacheConfig::NoCache => Some(2 * 1024 * 1024 * 1024),
	};

	let settings = DatabaseSettings {
		trie_cache_maximum_size,
		state_pruning: Some(PruningMode::ArchiveAll),
		source: DatabaseSource::ParityDb { path },
		blocks_pruning: BlocksPruning::KeepAll,
	};

	Backend::new(settings, 100).expect("Creates backend")
}

fn preload_files(root_path: &Path) -> Vec<(OsString, Vec<u8>)> {
	let mut out = Vec::new();
	for entry in std::fs::read_dir(root_path).unwrap() {
		let path = entry.unwrap().path();
		let filename = path.file_name().unwrap().to_os_string();
		let data = std::fs::read(path).unwrap();
		out.push((filename, data));
	}
	out
}

struct TemporaryBackend {
	backend: Backend<Block>,
	_temp_dir: TempDir,
}

impl std::ops::Deref for TemporaryBackend {
	type Target = Backend<Block>;
	fn deref(&self) -> &Self::Target {
		&self.backend
	}
}

impl TemporaryBackend {
	// This copies the database into another directory and creates a fresh backend using it.
	//
	// This ensures that we're guaranteed to start in exactly the same state for each benchmark run.
	//
	// On drop the copy will be automatically deleted.
	fn new(config: CacheConfig, files: &[(OsString, Vec<u8>)]) -> Self {
		let temp_dir =
			TempDir::new().expect("creating a new temporary dictionary should never fail");

		files.par_iter().for_each(|(filename, data)| {
			std::fs::write(temp_dir.path().join(filename), data).unwrap();
		});

		let backend = create_backend(config, temp_dir.path().to_owned());
		TemporaryBackend { backend, _temp_dir: temp_dir }
	}
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

	let tmpdir = TempDir::new().expect("Creates temporary directory");

	let block_hash = {
		let backend = create_backend(CacheConfig::NoCache, tmpdir.path().to_owned());
		insert_blocks(&backend, storage.clone())
	};

	// Let the backend fully deinitialize, since it's not synchronous.
	std::thread::sleep(Duration::from_millis(1000));

	// Load the whole database into memory so that we can quickly
	// write it back into the filesystem.
	let database_files = preload_files(&tmpdir.path());
	std::mem::drop(tmpdir);

	let run = |group: &mut criterion::BenchmarkGroup<WallTime>,
	           config: CacheConfig,
	           desc: &str,
	           keys: &[Vec<u8>],
	           repeat_shared: usize,
	           repeat_local: usize,
	           kind: BenchKind| {
		group.bench_function(desc, |b| {
			b.iter_custom(|iters| {
				let mut elapsed = Duration::ZERO;
				for _ in 0..iters {
					let backend = TemporaryBackend::new(config, &database_files);
					for _ in 0..repeat_shared {
						// This gets us a clear local cache (which will be merged into the shared
						// cache on drop).
						let state = backend.state_at(block_hash).expect("Creates state");

						let timestamp = Instant::now();
						for key in keys.iter().cycle().take(keys.len() * repeat_local) {
							match kind {
								BenchKind::Storage => {
									let _ = black_box(
										state.storage(&key).expect("Doesn't fail").unwrap(),
									);
								},
								BenchKind::StorageHash => {
									let _ = black_box(
										state.storage_hash(&key).expect("Doesn't fail").unwrap(),
									);
								},
							}
						}

						elapsed += timestamp.elapsed();
					}
				}

				elapsed
			})
		});
	};

	let sample_size = 10;

	// To make the invocations below readable.
	use BenchKind::*;
	use CacheConfig::*;

	// This tests iterating over the accounts with an empty shared cache.
	//
	// This will essentially achieve the best case of what the local cache alone can do
	// when iterating over unique values since only the very bottom of the trie will
	// have to be constantly fetched from storage In other words, all keys have the same prefix
	// since we're only reading keys from the same storage map, so mostly the same trie nodes
	// will be accessed for each value.
	let mut g = c.benchmark_group("Read 1000000 account keys");
	g.sample_size(sample_size);
	run(&mut g, WithCache, "with cache", &account_keys[..1000000], 1, 1, Storage);
	run(&mut g, NoCache, "without cache", &account_keys[..1000000], 1, 1, Storage);
	g.finish();

	// This tests iterating over random keys with an empty shared cache.
	//
	// This will essentially achieve the worst-ish case of what the local cache alone can do
	// when iterating over unique values since more than just the very bottom of the trie will
	// have to be constantly fetched from the storage In other words, keys will have different
	// prefixes so each read will most likely access access different trie nodes for each value.
	//
	// For example, let's assume that for the previous benchmark where we were reading from
	// the same storage map we were accessing these keys: (just an example; keys are not real)
	//
	//   ABCDEFX
	//   ABCDEFY
	//   ABCDEFZ
	//
	// As you can see the prefix is the same, so the nodes for `ABCDEF` will be cached, and only
	// the `X`, `Y` and `Z` will have to be fetched.
	//
	// Now here since the keys we are reading are random we'd most likely end up with something
	// like these: (again, just an example to illustrate the concept; keys are not real)
	//
	//   PHYGYEH
	//   DVQXLHK
	//   PHSBWOB
	//
	// It will still happen that keys will sometimes share a prefix, but it won't be all the time.
	//
	// Since most of the keys are account balance keys this will happen more often than not,
	// so this is technically not a true *the* worst case scenario, but the idea here is to
	// replicate an access pattern which could convieably happen in normal circumstances.
	let mut g = c.benchmark_group("Read 100000 shuffled keys");
	g.sample_size(sample_size);
	run(&mut g, WithCache, "with cache", &shuffled_keys[..100000], 1, 1, Storage);
	run(&mut g, NoCache, "without cache", &shuffled_keys[..100000], 1, 1, Storage);
	g.finish();

	// This tests iterating over random keys with a shared cache.
	//
	// The first iteration will be slow, but queries from any subsequent iterations will get
	// serviced by the shared cache speeding things up significantly, assuming a lot of the
	// nodes got cached in the shared cache.
	let mut g = c.benchmark_group("Read 100000 shuffled keys multiple times");
	g.sample_size(sample_size);
	run(&mut g, WithCache, "with cache", &shuffled_keys[..100000], 10, 1, Storage);
	run(&mut g, NoCache, "without cache", &shuffled_keys[..100000], 10, 1, Storage);
	g.finish();

	let mut g = c.benchmark_group("Read 10000 shuffled keys multiple times");
	g.sample_size(sample_size);
	run(&mut g, WithCache, "with cache", &shuffled_keys[..10000], 10, 1, Storage);
	run(&mut g, NoCache, "without cache", &shuffled_keys[..10000], 10, 1, Storage);
	g.finish();

	let mut g = c.benchmark_group("Read 1000 shuffled keys multiple times");
	g.sample_size(sample_size);
	run(&mut g, WithCache, "with cache", &shuffled_keys[..1000], 10, 1, Storage);
	run(&mut g, NoCache, "without cache", &shuffled_keys[..1000], 10, 1, Storage);
	g.finish();

	// Read a single value once. There should be no difference here between the cache and no cache
	// variants.
	let mut g = c.benchmark_group("Read a single value once");
	g.sample_size(100);
	run(&mut g, WithCache, "with cache", &all_keys[..1], 1, 1, Storage);
	run(&mut g, NoCache, "without cache", &all_keys[..1], 1, 1, Storage);
	g.finish();

	let mut g = c.benchmark_group("Read a single value 256k times");
	g.sample_size(sample_size);
	run(&mut g, WithCache, "with local cache", &all_keys[..1], 1, 262144, Storage);
	run(&mut g, WithCache, "with shared cache", &all_keys[..1], 262144, 1, Storage);
	run(&mut g, WithCache, "with local and shared cache", &all_keys[..1], 512, 512, Storage);
	run(&mut g, NoCache, "without cache", &all_keys[..1], 1, 262144, Storage);
	g.finish();

	let mut g = c.benchmark_group("Hash a single value once");
	g.sample_size(100);
	run(&mut g, WithCache, "with cache", &all_keys[..1], 1, 1, StorageHash);
	run(&mut g, NoCache, "without cache", &all_keys[..1], 1, 1, StorageHash);
	g.finish();

	let mut g = c.benchmark_group("Hash a single value 256k times");
	g.sample_size(sample_size);
	run(&mut g, WithCache, "with local cache", &all_keys[..1], 1, 262144, StorageHash);
	run(&mut g, WithCache, "with shared cache", &all_keys[..1], 262144, 1, StorageHash);
	run(&mut g, WithCache, "with local and shared cache", &all_keys[..1], 512, 512, StorageHash);
	run(&mut g, NoCache, "without cache", &all_keys[..1], 1, 262144, StorageHash);
	g.finish();

	let mut g = c.benchmark_group("Hash `:code`");
	let code_key = &[sp_core::storage::well_known_keys::CODE.to_vec()];
	g.sample_size(100);
	run(&mut g, WithCache, "with cache", &code_key[..], 1, 1, StorageHash);
	run(&mut g, NoCache, "without cache", &code_key[..], 1, 1, StorageHash);
	g.finish();
}

criterion_group!(benches, state_access_benchmarks);
criterion_main!(benches);
