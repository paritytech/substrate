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
use sc_client_db::{
	Backend, DatabaseSettings, DatabaseSource, KeepBlocks, PruningMode, TransactionStorageMode,
};
use sp_core::H256;
use sp_runtime::{
	generic::BlockId,
	testing::{Block as RawBlock, ExtrinsicWrapper, Header},
	Storage,
};
use std::path::PathBuf;
use tempfile::TempDir;

pub(crate) type Block = RawBlock<ExtrinsicWrapper<u64>>;

fn insert_block(db: &Backend<Block>, storage: Vec<(Vec<u8>, Vec<u8>)>) -> H256 {
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
			Storage { top: storage.into_iter().collect(), children_default: Default::default() },
			true,
		)
		.unwrap();

	op.set_block_data(header.clone(), Some(vec![]), None, None, NewBlockState::Best)
		.unwrap();

	db.commit_operation(op).unwrap();

	let mut op = db.begin_operation().unwrap();
	let mut header = Header {
		number: 1,
		parent_hash: Default::default(),
		state_root: Default::default(),
		digest: Default::default(),
		extrinsics_root: Default::default(),
	};

	header.state_root = db.state_at(BlockId::Number(0)).unwrap().storage_root(std::iter::empty()).0;

	op.set_block_data(header.clone(), Some(vec![]), None, None, NewBlockState::Best)
		.unwrap();

	db.commit_operation(op).unwrap();

	header.hash()
}

fn create_backend(cache_size: usize, path: PathBuf) -> Backend<Block> {
	let settings = DatabaseSettings {
		state_cache_size: cache_size,
		state_cache_child_ratio: None,
		state_pruning: PruningMode::ArchiveAll,
		source: DatabaseSource::ParityDb { path },
		keep_blocks: KeepBlocks::All,
		transaction_storage: TransactionStorageMode::BlockBody,
	};

	Backend::new(settings, 10).expect("Creates backend")
}

fn state_access_benchmarks(c: &mut Criterion) {
	sp_tracing::try_init_simple();

	let mut group = c.benchmark_group("State access");

	let path = TempDir::new().expect("Creates temporary directory");

	let backend = create_backend(0, path.path().to_owned());

	let mut rng = StdRng::seed_from_u64(353893213);

	let mut storage = Vec::new();
	let mut keys = Vec::new();

	for _ in 0..1_000_000 {
		let key_len: usize = rng.gen_range(32..128);
		let key = (&mut rng)
			.sample_iter(Uniform::new_inclusive(0, 255))
			.take(key_len)
			.collect::<Vec<u8>>();

		let value_len: usize = rng.gen_range(20..60);
		let value = (&mut rng)
			.sample_iter(Uniform::new_inclusive(0, 255))
			.take(value_len)
			.collect::<Vec<u8>>();

		keys.push(key.clone());
		storage.push((key, value));
	}

	let block_hash = insert_block(&backend, storage);

	group.sample_size(10);

	drop(backend);

	let backend = create_backend(128 * 1024 * 1024, path.path().to_owned());

	group.bench_function("with 128MB cache", |b| {
		b.iter_batched(
			|| backend.state_at(BlockId::Hash(block_hash)).expect("Creates state"),
			|state| {
				for key in &keys {
					let _ = state.storage(&key).expect("Doesn't fail");
				}
			},
			BatchSize::SmallInput,
		)
	});

	drop(backend);

	let backend = create_backend(0, path.path().to_owned());

	group.bench_function("with cache disabled", |b| {
		b.iter_batched(
			|| backend.state_at(BlockId::Hash(block_hash)).expect("Creates state"),
			|state| {
				for key in &keys {
					let _ = state.storage(&key).expect("Doesn't fail");
				}
			},
			BatchSize::SmallInput,
		)
	});
}

criterion_group!(benches, state_access_benchmarks);
criterion_main!(benches);
