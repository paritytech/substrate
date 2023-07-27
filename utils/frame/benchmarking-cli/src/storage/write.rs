// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use sc_cli::Result;
use sc_client_api::{Backend as ClientBackend, StorageProvider, UsageProvider};
use sc_client_db::{DbHash, DbState, DbStateBuilder};
use sp_api::StateBackend;
use sp_blockchain::HeaderBackend;
use sp_database::{ColumnId, Transaction};
use sp_runtime::traits::{Block as BlockT, HashingFor, Header as HeaderT};
use sp_trie::MemoryDB;

use log::{info, trace};
use rand::prelude::*;
use sp_storage::{ChildInfo, StateVersion};
use std::{
	fmt::Debug,
	sync::Arc,
	time::{Duration, Instant},
};

use super::cmd::StorageCmd;
use crate::shared::{new_rng, BenchRecord};

impl StorageCmd {
	/// Benchmarks the time it takes to write a single Storage item.
	/// Uses the latest state that is available for the given client.
	pub(crate) fn bench_write<Block, BA, H, C>(
		&self,
		client: Arc<C>,
		(db, state_col): (Arc<dyn sp_database::Database<DbHash>>, ColumnId),
		storage: sc_client_db::StorageDb<Block>,
	) -> Result<BenchRecord>
	where
		Block: BlockT<Header = H, Hash = DbHash> + Debug,
		H: HeaderT<Hash = DbHash>,
		BA: ClientBackend<Block>,
		C: UsageProvider<Block> + HeaderBackend<Block> + StorageProvider<Block, BA>,
	{
		// Store the time that it took to write each value.
		let mut record = BenchRecord::default();

		let best_hash = client.usage_info().chain.best_hash;
		let header = client.header(best_hash)?.ok_or("Header not found")?;
		let original_root = *header.state_root();
		let trie = DbStateBuilder::<Block>::new(Box::new(storage.clone()), original_root).build();

		info!("Preparing keys from block {}", best_hash);
		// Load all KV pairs and randomly shuffle them.
		let mut kvs: Vec<_> = trie.pairs(Default::default())?.collect();
		let (mut rng, _) = new_rng(None);
		kvs.shuffle(&mut rng);
		info!("Writing {} keys", kvs.len());

		let mut child_nodes = Vec::new();

		// Generate all random values first; Make sure there are no collisions with existing
		// db entries, so we can rollback all additions without corrupting existing entries.
		for key_value in kvs {
			let (k, original_v) = key_value?;
			match (self.params.include_child_trees, self.is_child_key(k.to_vec())) {
				(true, Some(info)) => {
					let child_keys =
						client.child_storage_keys(best_hash, info.clone(), None, None)?;
					for ck in child_keys {
						child_nodes.push((ck.clone(), info.clone()));
					}
				},
				_ => {
					// regular key
					let mut new_v = vec![0; original_v.len()];
					loop {
						// Create a random value to overwrite with.
						// NOTE: We use a possibly higher entropy than the original value,
						// could be improved but acts as an over-estimation which is fine for now.
						rng.fill_bytes(&mut new_v[..]);
						if check_new_value::<Block>(
							db.clone(),
							&trie,
							&k.to_vec(),
							&new_v,
							self.state_version(),
							state_col,
							None,
						) {
							break
						}
					}

					// Write each value in one commit.
					let (size, duration) = measure_write::<Block>(
						db.clone(),
						&trie,
						k.to_vec(),
						new_v.to_vec(),
						self.state_version(),
						state_col,
						None,
					)?;
					record.append(size, duration)?;
				},
			}
		}

		if self.params.include_child_trees {
			child_nodes.shuffle(&mut rng);
			info!("Writing {} child keys", child_nodes.len());

			for (key, info) in child_nodes {
				if let Some(original_v) = client
					.child_storage(best_hash, &info.clone(), &key)
					.expect("Checked above to exist")
				{
					let mut new_v = vec![0; original_v.0.len()];
					loop {
						rng.fill_bytes(&mut new_v[..]);
						if check_new_value::<Block>(
							db.clone(),
							&trie,
							&key.0,
							&new_v,
							self.state_version(),
							state_col,
							Some(&info),
						) {
							break
						}
					}

					let (size, duration) = measure_write::<Block>(
						db.clone(),
						&trie,
						key.0,
						new_v.to_vec(),
						self.state_version(),
						state_col,
						Some(&info),
					)?;
					record.append(size, duration)?;
				}
			}
		}

		Ok(record)
	}
}

/// Measures write benchmark
/// if `child_info` exist then it means this is a child tree key
fn measure_write<Block: BlockT>(
	db: Arc<dyn sp_database::Database<DbHash>>,
	trie: &DbState<Block>,
	key: Vec<u8>,
	new_v: Vec<u8>,
	version: StateVersion,
	_col: ColumnId,
	child_info: Option<&ChildInfo>,
) -> Result<(usize, Duration)> {
	let start = Instant::now();
	// Create a TX that will modify the Trie in the DB and
	// calculate the root hash of the Trie after the modification.
	let replace = vec![(key.as_ref(), Some(new_v.as_ref()))];
	let stx = match child_info {
		Some(info) => trie.child_storage_root(info, replace.iter().cloned(), version).0,
		None => trie.storage_root(replace.iter().cloned(), version),
	};

	let mut tx = Transaction::<DbHash>::default();
	sc_client_db::apply_tree_commit::<HashingFor<Block>>(stx, db.supports_tree_column(), &mut tx);

	db.commit(tx).map_err(|e| format!("Writing to the Database: {}", e))?;
	let result = (new_v.len(), start.elapsed());

	/*
	// Now undo the changes by removing what was added.
	let tx = convert_tx::<Block>(db.clone(), mdb.clone(), true, col);
	db.commit(tx).map_err(|e| format!("Writing to the Database: {}", e))?;
	*/
	Ok(result)
}

/// Checks if a new value causes any collision in tree updates
/// returns true if there is no collision
/// if `child_info` exist then it means this is a child tree key
fn check_new_value<Block: BlockT>(
	db: Arc<dyn sp_database::Database<DbHash>>,
	trie: &DbState<Block>,
	key: &Vec<u8>,
	new_v: &Vec<u8>,
	version: StateVersion,
	col: ColumnId,
	child_info: Option<&ChildInfo>,
) -> bool {
	let new_kv = vec![(key.as_ref(), Some(new_v.as_ref()))];
	let stx = match child_info {
		Some(info) => trie.child_storage_root(info, new_kv.iter().cloned(), version).0,
		None => trie.storage_root(new_kv.iter().cloned(), version),
	};
	let mut mdb = MemoryDB::<HashingFor<Block>>::default();
	stx.main.apply_to(&mut mdb);
	for (k, (_, rc)) in mdb.drain().into_iter() {
		if rc > 0 {
			//db.sanitize_key(&mut k);
			if db.get(col, k.as_ref()).is_some() {
				trace!("Benchmark-store key creation: Key collision detected, retry");
				return false
			}
		}
	}
	true
}
