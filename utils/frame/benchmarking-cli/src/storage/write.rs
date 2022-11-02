// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, HashFor, Header as HeaderT},
};
use sp_trie::PrefixedMemoryDB;

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
		storage: Arc<dyn sp_state_machine::Storage<HashFor<Block>>>,
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
		let header = client.header(BlockId::Hash(best_hash))?.ok_or("Header not found")?;
		let original_root = *header.state_root();
		let trie = DbStateBuilder::<Block>::new(storage.clone(), original_root).build();

		info!("Preparing keys from block {}", best_hash);
		// Load all KV pairs and randomly shuffle them.
		let mut kvs = trie.pairs();
		let (mut rng, _) = new_rng(None);
		kvs.shuffle(&mut rng);
		info!("Writing {} keys", kvs.len());

		let mut child_nodes = Vec::new();

		// Generate all random values first; Make sure there are no collisions with existing
		// db entries, so we can rollback all additions without corrupting existing entries.
		for (k, original_v) in kvs {
			match (self.params.include_child_trees, self.is_child_key(k.to_vec())) {
				(true, Some(info)) => {
					let child_keys =
						client.child_storage_keys_iter(&best_hash, info.clone(), None, None)?;
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
					.child_storage(&best_hash, &info.clone(), &key)
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

/// Converts a Trie transaction into a DB transaction.
/// Removals are ignored and will not be included in the final tx.
/// `invert_inserts` replaces all inserts with removals.
fn convert_tx<B: BlockT>(
	db: Arc<dyn sp_database::Database<DbHash>>,
	mut tx: PrefixedMemoryDB<HashFor<B>>,
	invert_inserts: bool,
	col: ColumnId,
) -> Transaction<DbHash> {
	let mut ret = Transaction::<DbHash>::default();

	for (mut k, (v, rc)) in tx.drain().into_iter() {
		if rc > 0 {
			db.sanitize_key(&mut k);
			if invert_inserts {
				ret.remove(col, &k);
			} else {
				ret.set(col, &k, &v);
			}
		}
		// < 0 means removal - ignored.
		// 0 means no modification.
	}
	ret
}

/// Measures write benchmark
/// if `child_info` exist then it means this is a child tree key
fn measure_write<Block: BlockT>(
	db: Arc<dyn sp_database::Database<DbHash>>,
	trie: &DbState<Block>,
	key: Vec<u8>,
	new_v: Vec<u8>,
	version: StateVersion,
	col: ColumnId,
	child_info: Option<&ChildInfo>,
) -> Result<(usize, Duration)> {
	let start = Instant::now();
	// Create a TX that will modify the Trie in the DB and
	// calculate the root hash of the Trie after the modification.
	let replace = vec![(key.as_ref(), Some(new_v.as_ref()))];
	let stx = match child_info {
		Some(info) => trie.child_storage_root(info, replace.iter().cloned(), version).2,
		None => trie.storage_root(replace.iter().cloned(), version).1,
	};
	// Only the keep the insertions, since we do not want to benchmark pruning.
	let tx = convert_tx::<Block>(db.clone(), stx.clone(), false, col);
	db.commit(tx).map_err(|e| format!("Writing to the Database: {}", e))?;
	let result = (new_v.len(), start.elapsed());

	// Now undo the changes by removing what was added.
	let tx = convert_tx::<Block>(db.clone(), stx.clone(), true, col);
	db.commit(tx).map_err(|e| format!("Writing to the Database: {}", e))?;
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
	let mut stx = match child_info {
		Some(info) => trie.child_storage_root(info, new_kv.iter().cloned(), version).2,
		None => trie.storage_root(new_kv.iter().cloned(), version).1,
	};
	for (mut k, (_, rc)) in stx.drain().into_iter() {
		if rc > 0 {
			db.sanitize_key(&mut k);
			if db.get(col, &k).is_some() {
				trace!("Benchmark-store key creation: Key collision detected, retry");
				return false
			}
		}
	}
	true
}
