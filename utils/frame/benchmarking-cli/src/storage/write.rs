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
use sc_client_api::UsageProvider;
use sc_client_db::{DatabaseSource, DbHash, DbState, DB_HASH_LEN};
use sc_service::Configuration;
use sp_api::StateBackend;
use sp_blockchain::HeaderBackend;
use sp_database::{ColumnId, Transaction};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, HashFor, Header as HeaderT},
};
use sp_trie::PrefixedMemoryDB;

use log::info;
use rand::prelude::*;
use std::{fmt::Debug, sync::Arc, time::Instant};

use super::{cmd::StorageCmd, record::BenchRecord};

impl StorageCmd {
	/// Benchmarks the time it takes to write a single Storage item.
	/// Uses the latest state that is available for the given client.
	pub(crate) fn bench_write<Block, H, C>(
		&self,
		cfg: &Configuration,
		client: Arc<C>,
		(db, state_col): (Arc<dyn sp_database::Database<DbHash>>, ColumnId),
		storage: Arc<dyn sp_state_machine::Storage<HashFor<Block>>>,
	) -> Result<BenchRecord>
	where
		Block: BlockT<Header = H, Hash = DbHash> + Debug,
		H: HeaderT<Hash = DbHash>,
		C: UsageProvider<Block> + HeaderBackend<Block>,
	{
		// Store the time that it took to write each value.
		let mut record = BenchRecord::default();

		let is_parity = matches!(cfg.database, DatabaseSource::ParityDb { path: _ });
		let block = BlockId::Number(client.usage_info().chain.best_number);
		let header = client.header(block)?.ok_or("Header not found")?;
		let original_root = *header.state_root();
		let trie = DbState::<Block>::new(storage.clone(), original_root);

		info!("Preparing keys from block {}", block);
		// Load all KV pairs and randomly shuffle them.
		let mut kvs = trie.pairs();
		let mut rng = Self::setup_rng();
		kvs.shuffle(&mut rng);

		info!("Writing {} keys", kvs.len());
		// Write each value in one commit.
		for (k, original_v) in kvs.iter() {
			// Create a random value to overwrite with.
			// NOTE: We use a possibly higher entropy than the original value,
			// could be improved but acts as an over-estimation which is fine for now.
			let mut new_v = vec![0; original_v.len()];
			rng.fill_bytes(&mut new_v[..]);

			// Interesting part here:
			let start = Instant::now();
			// Create a TX that will modify the Trie in the DB and
			// calculate the root hash of the Trie after the modification.
			let replace = vec![(k.as_ref(), Some(new_v.as_ref()))];
			let (root, tx) = trie.storage_root(replace.iter().cloned(), self.state_version());
			let tx = convert_tx::<Block>(tx, state_col, is_parity);
			db.commit(tx).map_err(|e| format!("Writing to the Database: {}", e))?;

			record.append(new_v.len(), start.elapsed())?;

			// Now undo the change:
			// Create a Trie with the modified root hash and replace the value with its original.
			let trie = DbState::<Block>::new(storage.clone(), root);
			let replace = vec![(k.as_ref(), Some(original_v.as_ref()))];
			let (root, tx) = trie.storage_root(replace.iter().cloned(), self.state_version());
			let tx = convert_tx::<Block>(tx, state_col, is_parity);
			db.commit(tx).map_err(|e| format!("Writing to the Database: {}", e))?;

			// Inserting the orginal value should bring us back to the original root hash.
			if root != original_root {
				// A crash here means hat the chain snapshot is now toast.
				log::error!("DB corrupted. Wrong final root: {:?} vs {:?}", root, original_root);
				std::process::exit(1);
			}
		}
		Ok(record)
	}
}

/// Converts a Trie transaction into a DB transaction.
///
/// The keys of Trie transactions are prefixed, this is treated differently by each DB.
/// ParityDB can use an optimization where only the last `DB_HASH_LEN` byte are needed.
/// The last `DB_HASH_LEN` byte are the hash of the actual stored data, everything
/// before that is the route in the Patricia Trie.
/// RocksDB cannot do this and needs the whole route, hence no key truncating for RocksDB.
fn convert_tx<B: BlockT>(
	mut tx: PrefixedMemoryDB<HashFor<B>>,
	col: ColumnId,
	parity_db: bool,
) -> Transaction<DbHash> {
	let mut ret = Transaction::<DbHash>::default();

	for (mut k, (v, rc)) in tx.drain().into_iter() {
		// Using shorter keys is only possible for ParityDB.
		// RocksDB needs the full key with prefix.
		if parity_db {
			let _prefix = k.drain(0..k.len() - DB_HASH_LEN);
		}

		if rc > 0 {
			ret.set(col, k.as_ref(), &v);
		} else if rc < 0 {
			ret.remove(col, &k);
		}
		// 0 means no modification.
	}
	ret
}
