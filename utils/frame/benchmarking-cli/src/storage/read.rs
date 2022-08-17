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
use sp_core::storage::StorageKey;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT},
};

use log::info;
use rand::prelude::*;
use std::{fmt::Debug, sync::Arc, time::Instant};

use super::cmd::StorageCmd;
use crate::shared::{new_rng, BenchRecord};

impl StorageCmd {
	/// Benchmarks the time it takes to read a single Storage item.
	/// Uses the latest state that is available for the given client.
	pub(crate) fn bench_read<B, BA, C>(&self, client: Arc<C>) -> Result<BenchRecord>
	where
		C: UsageProvider<B> + StorageProvider<B, BA>,
		B: BlockT + Debug,
		BA: ClientBackend<B>,
		<<B as BlockT>::Header as HeaderT>::Number: From<u32>,
	{
		let mut record = BenchRecord::default();
		let block = BlockId::Number(client.usage_info().chain.best_number);

		info!("Preparing keys from block {}", block);
		// Load all keys and randomly shuffle them.
		let empty_prefix = StorageKey(Vec::new());
		let mut keys = client.storage_keys(&block, &empty_prefix)?;
		let (mut rng, _) = new_rng(None);
		keys.shuffle(&mut rng);

		let mut child_nodes = Vec::new();
		// Interesting part here:
		// Read all the keys in the database and measure the time it takes to access each.
		info!("Reading {} keys", keys.len());
		for key in keys.as_slice() {
			match (self.params.include_child_trees, self.is_child_key(key.clone().0)) {
				(true, Some(info)) => {
					// child tree key
					let child_keys = client.child_storage_keys(&block, &info, &empty_prefix)?;
					for ck in child_keys {
						child_nodes.push((ck.clone(), info.clone()));
					}
				},
				_ => {
					// regular key
					let start = Instant::now();
					let v = client
						.storage(&block, &key)
						.expect("Checked above to exist")
						.ok_or("Value unexpectedly empty")?;
					record.append(v.0.len(), start.elapsed())?;
				},
			}
		}

		if self.params.include_child_trees {
			child_nodes.shuffle(&mut rng);

			info!("Reading {} child keys", child_nodes.len());
			for (key, info) in child_nodes.as_slice() {
				let start = Instant::now();
				let v = client
					.child_storage(&block, info, key)
					.expect("Checked above to exist")
					.ok_or("Value unexpectedly empty")?;
				record.append(v.0.len(), start.elapsed())?;
			}
		}
		Ok(record)
	}
}
