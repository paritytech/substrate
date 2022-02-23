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

use super::{post_process::TimeResult, cmd::StorageCmd};

impl StorageCmd {
	pub fn read<B, BA, C>(&self, client: Arc<C>) -> Result<TimeResult>
	where
		C: UsageProvider<B> + StorageProvider<B, BA>,
		B: BlockT + Debug,
		BA: ClientBackend<B>,
		<<B as BlockT>::Header as HeaderT>::Number: From<u32>,
	{
		let mut times = TimeResult::default();
		let block = BlockId::Number(client.usage_info().chain.best_number);

		info!("Preparing keys from block {}", block);
		// Load all keys and randomly shuffle them.
		let empty_prefix = StorageKey(Vec::new());
		let mut keys = client.storage_keys(&block, &empty_prefix)?;
		let mut rng = self.setup_rng();
		keys.shuffle(&mut rng);

		// Warmup.
		for i in 0..self.warmups {
			info!("Warmup round {}/{}", i + 1, self.warmups);
			for key in keys.clone() {
				let _ = client
					.storage(&block, &key)
					.expect("Checked above to exist")
					.ok_or("Value unexpectedly empty")?;
			}
		}

		// Interesting part here:
		// Read all the keys in the database and measure the time it takes to access each.
		info!("Instrumentation round");
		for key in keys.clone() {
			let start = Instant::now();
			let v = client
				.storage(&block, &key)
				.expect("Checked above to exist")
				.ok_or("Value unexpectedly empty")?;
			let elapsed: u64 = start.elapsed().as_nanos().try_into().unwrap();
			times.ns_by_size.push((v.0.len() as u64, elapsed));
		}

		Ok(times)
	}
}
