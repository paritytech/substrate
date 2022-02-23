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

use super::{post_process::TimeResult, StorageCmd};

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
