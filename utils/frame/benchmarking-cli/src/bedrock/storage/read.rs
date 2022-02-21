use sc_cli::Result;
use sc_client_api::{
	blockchain::Backend as BlockchainBackend, Backend, StorageProvider, UsageProvider,
};
use sc_service::Configuration;
use sp_core::storage::{well_known_keys, ChildInfo, Storage, StorageChild, StorageKey, StorageMap};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT},
};

use log::info;
use rand::prelude::*;
use serde::Serialize;
use std::{
	fmt::Debug,
	fs,
	path::PathBuf,
	sync::Arc,
	time::{Duration, Instant},
};

use super::cmd::ReadCmd;
use crate::bedrock::TimeResult;

impl ReadCmd {
	pub fn run<B, BA, C>(&self, cfg: &Configuration, client: Arc<C>) -> Result<()>
	where
		C: UsageProvider<B> + StorageProvider<B, BA>,
		B: BlockT + Debug,
		BA: Backend<B>,
		<<B as BlockT>::Header as HeaderT>::Number: From<u32>,
	{
		let block = BlockId::Number(client.usage_info().chain.best_number);
		info!("Best block is {}", block);

		info!("Loading storage keys");
		let empty_key = StorageKey(Vec::new());
		let mut tops = client.storage_keys(&block, &empty_key)?;
		// Randomly shuffle the top keys.
		let mut rng = rand::thread_rng();
		tops.shuffle(&mut rng);

		let mut time_by_key_index = Vec::<Duration>::with_capacity(tops.len());

		// Interesting part right here.
		// Read all the keys in the database and measure the time it takes to access each.
		info!("Running benchmark with {} keys", tops.len());
		for key in tops.clone() {
			let mut start = Instant::now();
			client.storage(&block, &key).expect("Must exist").unwrap();
			time_by_key_index.push(start.elapsed());
		}

		// TODO warmup

		info!("Measuring value sizes");
		let mut res = TimeResult::default();
		for (i, key) in tops.clone().into_iter().enumerate() {
			let value = client.storage(&block, &key).expect("Must exist").unwrap();
			let size = value.0.len();
			res.time_by_size.push((size as u64, time_by_key_index[i].as_nanos()));
		}

		let template = res.post_process(&cfg, &self.post_proc)?;
		template.write(&self.post_proc.weight_out)
	}
}
