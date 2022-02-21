use sc_cli::{CliConfiguration, Result};
use sc_client_db::{
	columns,
	utils::{open_database, read_meta, DatabaseType},
	BenchmarkingState, Database, DatabaseSource, DbHash,
};
use sc_service::Configuration;
use sp_database::Transaction;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use log::info;
use rand::prelude::*;
use std::{
	path::PathBuf,
	sync::Arc,
	time::{Duration, Instant},
};

use super::{cmd::ReadCmd, *};
use crate::bedrock::TimeResult;

const KEY_LEN_BYTES: usize = 48;
const WRITE_LEN_BYTES: usize = 64;
const INIT_SIZE: usize = 1_000_000;

impl ReadCmd {
	pub fn run<B>(&self, config: Configuration) -> Result<()>
	where
		B: BlockT,
	{
		let db = setup_db::<B>(&config)?;

		info!("Reading DB. {:?}", self.db_args);
		let kvs = self.db_args.prepare_kvs();
		let res = raw_db_read(&config, kvs, db.clone());
		info!("Post processing");
		res.summary();
		res.save_json("first.json");

		Ok(())
	}
}

pub fn raw_db_read(cfg: &Configuration, kvs: Vec<KV>, db: Arc<DB>) -> TimeResult {
	let repeat = 10;
	let warmup = 10;

	info!("{} rounds of warmup...", warmup);
	for _ in 0..10 {
		for (k, v) in kvs.iter() {
			// TODO nicer proof text
			db.get(COLUMN, &k).expect("Different seed when populating the DB");
		}
	}
	info!("Reading all keys once more");
	let mut res = TimeResult::default();
	for (k, v) in kvs.iter() {
		let start = Instant::now();
		// TODO nicer proof text
		db.get(COLUMN, &k).expect("Different seed when populating the DB");
		let took = start.elapsed();
		res.time_by_size.push((v.len() as u64, took.as_nanos()));
	}
	res
}

/// Raw DB write performance of the underlying Database.
/// Does not represent a Write from in Substrate, since they funnel through a Trie first.
pub fn raw_db_write<R: Rng>(rng: &mut R, cfg: &Configuration, db: Arc<DB>) {
	dump_info(db.clone());
	// Create the keys.
	//let kvs = prepare_kvs(rng, 1);

	/*for p in 2..10 {
		let n = 1 << (p << 1);
		let r = 2 * 5 + 1; // uneven for median calculation

		let mut times = Vec::<Duration>::new();

		for _ in 0..r {
			let start = Instant::now();
			// Write them and measure the time.
			write_kvs(&kvs, db.clone(), COLUMN);
			let elapsed = start.elapsed();

			// Cleanup.
			remove_kvs(&kvs, db.clone(), COLUMN);
			times.push(elapsed);
		}
		// Calculate the median of the times.
		times.sort();
		let median = times[times.len() / 2];
		let per = (median.as_nanos() as f64 / n as f64) / 1000.0;
		// Print the results.
		info!("A commit with {} values took {} ms. {:.3} µs each", n, median.as_millis(), per);
	}*/
}
