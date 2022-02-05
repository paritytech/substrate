use rand::Rng;
use sc_client_db::{Database, DbHash};
use sp_database::Transaction;
use std::{
	fmt::Debug,
	sync::Arc,
	time::{Duration, Instant},
};
use frame_benchmarking::BenchmarkResult;
use log::info;

use crate::bedrock::*;

const KEY_LEN_BYTES: usize = 32;
const WRITE_LEN_BYTES: usize = 64;
const COLUMN: u32 = 0;

/// Key-Value pair.
type KV = (Vec<u8>, Vec<u8>);
type DB = dyn Database<DbHash>;

pub fn db_write(cfg: &BedrockParams, db: &DB) {
	for p in 2..10 {
		let n = 1 << (p << 1);
		let r = 2 * 5 + 1; // uneven for median calculation

		let mut times = Vec::<Duration>::new();
		// Create the key and value pairs.
		let kvs = prepare_kvs(n);

		for _ in 0..r {
			let start = Instant::now();
			// Write them and measure the time.
			write_kvs(&kvs, db);
			let elapsed = start.elapsed();

			// Cleanup.
			remove_kvs(&kvs, db);
			times.push(elapsed);
		}
		// Calculate the median of the times.
		times.sort();
		let median = times[times.len() / 2];
		let per = (median.as_nanos() as f64 / n as f64) / 1000.0;
		// Print the results.
		info!("A commit with {} values took {} ms. {:.3} µs each", n, median.as_millis(), per);
	}
}

fn write_kvs(kvs: &Vec<KV>, db: &DB) {
	let mut commit = Transaction::new();
	for (k, v) in kvs {
		commit.set(COLUMN, k, v);
	}
	db.commit(commit).unwrap();
}

fn remove_kvs(kvs: &Vec<KV>, db: &DB) {
	let mut commit = Transaction::new();
	for (k, _) in kvs {
		commit.remove(COLUMN, &k);
	}
	db.commit(commit).unwrap();
}

fn prepare_kvs(num: usize) -> Vec<KV> {
	let mut ret = Vec::with_capacity(num);
	// Seed for reproducibility.
	let mut rng = rand::thread_rng();

	for i in 0..num {
		let k = random_vec(&mut rng, KEY_LEN_BYTES);
		let v = random_vec(&mut rng, WRITE_LEN_BYTES);
		ret.push((k, v));
	}

	ret
}

// Thanks Nikolay!
fn random_vec<R: Rng>(rng: &mut R, len: usize) -> Vec<u8> {
	let mut val = vec![0u8; len];
	rng.fill_bytes(&mut val[..]);
	val
}
