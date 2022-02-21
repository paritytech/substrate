#![allow(unused_imports)] // TODO

pub mod cmd;
pub mod fill;
pub mod read;

use std::sync::Arc;

use log::*;
use rand::prelude::*;

use clap::Args;
use sc_cli::{CliConfiguration, Result};
use sc_client_db::{
	columns,
	utils::{open_database, read_meta, DatabaseType},
	BenchmarkingState, Database, DatabaseSource, DbHash,
};
use sc_service::Configuration;
use sp_database::Transaction;
use sp_runtime::traits::Block as BlockT;

const COLUMN: u32 = 0;

// Helper
type DB = dyn Database<DbHash>;
// Helper
type KV = (Vec<u8>, Vec<u8>);

#[derive(Clone, PartialEq, Args)]
pub struct DbArgs {
	/// RNG seed used to generate key-value pairs.
	#[clap(long, default_value = "0")]
	pub seed: u64,

	/// Best effort approach to set the total size of the DB in MiB (2^20).
	#[clap(long, default_value = "512")]
	pub total_size: u64,

	/// Value min length.
	#[clap(long, default_value = "1")]
	pub v_min_len: u64,

	/// Value max length.
	#[clap(long, default_value = "1024")]
	pub v_max_len: u64,

	/// Key length. Currently constant.
	#[clap(long, default_value = "32")]
	pub k_len: u64,
}

impl DbArgs {
	/// Returns the number of KV pairs needed to reach `total_size`.
	/// NOTE: This is best effort.
	pub fn kv_count(&self) -> u64 {
		// c * KEY_L + c * VAL_L = total_size
		let val_l = (self.v_max_len + self.v_min_len) / 2;
		(self.total_size << 20) / (self.k_len + val_l)
	}

	pub fn prepare_kvs(&self) -> Vec<KV> {
		let mut rng = self.setup_rng();
		let ks = self.prepare_ks(&mut rng);
		let vs = self.prepare_vs(&mut rng);
		// zip
		ks.iter().cloned().zip(vs.iter().cloned()).collect()
	}

	pub fn prepare_ks<R: Rng>(&self, rng: &mut R) -> Vec<Vec<u8>> {
		(0..self.kv_count()).map(|_| random_vec(rng, self.k_len)).collect()
	}

	pub fn prepare_vs<R: Rng>(&self, rng: &mut R) -> Vec<Vec<u8>> {
		use rand_distr::{Distribution, Uniform};
		let dist = Uniform::new_inclusive(self.v_min_len, self.v_max_len);

		(0..self.kv_count())
			.map(|i| {
				let l = dist.sample(rng);
				random_vec(rng, l)
			})
			.collect()
	}

	pub fn setup_rng(&self) -> StdRng {
		StdRng::seed_from_u64(self.seed)
	}
}

impl std::fmt::Debug for DbArgs {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"Target Size: {} MiB, KV Pairs: {}, Key Len: {}, Value len: rng[{}, {}]",
			self.total_size,
			self.kv_count(),
			self.k_len,
			self.v_min_len,
			self.v_max_len
		)
	}
}

pub(crate) fn setup_db<BB>(config: &Configuration) -> Result<Arc<DB>>
where
	BB: BlockT,
{
	let mut db_config = sc_client_db::DatabaseSettings {
		state_cache_size: config.state_cache_size,
		state_cache_child_ratio: config.state_cache_child_ratio.map(|v| (v, 100)),
		state_pruning: config.state_pruning.clone(),
		source: config.database.clone(),
		keep_blocks: config.keep_blocks.clone(),
		transaction_storage: config.transaction_storage.clone(),
	};
	if db_config.state_cache_size != 0 {
		panic!("Cache size must be 0");
	}
	info!("Loading {}... with cache size {}", db_config.source, db_config.state_cache_size);
	if db_config.source.path().is_some() {
		info!("Db path = {}", db_config.source.path().unwrap().display());
	}

	let db = open_database::<BB>(&db_config, DatabaseType::Full)
		.map_err(|e| sc_cli::Error::Input(format!("{}", e)))?;
	let meta = read_meta::<BB>(&*db, columns::HEADER)?;
	info!("Best block: {}", meta.best_number);
	Ok(db)
}

fn dump_info(db: Arc<DB>) {}

pub(crate) fn random_vec<R: Rng>(rng: &mut R, len: u64) -> Vec<u8> {
	let mut val = vec![0u8; len as usize];
	rng.fill_bytes(&mut val[..]);
	val
}

fn write_kvs(kvs: &Vec<KV>, db: Arc<DB>, column: u32) {
	let mut commit = Transaction::new();
	for (k, v) in kvs {
		commit.set(column, k, v);
	}
	db.commit(commit).unwrap();
}

fn remove_kvs(kvs: &Vec<KV>, db: Arc<DB>, column: u32) {
	let mut commit = Transaction::new();
	for (k, _) in kvs {
		commit.remove(column, &k);
	}
	db.commit(commit).unwrap();
}
