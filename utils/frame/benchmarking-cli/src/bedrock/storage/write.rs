use sc_cli::Result;
use sc_client_api::{
	blockchain::Backend as BlockchainBackend, Backend, BlockImportOperation, NewBlockState,
	StorageProvider, UsageProvider,
};
use sc_client_db::DbState;
use sc_service::Configuration;
use sp_api::StateBackend;
use sp_blockchain::HeaderBackend;
use sp_core::{map, storage::StorageKey, H256};
use sp_database::{ColumnId, Transaction};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, HashFor, Header as HeaderT},
};
use sp_state_machine::*;
use sp_storage::{StateVersion, StorageMap};

use hash_db::{HashDB, Hasher, Prefix};
use kvdb::DBTransaction;
use log::info;
use rand::prelude::*;
use std::{
	fmt::Debug,
	fs,
	ops::Range,
	path::PathBuf,
	sync::Arc,
	time::{Duration, Instant},
};

use super::{super::db::setup_db, cmd::WriteCmd};
use crate::bedrock::TimeResult;

impl WriteCmd {
	pub fn run<B, BA, S, H, C>(
		&self,
		cfg: &Configuration,
		prov: Arc<C>,
		backend: Arc<BA>,
	) -> Result<()>
	where
		B: BlockT<Header = H, Hash = H256> + Debug,
		BA: Backend<B, State = S>,
		H: HeaderT<Hash = H256>,
		C: UsageProvider<B> + StorageProvider<B, BA> + HeaderBackend<B>,
		S: sp_state_machine::Backend<
			HashFor<B>,
			Transaction = sp_trie::PrefixedMemoryDB<HashFor<B>>,
		>,
	{
		let COLUMN = sc_client_db::columns::STATE;
		let state_version = StateVersion::V1;
		let block = BlockId::Number(prov.usage_info().chain.best_number);
		info!("Best block is {}", block);
		let state = backend.state_at(block)?;
		let header = prov.header(block).unwrap().unwrap();
		let original_root = header.state_root();
		info!("Found {} keys", state.keys(Default::default()).len());
		let db = backend.expose_db().ok_or("no DB")?;
		let storage = backend.expose_storage().ok_or("no storage")?;

		// Load all KV pairs from the DB.
		let original_kvs = state.pairs();
		let mut kvs = original_kvs.clone();
		// Replace each value with a random value of the same size.
		// NOTE: We use a possibly higher entropy than the original value,
		// could be improved but acts as an overestimation which is fine for now.
		let mut rng = StdRng::seed_from_u64(123);	// TODO arg
		for (_, v) in kvs.iter_mut() {
			let l = rng.gen_range(0..=v.len());
			*v = random_vec(&mut rng, l);
		}
		// Randomly shuffle the KV pairs.
		kvs.shuffle(&mut rng);

		// Store the time that it took to write a value.
		let mut time_by_key_index = Vec::<Duration>::with_capacity(kvs.len());
		// Write each value in one commit.
		for ((_, ov), (k, v)) in original_kvs.iter().zip(kvs.iter()) {
			let delta = vec![(k.clone(), v.clone())];
			let delta = delta.iter().map(|(k, v)| (k.as_ref(), Some(v.as_ref())));

			// Interesting part here:
			let start = Instant::now();
			// Create a TX that will modify the Trie in the DB and
			// calculate the root hash of the Trie after appending `delta`.
			let (root, tx) = state.storage_root(delta, state_version);
			let tx = convert_tx::<B>(COLUMN, tx);
			db.commit(tx).expect("Must commit");

			time_by_key_index.push(start.elapsed());
			
			// Trie with the new root.
			let new_state = DbState::<B>::new(storage.clone(), root);

			// Now undo the changes to restore the original state.
			// Sanity check that all values have been written.
			let read2 = new_state.storage(k).expect("Must be in trie").unwrap();
			if read2 != *v {
				// FAILS HERE
				log::error!("Read wrong value. {:?} vs {:?}", read2, *v);
			}
			// Replace it with the original value.
			let delta = vec![(k.clone(), ov.clone())];
			let delta = delta.iter().map(|(k, v)| (k.as_ref(), Some(v.as_ref())));

			let (root, tx) = new_state.storage_root(delta, state_version);
			let tx = convert_tx::<B>(COLUMN, tx);
			db.commit(tx).expect("Must commit");
			// Replacing the value should bring us back to the original root.
			if root != *original_root {
				// FAILS HERE
				log::error!("Wrong final root. {:?} vs {:?}", root, original_root);
				std::process::exit(1);
			}
		}

		let mut res = TimeResult::default();
		for (i, (_, v)) in original_kvs.clone().into_iter().enumerate() {
			res.time_by_size.push((v.len() as u64, time_by_key_index[i].as_nanos()));
		}

		let template = res.post_process(&cfg, &self.post_proc)?;
		template.write(&self.post_proc.weight_out)
	}
}

fn convert_tx<B: BlockT>(
	col: ColumnId,
	mut tx: sp_trie::PrefixedMemoryDB<HashFor<B>>,
) -> Transaction<H256> {
	let mut ret = sp_database::Transaction::<H256>::default();
	
	for (k, (v, rc)) in tx.drain().into_iter() {
		if rc > 0 {
			ret.set(col, k.as_ref(), &v);
		} else if rc < 0 {
			ret.remove(col, &k);
		}
	}
	ret
}

fn random_vec<R: Rng>(rng: &mut R, len: usize) -> Vec<u8> {
	let mut val = vec![0u8; len];
	rng.fill_bytes(&mut val[..]);
	val
}
