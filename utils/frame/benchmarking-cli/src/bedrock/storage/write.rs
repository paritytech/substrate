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
use sc_client_db::{DatabaseSource, DbHash};

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

struct StorageUnprefixer<H>(Arc<dyn sp_state_machine::Storage<H>>);

impl<H> sp_state_machine::Storage<H> for StorageUnprefixer<H>
where
	H: sp_api::Hasher,
{
	fn get(
		&self,
		key: &H::Out,
		prefix: Prefix,
	) -> sp_std::result::Result<Option<sp_state_machine::DBValue>, sp_state_machine::DefaultError> {
		let res = self.0.get(&key, prefix);
		if res.is_err() || res.clone().unwrap().is_none() {
			warn!(
				"Not found {} with prefix {}/{}",
				hex::encode(&key),
				hex::encode(&prefix.0),
				prefix.1.unwrap_or_default()
			);
		}
		res
	}
}

impl WriteCmd {
	pub fn run<Block, BA, S, H, C>(
		&self,
		cfg: &Configuration,
		prov: Arc<C>,
		_backend: Arc<BA>,
		db: Arc<dyn sp_database::Database<DbHash>>,
		storage: Arc<dyn sp_state_machine::Storage<HashFor<Block>>>,
	) -> Result<()>
	where
		Block: BlockT<Header = H, Hash = H256> + Debug,
		BA: Backend<Block, State = S>,
		H: HeaderT<Hash = H256>,
		C: UsageProvider<Block> + StorageProvider<Block, BA> + HeaderBackend<Block>,
		S: sp_state_machine::Backend<
			HashFor<Block>,
			Transaction = sp_trie::PrefixedMemoryDB<HashFor<Block>>,
		>,
	{
		let COLUMN = sc_client_db::columns::STATE;
		let mut state_version = StateVersion::V0;
		if self.storage_v1 {
			state_version = StateVersion::V1;
		}

		let is_parity = matches!(cfg.database, DatabaseSource::ParityDb{path:_});
		let block = BlockId::Number(prov.usage_info().chain.best_number);
		info!("Best block is {}", block);
		let header = prov.header(block).unwrap().unwrap();
		let original_root = header.state_root();

		let mut rng = StdRng::seed_from_u64(self.seed);

		let state = DbState::<Block>::new(storage.clone(), *original_root);
		info!("Preparing {} keys", state.keys(Default::default()).len());

		// Load all KV pairs from the DB.
		let mut original_kvs = state.pairs();
		// Randomly shuffle the KV pairs.
		original_kvs.shuffle(&mut rng);
		let mut kvs = original_kvs.clone();
		// Replace each value with a random value of the same size.
		// NOTE: We use a possibly higher entropy than the original value,
		// could be improved but acts as an overestimation which is fine for now.
		for (_, v) in kvs.iter_mut() {
			*v = random_vec(&mut rng, v.len());
		}

		info!("Starting run");
		// Store the time that it took to write a value.
		let mut time_by_key_index = Vec::<Duration>::with_capacity(kvs.len());
		// Write each value in one commit.
		for ((_, ov), (k, v)) in original_kvs.iter().zip(kvs.iter()) {
			// Interesting part here:
			let start = Instant::now();
			// Create a TX that will modify the Trie in the DB and
			// calculate the root hash of the Trie after appending `delta`.
			let delta = vec![(k.clone(), v.clone())];
			let delta = delta.iter().map(|(k2, v2)| (k2.as_ref(), Some(v2.as_ref())));
			let (root, tx) = state.storage_root(delta, state_version);
			let tx = convert_tx::<Block>(COLUMN, tx, is_parity);
			db.commit(tx).expect("Must commit");

			time_by_key_index.push(start.elapsed());

			let new_state = DbState::<Block>::new(storage.clone(), root);

			// Replace it with the original value.
			let delta = vec![(k.clone(), ov.clone())];
			let delta = delta.iter().map(|(k2, v2)| (&**k2, Some(v2.as_ref())));
			let (root, tx) = new_state.storage_root(delta, state_version);
			let tx = convert_tx::<Block>(COLUMN, tx, is_parity);
			db.commit(tx).expect("Must commit");

			// Replacing the value should bring us back to the original root.
			if root != *original_root {
				log::error!("Wrong final root. {:?} vs {:?}", root, original_root);
				std::process::exit(1);
			}
		}

		let mut res = TimeResult::default();
		for (i, (_, v)) in original_kvs.clone().into_iter().enumerate() {
			res.time_by_size.push((v.len() as u64, time_by_key_index[i].as_nanos()));
		}

		let template = res.post_process(&cfg, &self.post_proc, false)?;
		template.write(&self.post_proc.weight_out, false)
	}
}

fn convert_tx<B: BlockT>(
	col: ColumnId,
	mut tx: sp_trie::PrefixedMemoryDB<HashFor<B>>,
	parity_db: bool,
) -> Transaction<H256> {
	let mut ret = sp_database::Transaction::<H256>::default();

	for (mut k, (v, rc)) in tx.drain().into_iter() {
		// Trunking keys is only needed for ParityDB.
		if parity_db {
			k.drain(0..k.len() - sc_client_db::DB_HASH_LEN);
		}
		if rc > 0 {
			ret.set(col, k.as_ref(), &v);
			if v.len() == 0 {
				panic!("Inserting should never be a removal");
			}
		} else if rc < 0 {
			ret.remove(col, &k);
		} else if rc == 0 && v.len() == 0 {
			panic!("should not happen");
		}
	}
	ret
}

fn random_vec<R: Rng>(rng: &mut R, len: usize) -> Vec<u8> {
	let mut val = vec![0u8; len];
	rng.fill_bytes(&mut val[..]);
	val
}
