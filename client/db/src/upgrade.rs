// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Database upgrade logic.

use std::fs;
use std::io::{Read, Write, ErrorKind};
use std::path::{Path, PathBuf};
use log::warn;
use std::marker::PhantomData;
use std::time::{Duration, Instant};

use sp_runtime::traits::{Block as BlockT, HashFor, NumberFor, Header as HeaderT};
use crate::HValue;
use crate::utils::DatabaseType;
use crate::{StateDb, PruningMode, StateMetaDb};
use historied_db::management::tree::TreeManagement;
use historied_db::{
	StateDBRef, InMemoryStateDBRef, StateDB, ManagementRef, Management,
	ForkableManagement, Latest, UpdateResult,
	historied::{InMemoryValue, InMemoryValueSlice, Value},
	historied::tree::Tree,
	management::tree::{Tree as TreeMgmt, ForkPlan},
};
use codec::{Decode, Encode};
use kvdb::KeyValueDB;
use std::io;

use std::sync::Arc;

/// Version file name.
const VERSION_FILE_NAME: &'static str = "db_version";

/// Current db version.
const CURRENT_VERSION: u32 = 2;

/// Upgrade database to current version.
pub fn upgrade_db<Block: BlockT>(db_path: &Path, db_type: DatabaseType) -> sp_blockchain::Result<()> {
	let is_empty = db_path.read_dir().map_or(true, |mut d| d.next().is_none());
	if !is_empty {
		let db_version = current_version(db_path)?;
		match db_version {
			0 => Err(sp_blockchain::Error::Backend(format!("Unsupported database version: {}", db_version)))?,
			1 => migrate_1_to_2::<Block>(db_path, db_type)?,
			2 => (),
			42 => {
				delete_historied::<Block>(db_path, db_type)?;
/*				let now = Instant::now();
				let hash_for_root = inject_non_canonical::<Block>(db_path, db_type)?;
				println!("inject non canonnical in {}", now.elapsed().as_millis());
				compare_latest_roots::<Block>(db_path, db_type, hash_for_root)?;*/
			},
			_ => Err(sp_blockchain::Error::Backend(format!("Future database version: {}", db_version)))?,
		}
	}

	update_version(db_path)
}

/// Migration from version1 to version2:
/// the number of columns has changed from 11 to 15;
fn migrate_1_to_2<Block: BlockT>(db_path: &Path, db_type: DatabaseType) -> sp_blockchain::Result<()> {
	// Number of columns in v0.
	const V1_NUM_COLUMNS: u32 = 11;
	{
		let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(V1_NUM_COLUMNS);
		let path = db_path.to_str()
			.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;
		let db = kvdb_rocksdb::Database::open(&db_config, &path)
			.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?;
		db.add_column().map_err(db_err)?;
		db.add_column().map_err(db_err)?;
		db.add_column().map_err(db_err)?;
		db.add_column().map_err(db_err)?;
		db.add_column().map_err(db_err)?;
	}

	Ok(())
}


/// This does not seems to work, there is still no reimport of the blocks.
fn delete_non_canonical<Block: BlockT>(db_path: &Path, db_type: DatabaseType) -> sp_blockchain::Result<()> {
		let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(crate::utils::NUM_COLUMNS);
		let path = db_path.to_str()
			.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;
		let db_read = kvdb_rocksdb::Database::open(&db_config, &path)
			.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?;

		let non_canon = db_read.get(crate::utils::COLUMN_META, crate::meta_keys::FINALIZED_BLOCK).unwrap().unwrap();
		let latest = db_read.get(crate::utils::COLUMN_META, crate::meta_keys::BEST_BLOCK).unwrap().unwrap();
		println!("non_can: {:?} latest : {:?}", non_canon, latest);
		let mut tx = db_read.transaction();
		tx.put(crate::utils::COLUMN_META, crate::meta_keys::BEST_BLOCK, non_canon.as_slice());
		db_read.write(tx).expect("dtdt");
		println!("replaced best block by finalized block value");
		

		let db = sp_database::as_database(db_read);

		let meta = crate::read_meta::<Block>(&*db, crate::columns::HEADER)?;
		let leaves = crate::LeafSet::<Block::Hash, NumberFor<Block>>::read_from_db(&*db, crate::columns::META, crate::meta_keys::LEAF_PREFIX)?;
		println!("previous leaf set: {:?}", leaves);

		let mut leaves = crate::LeafSet::<Block::Hash, NumberFor<Block>>::new();
		leaves.import(meta.finalized_hash, meta.finalized_number, Default::default());

		println!("new leaf set: {:?}", leaves);
		let mut tx = sp_database::Transaction::new();

		leaves.prepare_transaction(&mut tx, crate::columns::META, crate::meta_keys::LEAF_PREFIX);
		// second call on purpose
		leaves.prepare_transaction(&mut tx, crate::columns::META, crate::meta_keys::LEAF_PREFIX);
		db.commit(tx);


		let state_db: StateDb<Block::Hash, Vec<u8>> = StateDb::new(
			PruningMode::Constrained(sc_state_db::Constraints {
				max_blocks: None, // may require info in the future, in fact we should fetch it
				max_mem: None,
			}),
			true, // Rc or not does not matter in this case
			&StateMetaDb(&*db),
		).expect("TODO err");

		state_db.clear_non_canonical();
		Ok(())
/*		let storage_db = crate::StorageDb {
			db: db.clone(),
			state_db,
			prefix_keys: true,
		};
	
		let storage: Arc<crate::StorageDb<Block>> = Arc::new(storage_db);*/
}

// This would be interesting if it worked, but injecting key hashed encoded node
// is totally dumb. TODO delete
fn inject_non_canonical<Block: BlockT>(
	db_path: &Path,
	db_type: DatabaseType,
) -> sp_blockchain::Result<Block::Hash> {
	let path = db_path.to_str()
		.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;

	let journals = {
		let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(crate::utils::NUM_COLUMNS);
		let db_read = kvdb_rocksdb::Database::open(&db_config, &path)
			.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?;

		let non_canon = db_read.get(crate::utils::COLUMN_META, crate::meta_keys::FINALIZED_BLOCK).unwrap().unwrap();
		let latest = db_read.get(crate::utils::COLUMN_META, crate::meta_keys::BEST_BLOCK).unwrap().unwrap();
		println!("non_can: {:?} latest : {:?}", non_canon, latest);
		
		let db = sp_database::as_database(db_read);
		let meta = crate::read_meta::<Block>(&*db, crate::columns::HEADER)?;
		let leaves = crate::LeafSet::<Block::Hash, NumberFor<Block>>::read_from_db(&*db, crate::columns::META, crate::meta_keys::LEAF_PREFIX)?;
		println!("previous leaf set: {:?}", leaves);

		let meta = StateMetaDb(&*db);
		let state_db: StateDb<Block::Hash, Vec<u8>> = StateDb::new(
			PruningMode::Constrained(sc_state_db::Constraints {
				max_blocks: None, // may require info in the future, in fact we should fetch it
				max_mem: None,
			}),
			true, // Rc or not does not matter in this case
			&meta,
		).expect("TODO err");

		state_db.get_non_cannonical_journals(meta).expect("aib")
	};

	let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(crate::utils::NUM_COLUMNS);
	let db_histo = Arc::new(kvdb_rocksdb::Database::open(&db_config, &path)
		.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?);

	let historied_persistence = crate::RocksdbStorage(db_histo.clone());
	let mut management = TreeManagement::<
		<HashFor<Block> as hash_db::Hasher>::Out,
		u32,
		u32,
		Vec<u8>,
		crate::TreeManagementPersistenceNoTx,
	>::from_ser(historied_persistence);
	
	let mut last_hash = Default::default();
		for journal in journals {
			if let Some(state) = management.get_db_state_for_fork(&journal.parent_hash) {
				management.append_external_state(journal.hash, &state);
				last_hash = journal.hash;
				let state = management.latest_state();
				println!("adding journal: {:?} parent {:?}, at {:?}", journal.hash, journal.parent_hash, state);
				let mut historied_db = crate::HistoriedDBMut {
					current_state: state,
					db: db_histo.clone(),
				};
				let mut tx = historied_db.transaction();
				let mut nb_ins = 0;
				let mut nb_del = 0;
				for (k, v) in journal.inserted {
					nb_ins += 1;
					historied_db.update_single(k.as_slice(), Some(v), &mut tx);
				}
				for k in journal.deleted {
					nb_del += 1;
					historied_db.update_single(k.as_slice(), None, &mut tx);
				}
				historied_db.write_change_set(tx);
				println!("added, ins: {}, del: {}", nb_ins, nb_del);
				break; // TODO for test remove
			} else {
				println!("warn ignoring journal: {:?} parent {:?}", journal.hash, journal.parent_hash);
			}
		}

		Ok(last_hash)
}

fn compare_latest_roots<Block: BlockT>(db_path: &Path, db_type: DatabaseType, hash_for_root: Block::Hash) -> sp_blockchain::Result<()> {
	let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(crate::utils::NUM_COLUMNS);
	let path = db_path.to_str()
		.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;
	let db = kvdb_rocksdb::Database::open(&db_config, &path)
		.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?;

	let (tree_root, block_hash) = match db.get(crate::utils::COLUMN_META, crate::meta_keys::BEST_BLOCK) {
		Ok(id) => {
			let id = id.unwrap();
			let id = db.get(crate::columns::HEADER, &id).expect("s").map(|b| Block::Header::decode(&mut &b[..]).ok());
			use sp_runtime::traits::Header;
			let id = id.unwrap().expect("d");
			warn!("Head is {:?}", id);
	/*				let mut hash = <HashFor::<Block> as hash_db::Hasher>::Out::default();
				hash.as_mut().copy_from_slice(id.as_slice());*/
			(id.state_root().clone(), id.hash().clone())
		},
		Err(e) => panic!("no best block is bad sign {:?}", e),
	};
	println!("hash queryied: {:?}", tree_root);
	let db = Arc::new(db);
	let now = Instant::now();
	let historied_persistence = crate::RocksdbStorage(db.clone());
	let mut management = TreeManagement::<
		<HashFor<Block> as hash_db::Hasher>::Out,
		u32,
		u32,
		Vec<u8>,
		crate::TreeManagementPersistenceNoTx,
	>::from_ser(historied_persistence);

	if hash_for_root != block_hash {
		println!("querying not best block, but {:?}", hash_for_root);
	}
	let current_state = management.get_db_state(&hash_for_root).expect("just added");
	println!("current state {:?}", current_state);
	let historied_db = crate::HistoriedDB {
		current_state,
		db: db.clone(),
		do_assert: false,
	};


	let mut root_callback = trie_db::TrieRoot::<HashFor<Block>, _>::default();
	let _state = management.get_db_state(&hash_for_root).expect("just added");
	let iter_kv = historied_db.iter();

	trie_db::trie_visit::<sp_trie::Layout<HashFor<Block>>, _, _, _, _>(iter_kv, &mut root_callback);
	let hash = root_callback.root;
	println!("hash calculated {:?} : {}", hash, now.elapsed().as_millis());

	Ok(())
}



/// Hacky migrate to trigger action on db.
/// Here drop historied state content.
fn delete_historied<Block: BlockT>(db_path: &Path, db_type: DatabaseType) -> sp_blockchain::Result<()> {

	let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(crate::utils::NUM_COLUMNS);
   {
		let option = rocksdb::Options::default();
		 let cfs = rocksdb::DB::list_cf(&option, db_path).unwrap();
		 let db = rocksdb::DB::open_cf(&option, db_path, cfs.clone()).unwrap();
		 for cf in cfs {

			 if let Some(col) = db.cf_handle(&cf) {
				println!("{:?}, {:?}", cf, db.property_int_value_cf(col, "rocksdb.estimate-table-readers-mem"));
				println!("{:?}, {:?}", cf, db.property_int_value_cf(col, "rocksdb.size-all-mem-tables"));
				println!("{:?}, {:?}", cf, db.property_int_value_cf(col, "rocksdb.cur-size-all-mem-tables"));
			 }
		 }
	}

//	delete_non_canonical::<Block>(db_path, db_type)?;
	let path = db_path.to_str()
		.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;
	let db = kvdb_rocksdb::Database::open(&db_config, &path)
		.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?;
	println!("db stats : {:?}", db.get_statistics());
	log::warn!("START MIGRATE");
	log::warn!("start clean");
	let mut tx = db.transaction();
	tx.delete(2, b"tree_mgmt/touched_gc");
	tx.delete(2, b"tree_mgmt/current_gc");
	tx.delete(2, b"tree_mgmt/last_index");
	tx.delete(2, b"tree_mgmt/neutral_elt");
	tx.delete(2, b"tree_mgmt/tree_meta");
	tx.delete_prefix(11, &[]);
	tx.delete_prefix(12, &[]);
	tx.delete_prefix(13, &[]);
	tx.delete_prefix(14, &[]);
	for i in 0u8..255 {
		tx.delete_prefix(11, &[i]);
		tx.delete_prefix(12, &[i]);
		tx.delete_prefix(13, &[i]);
		tx.delete_prefix(14, &[i]);
	}
	tx.put(2, b"tree_mgmt/neutral_elt", &[0].encode()); // only for storing Vec<u8>, if changing type, change this.
	db.write(tx).map_err(db_err)?;
	warn!("end clean");
	warn!("END MIGRATE");

	// Can not use crate::meta_keys::BEST_BLOCK on non archive node: using CANNONICAL,
	// TODO EMCH would need to fetch non_cannonical overlay to complete.
//	let (tree_root, block_hash) = match db.get(crate::utils::COLUMN_META, crate::meta_keys::FINALIZED_BLOCK) {
	let (tree_root, block_hash) = match db.get(crate::utils::COLUMN_META, crate::meta_keys::BEST_BLOCK) {
		Ok(id) => {
			let id = id.unwrap();
			let id = db.get(crate::columns::HEADER, &id).expect("s").map(|b| Block::Header::decode(&mut &b[..]).ok());
			use sp_runtime::traits::Header;
			let id = id.unwrap().expect("d");
			warn!("Head is {:?}", id);
	/*				let mut hash = <HashFor::<Block> as hash_db::Hasher>::Out::default();
				hash.as_mut().copy_from_slice(id.as_slice());*/
			(id.state_root().clone(), id.hash().clone())
		},
		Err(e) => panic!("no best block is bad sign {:?}", e),
	};

/* Using storage db works only on FINALIZED_BLOCK
	let db = Arc::new(db);
	let storage = StorageDb::<Block>(db.clone(), PhantomData);
*/

	let db = Arc::new(db);
	let db_read = db.clone();
	let db = sp_database::as_database(ArcKVDB(db));
	let meta = crate::read_meta::<Block>(&*db, crate::columns::HEADER)?;
	let leaves = crate::LeafSet::<Block::Hash, NumberFor<Block>>::read_from_db(&*db, crate::columns::META, crate::meta_keys::LEAF_PREFIX)?;
	println!("previous leaf set: {:?}", leaves);

	let meta = StateMetaDb(&*db);
	let state_db: StateDb<Block::Hash, Vec<u8>> = StateDb::new(
		PruningMode::Constrained(sc_state_db::Constraints {
			max_blocks: None, // may require info in the future, in fact we should fetch it
			max_mem: None,
		}),
		true, // Rc or not does not matter in this case
		&meta,
	).expect("TODO err");


	let storage = crate::StorageDb::<Block> {
		db: db.clone(),
		state_db,
		prefix_keys: true, // Rc does not really matter here
	};
//		let storage: Arc::<dyn sp_state_machine::Storage<HashFor<Block>>> = Arc::new(storage);
/*		let mut root = Block::Hash::default();
		let trie_backend = sp_state_machine::TrieBackend::new(
			storage,
			tree_root,
		);*/
	let trie = sp_trie::trie_types::TrieDB::new(
		&storage,
		&tree_root,
	).expect("build trie");

	let mut iter = sp_trie::TrieDBIterator::new(&trie).expect("titer");
	let historied_persistence = crate::RocksdbStorage(db_read.clone());
	let mut management = TreeManagement::<
		<HashFor<Block> as hash_db::Hasher>::Out,
		u32,
		u32,
		Vec<u8>,
		crate::TreeManagementPersistenceNoTx,
	>::from_ser(historied_persistence);
	let state = management.latest_state_fork();
	let test = management.get_db_state_for_fork(&Default::default());
	println!("test: {:?}", test);
	management.append_external_state(block_hash.clone(), &state);
	let state = management.latest_state();
	let mut count_tx = 0;
	let mut count = 0;

	let mut kv_db = crate::HistoriedDBMut {
		current_state: state,
		db: db_read.clone(),
	};
	let mut tx = kv_db.transaction();
	let mut longest_key = 0;
	while let Some(Ok((k, v))) = iter.next() {
		longest_key = std::cmp::max(longest_key, k.as_slice().len());
		kv_db.unchecked_new_single(k.as_slice(), v, &mut tx);
		count_tx += 1;
		if count_tx == 1000 {
			count += 1;
			warn!("write a thousand {} {:?}", count, &k[..20]);
			kv_db.write_change_set(tx).expect("write_tx");
			tx = kv_db.transaction();
			count_tx = 0;
		}
	}
	kv_db.write_change_set(tx).expect("write_tx last");
	println!("longest key is {} byte", longest_key);

	let now = Instant::now();
	let mut iter = sp_trie::TrieDBIterator::new(&trie).expect("titer");
	let mut count = 0;
	while let Some(Ok((_k, _v))) = iter.next() {
		count += 1;
	}
	println!("iter trie state of {} in : {}", count, now.elapsed().as_millis());
	let now = Instant::now();

	let current_state = management.get_db_state(&block_hash).expect("just added");
	let historied_db = crate::HistoriedDB {
		current_state,
		db: db_read.clone(),
		do_assert: false,
	};
	let mut count = 0;
	for (_k, _v) in historied_db.iter() {
		count += 1;
	}
	println!("iter kvstate {} state in : {}", count, now.elapsed().as_millis());
	let now = Instant::now();


	let mut root_callback = trie_db::TrieRoot::<HashFor<Block>, _>::default();
	let _state = management.get_db_state(&block_hash).expect("just added");
	let iter_kv = historied_db.iter();

	trie_db::trie_visit::<sp_trie::Layout<HashFor<Block>>, _, _, _, _>(iter_kv, &mut root_callback);
	let hash = root_callback.root;
	println!("hash calcuated {:?} : {}", hash, now.elapsed().as_millis());

	let now = Instant::now();

	let mut try_index = |indexes_conf: &'static[u32], do_write: bool| {
		println!("index {:?}", indexes_conf);
		let indexes_conf = trie_db::partial_db::DepthIndexes::new(indexes_conf);
		let mut indexes = std::collections::BTreeMap::new();
		let mut root_callback = trie_db::TrieRootIndexes::<HashFor<Block>, _, _>::new(&mut indexes, &indexes_conf);
		let iter_kv = historied_db.iter();
		trie_db::trie_visit::<sp_trie::Layout<HashFor<Block>>, _, _, _, _>(iter_kv, &mut root_callback);
		println!("in mem index calculated {:?} : {}", indexes.len(), now.elapsed().as_millis());
		if do_write {
			let now = Instant::now();
			let state = management.latest_state();
			let mut historied_db = crate::HistoriedDBMut {
				current_state: state,
				db: db_read.clone(),
			};
			let mut tx = historied_db.transaction();
			let indexes_check = indexes.clone();
			for (k, v) in indexes {
				historied_db.unchecked_new_single_index(k.as_slice(), crate::encode_index(v), &mut tx);
			}
			historied_db.write_change_set(tx);
			println!("in mem index calculated rocksdb write : {}", now.elapsed().as_millis());

			let now = Instant::now();
			// TODO put depth indexes in trait: here need copy with upgrade client static def.
			let mut result_indexes = std::collections::BTreeMap::new();
			let state = management.get_db_state(&block_hash).expect("just added");
			let historied_db = 	crate::HistoriedDB {
				current_state: state,
				db: db_read.clone(),
				do_assert: false,
			};
			let root_new: <HashFor<Block> as hash_db::Hasher>::Out = {
				let mut cb = trie_db::TrieRootIndexes::<HashFor<Block>, _, _>::new(&mut result_indexes, &indexes_conf);
				let iter = trie_db::partial_db::RootIndexIterator::new(
					&historied_db,
					//&historied_db,
					&indexes_check,
					&indexes_conf,
					std::iter::empty(),
					Vec::new(),
				);
				trie_db::trie_visit_with_indexes::<sp_trie::Layout<HashFor<Block>>, _, _, _>(iter, &mut cb);
				cb.root.unwrap_or(Default::default())
			};

			println!("check root with index {:?} in : {} with {:?}", Some(root_new) == hash, now.elapsed().as_millis(), result_indexes.len());

		}
	};
	/*
	// last checked max length was 120 so 240 index
	let all = & 
[1u32, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239];
	let every_two = &
[2u32, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134, 136, 138, 140, 142, 144, 146, 148, 150, 152, 154, 156, 158, 160, 162, 164, 166, 168, 170, 172, 174, 176, 178, 180, 182, 184, 186, 188, 190, 192, 194, 196, 198, 200, 202, 204, 206, 208, 210, 212, 214, 216, 218, 220, 222, 224, 226, 228, 230, 232, 234, 236, 238];

	let every_three = &
[3u32, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 48, 51, 54, 57, 60, 63, 66, 69, 72, 75, 78, 81, 84, 87, 90, 93, 96, 99, 102, 105, 108, 111, 114, 117, 120, 123, 126, 129, 132, 135, 138, 141, 144, 147, 150, 153, 156, 159, 162, 165, 168, 171, 174, 177, 180, 183, 186, 189, 192, 195, 198, 201, 204, 207, 210, 213, 216, 219, 222, 225, 228, 231, 234, 237];

	let every_four = &
[4u32, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96, 100, 104, 108, 112, 116, 120, 124, 128, 132, 136, 140, 144, 148, 152, 156, 160, 164, 168, 172, 176, 180, 184, 188, 192, 196, 200, 204, 208, 212, 216, 220, 224, 228, 232, 236];

	let every_five = &
[5u32, 10, 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120, 125, 130, 135, 140, 145, 150, 155, 160, 165, 170, 175, 180, 185, 190, 195, 200, 205, 210, 215, 220, 225, 230, 235];
	let every_ten = &
[10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 160, 170, 180, 190, 200, 210, 220, 230];


	try_index(all, false);
	try_index(every_two, false);
	try_index(every_three, false);
	try_index(every_four, false);
	try_index(every_five, false);
	try_index(every_ten, false);
	*/
	let every_five = &
[5u32, 10, 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120, 125, 130, 135, 140, 145, 150, 155, 160, 165, 170, 175, 180, 185, 190, 195, 200, 205, 210, 215, 220, 225, 230, 235];
/*	try_index(&[8], false);
	try_index(&[16], false);
	try_index(&[64], false);
	try_index(&[96], false);
	try_index(&[128], false);
	try_index(&[230], false);
	try_index(&[80], true);*/

//	try_index(&[32, 64, 96], true);
	try_index(every_five, true);
	Ok(())
}

struct ArcKVDB<D: KeyValueDB>(Arc<D>);

impl<D: KeyValueDB> parity_util_mem::MallocSizeOf for ArcKVDB<D> {
	fn size_of(&self, ops: &mut parity_util_mem::MallocSizeOfOps) -> usize {
		self.0.size_of(ops)
	}
}

impl<D: KeyValueDB> KeyValueDB for ArcKVDB<D> {
	fn transaction(&self) -> kvdb::DBTransaction {
		self.0.transaction()
	}

	fn get(&self, col: u32, key: &[u8]) -> io::Result<Option<Vec<u8>>> {
		self.0.get(col, key)
	}

	fn get_by_prefix(&self, col: u32, prefix: &[u8]) -> Option<Box<[u8]>> {
		self.0.get_by_prefix(col, prefix)
	}

	fn write(&self, transaction: kvdb::DBTransaction) -> io::Result<()> {
		self.0.write(transaction)
	}

	fn iter<'a>(&'a self, col: u32) -> Box<dyn Iterator<Item = (Box<[u8]>, Box<[u8]>)> + 'a> {
		self.0.iter(col)
	}

	fn iter_with_prefix<'a>(
		&'a self,
		col: u32,
		prefix: &'a [u8],
	) -> Box<dyn Iterator<Item = (Box<[u8]>, Box<[u8]>)> + 'a> {
		self.0.iter_with_prefix(col, prefix)
	}

	fn restore(&self, new_db: &str) -> io::Result<()> {
		self.0.restore(new_db)
	}
}

struct StorageDb<Block>(Arc<kvdb_rocksdb::Database>, PhantomData<Block>);

impl<Block: BlockT> hash_db::HashDBRef<HashFor<Block>, Vec<u8>> for StorageDb<Block> {
	fn contains(&self, key: &<HashFor::<Block> as hash_db::Hasher>::Out, prefix: hash_db::Prefix) -> bool {
		self.get(key, prefix).is_some()
	}

	fn get(&self, key: &<HashFor::<Block> as hash_db::Hasher>::Out, prefix: hash_db::Prefix) -> Option<sp_trie::DBValue> {
		let key = sp_trie::prefixed_key::<HashFor<Block>>(key, prefix);
		self.0.get(crate::columns::STATE, key.as_slice()).expect("bad script")
	}
}

impl<Block: BlockT> hash_db::HashDBRef<HashFor<Block>, Vec<u8>> for crate::StorageDb<Block> {
	fn contains(&self, key: &<HashFor::<Block> as hash_db::Hasher>::Out, prefix: hash_db::Prefix) -> bool {
		self.get(key, prefix).is_some()
	}

	fn get(&self, key: &<HashFor::<Block> as hash_db::Hasher>::Out, prefix: hash_db::Prefix) -> Option<sp_trie::DBValue> {
		if self.prefix_keys {
			let key = sp_trie::prefixed_key::<HashFor<Block>>(key, prefix);
			self.state_db.get(&key, self)
		} else {
			self.state_db.get(key.as_ref(), self)
		}
		.unwrap()
	}
}


impl<Block: BlockT> sp_state_machine::Storage<HashFor<Block>> for StorageDb<Block> {
	fn get(&self, key: &Block::Hash, prefix: hash_db::Prefix) -> Result<Option<sp_trie::DBValue>, String> {
		let key = sp_trie::prefixed_key::<HashFor<Block>>(key, prefix);
		Ok(self.0.get(crate::columns::STATE_META, key.as_slice()).expect("bad script"))
	}
}


/// Reads current database version from the file at given path.
/// If the file does not exist returns 0.
fn current_version(path: &Path) -> sp_blockchain::Result<u32> {
	let unknown_version_err = || sp_blockchain::Error::Backend("Unknown database version".into());

	match fs::File::open(version_file_path(path)) {
		Err(ref err) if err.kind() == ErrorKind::NotFound => {
			warn!("version file not found");
			Ok(0)
		},
		Err(e) => {
			warn!("version file error: {:?}", e);
			Err(unknown_version_err())
		},
		Ok(mut file) => {
			let mut s = String::new();
			file.read_to_string(&mut s).map_err(|e| {
				warn!("version file error: {:?}", e);
				unknown_version_err()
			})?;
			warn!("version db : {:?}", s);
			u32::from_str_radix(&s, 10).map_err(|_| unknown_version_err())
		},
	}
}

/// Maps database error to client error
fn db_err(err: std::io::Error) -> sp_blockchain::Error {
	sp_blockchain::Error::Backend(format!("{}", err))
}

/// Writes current database version to the file.
/// Creates a new file if the version file does not exist yet.
fn update_version(path: &Path) -> sp_blockchain::Result<()> {
	fs::create_dir_all(path).map_err(db_err)?;
	let mut file = fs::File::create(version_file_path(path)).map_err(db_err)?;
	file.write_all(format!("{}", CURRENT_VERSION).as_bytes()).map_err(db_err)?;
	Ok(())
}

/// Returns the version file path.
fn version_file_path(path: &Path) -> PathBuf {
	let mut file_path = path.to_owned();
	file_path.push(VERSION_FILE_NAME);
	file_path
}

#[cfg(test)]
mod tests {
	use sc_state_db::PruningMode;
	use crate::{DatabaseSettings, DatabaseSettingsSrc};
	use crate::tests::Block;
	use super::*;

	fn create_db(db_path: &Path, version: Option<u32>) {
		if let Some(version) = version {
			fs::create_dir_all(db_path).unwrap();
			let mut file = fs::File::create(version_file_path(db_path)).unwrap();
			file.write_all(format!("{}", version).as_bytes()).unwrap();
		}
	}

	fn open_database(db_path: &Path) -> sp_blockchain::Result<()> {
		crate::utils::open_database::<Block>(&DatabaseSettings {
			state_cache_size: 0,
			state_cache_child_ratio: None,
			pruning: PruningMode::ArchiveAll,
			source: DatabaseSettingsSrc::RocksDb { path: db_path.to_owned(), cache_size: 128 },
			experimental_cache: Default::default(),
		}, DatabaseType::Full).map(|_| ())
	}

	#[test]
	fn downgrade_never_happens() {
		let db_dir = tempfile::TempDir::new().unwrap();
		create_db(db_dir.path(), Some(CURRENT_VERSION + 1));
		assert!(open_database(db_dir.path()).is_err());
	}

	#[test]
	fn open_empty_database_works() {
		let db_dir = tempfile::TempDir::new().unwrap();
		open_database(db_dir.path()).unwrap();
		open_database(db_dir.path()).unwrap();
		assert_eq!(current_version(db_dir.path()).unwrap(), CURRENT_VERSION);
	}
}
