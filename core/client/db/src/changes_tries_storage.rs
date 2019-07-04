// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! DB-backed changes tries storage.

use std::collections::HashMap;
use std::sync::Arc;
use kvdb::{KeyValueDB, DBTransaction};
use parity_codec::Encode;
use parking_lot::{RwLock, RwLockWriteGuard};
use client::error::{Error as ClientError, Result as ClientResult};
use trie::MemoryDB;
use client::backend::PrunableStateChangesTrieStorage;
use client::blockchain::{Cache, well_known_cache_keys};
use parity_codec::Decode;
use primitives::{H256, Blake2Hasher, ChangesTrieConfiguration, convert_hash};
use runtime_primitives::traits::{
	Block as BlockT, Header as HeaderT, NumberFor, One,
};
use runtime_primitives::generic::{BlockId, DigestItem, ChangesTrieSignal};
use state_machine::DBValue;
use crate::utils::{self, Meta};
use crate::cache::{DbCacheSync, DbCache, DbCacheTransactionOps, ComplexBlockId, EntryType as CacheEntryType};

/// Extract new changes trie configuration (if available) from the header.
pub fn extract_new_configuration<Header: HeaderT>(header: &Header) -> Option<&Option<ChangesTrieConfiguration>> {
	header.digest()
		.log(DigestItem::as_changes_trie_signal)
		.and_then(ChangesTrieSignal::as_new_configuration)
}

/// Opaque configuration cache transaction.
pub struct DbChangesTrieStorageTransaction<'a, Block: BlockT> {
	/// Lock needs to be held between commit and post_commit calls.
	lock: RwLockWriteGuard<'a, DbCache<Block>>,
	/// Cache operations that needs to be performed once tx is committed.
	ops: DbCacheTransactionOps<Block>,
}

/// Changes tries storage.
///
/// Stores all tries in separate DB column.
pub struct DbChangesTrieStorage<Block: BlockT> {
	db: Arc<dyn KeyValueDB>,
	changes_tries_column: Option<u32>,
	key_lookup_column: Option<u32>,
	header_column: Option<u32>,
	meta: Arc<RwLock<Meta<NumberFor<Block>, Block::Hash>>>,
	min_blocks_to_keep: Option<u32>,
	cache: DbCacheSync<Block>,
}

impl<Block: BlockT<Hash=H256>> DbChangesTrieStorage<Block> {
	/// Create new changes trie storage.
	pub fn new(
		db: Arc<dyn KeyValueDB>,
		changes_tries_column: Option<u32>,
		key_lookup_column: Option<u32>,
		header_column: Option<u32>,
		cache_column: Option<u32>,
		meta: Arc<RwLock<Meta<NumberFor<Block>, Block::Hash>>>,
		min_blocks_to_keep: Option<u32>,
	) -> Self {
		let (finalized_hash, finalized_number, genesis_hash) = {
			let meta = meta.read();
			(meta.finalized_hash, meta.finalized_number, meta.genesis_hash)
		};
		Self {
			db: db.clone(),
			changes_tries_column,
			key_lookup_column,
			header_column,
			meta,
			min_blocks_to_keep,
			cache: DbCacheSync(RwLock::new(DbCache::new(
				db.clone(),
				key_lookup_column,
				header_column,
				cache_column,
				genesis_hash,
				ComplexBlockId::new(finalized_hash, finalized_number),
			))),
		}
	}

	/// Commit new changes trie.
	pub fn commit(
		&self,
		tx: &mut DBTransaction,
		mut changes_trie: MemoryDB<Blake2Hasher>,
		parent_block: ComplexBlockId<Block>,
		block: ComplexBlockId<Block>,
		finalized: bool,
		new_configuration: Option<Option<ChangesTrieConfiguration>>,
	) -> ClientResult<Option<DbChangesTrieStorageTransaction<Block>>> {
		// insert changes trie, associated with block, into DB
		for (key, (val, _)) in changes_trie.drain() {
			tx.put(self.changes_tries_column, &key[..], &val);
		}

		// if configuration has been changed, we need to update configuration cache as well
		let new_configuration = match new_configuration {
			Some(new_configuration) => new_configuration,
			None => return Ok(None),
		};

		let mut cache_at = HashMap::new();
		cache_at.insert(well_known_cache_keys::CHANGES_TRIE_CONFIG, new_configuration.encode());

		let mut cache = self.cache.0.write();
		let cache_ops = cache.transaction(tx)
			.on_block_insert(
				parent_block,
				block,
				cache_at,
				if finalized { CacheEntryType::Final } else { CacheEntryType::NonFinal },
			)?
			.into_ops();
		Ok(Some(DbChangesTrieStorageTransaction {
			lock: cache,
			ops: cache_ops,
		}))
	}

	/// When transaction has been committed.
	pub fn post_commit(&self, tx: Option<DbChangesTrieStorageTransaction<Block>>) {
		if let Some(mut tx) = tx {
			tx.lock.commit(tx.ops);
		}
	}

	/// Prune obsolete changes tries.
	pub fn prune(
		&self,
		tx: &mut DBTransaction,
		parent_hash: Block::Hash,
		block_hash: Block::Hash,
		block_num: NumberFor<Block>,
	) -> ClientResult<()> {
		// never prune on archive nodes
		let min_blocks_to_keep = match self.min_blocks_to_keep {
			Some(min_blocks_to_keep) => min_blocks_to_keep,
			None => return Ok(()),
		};

		// prune changes tries that are created using newest configuration
		let (activation_num, _, newest_config) = self.configuration_at(&BlockId::Hash(parent_hash))?;
		if let Some(config) = newest_config {
			state_machine::prune_changes_tries(
				activation_num,
				&config,
				&*self,
				min_blocks_to_keep.into(),
				&state_machine::ChangesTrieAnchorBlockId {
					hash: convert_hash(&block_hash),
					number: block_num,
				},
				|node| tx.delete(self.changes_tries_column, node.as_ref()));
		}

		// TODO: prune tries that were created using previous configurations

		Ok(())
	}
}

impl<Block> client::backend::PrunableStateChangesTrieStorage<Block, Blake2Hasher>
	for DbChangesTrieStorage<Block>
where
	Block: BlockT<Hash=H256>,
{
	fn storage(&self) -> &dyn state_machine::ChangesTrieStorage<Blake2Hasher, NumberFor<Block>> {
		self
	}

	fn configuration_at(
		&self,
		at: &BlockId<Block>,
	) -> ClientResult<(NumberFor<Block>, Block::Hash, Option<ChangesTrieConfiguration>)> {
		self.cache
			.get_at(&well_known_cache_keys::CHANGES_TRIE_CONFIG, at)
			.and_then(|(number, hash, encoded)| Decode::decode(&mut &encoded[..]).map(|config| (number, hash, config)))
			.ok_or_else(|| ClientError::ErrorReadingChangesTriesConfig)
	}

	fn oldest_changes_trie_block(
		&self,
		config_activation_block: NumberFor<Block>,
		config: ChangesTrieConfiguration,
		best_finalized_block: NumberFor<Block>,
	) -> NumberFor<Block> {
		match self.min_blocks_to_keep {
			Some(min_blocks_to_keep) => state_machine::oldest_non_pruned_changes_trie(
				config_activation_block,
				&config,
				min_blocks_to_keep.into(),
				best_finalized_block,
			),
			None => One::one(),
		}
	}
}

impl<Block> state_machine::ChangesTrieRootsStorage<Blake2Hasher, NumberFor<Block>>
	for DbChangesTrieStorage<Block>
where
	Block: BlockT<Hash=H256>,
{
	fn build_anchor(
		&self,
		hash: H256,
	) -> Result<state_machine::ChangesTrieAnchorBlockId<H256, NumberFor<Block>>, String> {
		utils::read_header::<Block>(&*self.db, self.key_lookup_column, self.header_column, BlockId::Hash(hash))
			.map_err(|e| e.to_string())
			.and_then(|maybe_header| maybe_header.map(|header|
				state_machine::ChangesTrieAnchorBlockId {
					hash,
					number: *header.number(),
				}
			).ok_or_else(|| format!("Unknown header: {}", hash)))
	}

	fn root(
		&self,
		anchor: &state_machine::ChangesTrieAnchorBlockId<H256, NumberFor<Block>>,
		block: NumberFor<Block>,
	) -> Result<Option<H256>, String> {
		// check API requirement: we can't get NEXT block(s) based on anchor
		if block > anchor.number {
			return Err(format!("Can't get changes trie root at {} using anchor at {}", block, anchor.number));
		}

		// we need to get hash of the block to resolve changes trie root
		let block_id = if block <= self.meta.read().finalized_number {
			// if block is finalized, we could just read canonical hash
			BlockId::Number(block)
		} else {
			// the block is not finalized
			let mut current_num = anchor.number;
			let mut current_hash: Block::Hash = convert_hash(&anchor.hash);
			let maybe_anchor_header: Block::Header = utils::require_header::<Block>(
				&*self.db, self.key_lookup_column, self.header_column, BlockId::Number(current_num)
			).map_err(|e| e.to_string())?;
			if maybe_anchor_header.hash() == current_hash {
				// if anchor is canonicalized, then the block is also canonicalized
				BlockId::Number(block)
			} else {
				// else (block is not finalized + anchor is not canonicalized):
				// => we should find the required block hash by traversing
				// back from the anchor to the block with given number
				while current_num != block {
					let current_header: Block::Header = utils::require_header::<Block>(
						&*self.db, self.key_lookup_column, self.header_column, BlockId::Hash(current_hash)
					).map_err(|e| e.to_string())?;

					current_hash = *current_header.parent_hash();
					current_num = current_num - One::one();
				}

				BlockId::Hash(current_hash)
			}
		};

		Ok(utils::require_header::<Block>(&*self.db, self.key_lookup_column, self.header_column, block_id)
			.map_err(|e| e.to_string())?
			.digest().log(DigestItem::as_changes_trie_root)
			.map(|root| H256::from_slice(root.as_ref())))
	}
}

impl<Block> state_machine::ChangesTrieStorage<Blake2Hasher, NumberFor<Block>>
	for DbChangesTrieStorage<Block>
where
	Block: BlockT<Hash=H256>,
{
	fn as_roots_storage(&self) -> &dyn state_machine::ChangesTrieRootsStorage<Blake2Hasher, NumberFor<Block>> {
		self
	}

	fn get(&self, key: &H256, _prefix: &[u8]) -> Result<Option<DBValue>, String> {
		self.db.get(self.changes_tries_column, &key[..])
			.map_err(|err| format!("{}", err))
	}
}

#[cfg(test)]
mod tests {
	use client::backend::{Backend as ClientBackend, NewBlockState, BlockImportOperation};
	use client::blockchain::HeaderBackend as BlockchainHeaderBackend;
	use runtime_primitives::testing::Header;
	use runtime_primitives::traits::{Hash, BlakeTwo256};
	use state_machine::{ChangesTrieRootsStorage, ChangesTrieStorage};
	use crate::Backend;
	use crate::tests::{Block, insert_header, prepare_changes};
	use super::*;

	#[test]
	fn changes_trie_storage_works() {
		let backend = Backend::<Block>::new_test(1000, 100);
		backend.changes_tries_storage.meta.write().finalized_number = 1000;

		let check_changes = |backend: &Backend<Block>, block: u64, changes: Vec<(Vec<u8>, Vec<u8>)>| {
			let (changes_root, mut changes_trie_update) = prepare_changes(changes);
			let anchor = state_machine::ChangesTrieAnchorBlockId {
				hash: backend.blockchain().header(BlockId::Number(block)).unwrap().unwrap().hash(),
				number: block
			};
			assert_eq!(backend.changes_tries_storage.root(&anchor, block), Ok(Some(changes_root)));

			let storage = backend.changes_tries_storage.storage();
			for (key, (val, _)) in changes_trie_update.drain() {
				assert_eq!(storage.get(&key, &[]), Ok(Some(val)));
			}
		};

		let changes0 = vec![(b"key_at_0".to_vec(), b"val_at_0".to_vec())];
		let changes1 = vec![
			(b"key_at_1".to_vec(), b"val_at_1".to_vec()),
			(b"another_key_at_1".to_vec(), b"another_val_at_1".to_vec()),
		];
		let changes2 = vec![(b"key_at_2".to_vec(), b"val_at_2".to_vec())];

		let block0 = insert_header(&backend, 0, Default::default(), changes0.clone(), Default::default());
		let block1 = insert_header(&backend, 1, block0, changes1.clone(), Default::default());
		let _ = insert_header(&backend, 2, block1, changes2.clone(), Default::default());

		// check that the storage contains tries for all blocks
		check_changes(&backend, 0, changes0);
		check_changes(&backend, 1, changes1);
		check_changes(&backend, 2, changes2);
	}

	#[test]
	fn changes_trie_storage_works_with_forks() {
		let backend = Backend::<Block>::new_test(1000, 100);

		let changes0 = vec![(b"k0".to_vec(), b"v0".to_vec())];
		let changes1 = vec![(b"k1".to_vec(), b"v1".to_vec())];
		let changes2 = vec![(b"k2".to_vec(), b"v2".to_vec())];
		let block0 = insert_header(&backend, 0, Default::default(), changes0.clone(), Default::default());
		let block1 = insert_header(&backend, 1, block0, changes1.clone(), Default::default());
		let block2 = insert_header(&backend, 2, block1, changes2.clone(), Default::default());

		let changes2_1_0 = vec![(b"k3".to_vec(), b"v3".to_vec())];
		let changes2_1_1 = vec![(b"k4".to_vec(), b"v4".to_vec())];
		let block2_1_0 = insert_header(&backend, 3, block2, changes2_1_0.clone(), Default::default());
		let block2_1_1 = insert_header(&backend, 4, block2_1_0, changes2_1_1.clone(), Default::default());

		let changes2_2_0 = vec![(b"k5".to_vec(), b"v5".to_vec())];
		let changes2_2_1 = vec![(b"k6".to_vec(), b"v6".to_vec())];
		let block2_2_0 = insert_header(&backend, 3, block2, changes2_2_0.clone(), Default::default());
		let block2_2_1 = insert_header(&backend, 4, block2_2_0, changes2_2_1.clone(), Default::default());

		// finalize block1
		backend.changes_tries_storage.meta.write().finalized_number = 1;

		// branch1: when asking for finalized block hash
		let (changes1_root, _) = prepare_changes(changes1);
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: block2_1_1, number: 4 };
		assert_eq!(backend.changes_tries_storage.root(&anchor, 1), Ok(Some(changes1_root)));

		// branch2: when asking for finalized block hash
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: block2_2_1, number: 4 };
		assert_eq!(backend.changes_tries_storage.root(&anchor, 1), Ok(Some(changes1_root)));

		// branch1: when asking for non-finalized block hash (search by traversal)
		let (changes2_1_0_root, _) = prepare_changes(changes2_1_0);
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: block2_1_1, number: 4 };
		assert_eq!(backend.changes_tries_storage.root(&anchor, 3), Ok(Some(changes2_1_0_root)));

		// branch2: when asking for non-finalized block hash (search using canonicalized hint)
		let (changes2_2_0_root, _) = prepare_changes(changes2_2_0);
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: block2_2_1, number: 4 };
		assert_eq!(backend.changes_tries_storage.root(&anchor, 3), Ok(Some(changes2_2_0_root)));

		// finalize first block of branch2 (block2_2_0)
		backend.changes_tries_storage.meta.write().finalized_number = 3;

		// branch2: when asking for finalized block of this branch
		assert_eq!(backend.changes_tries_storage.root(&anchor, 3), Ok(Some(changes2_2_0_root)));

		// branch1: when asking for finalized block of other branch
		// => result is incorrect (returned for the block of branch1), but this is expected,
		// because the other fork is abandoned (forked before finalized header)
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: block2_1_1, number: 4 };
		assert_eq!(backend.changes_tries_storage.root(&anchor, 3), Ok(Some(changes2_2_0_root)));
	}

	#[test]
	fn changes_tries_with_digest_are_pruned_on_finalization() {
		let mut backend = Backend::<Block>::new_test(1000, 100);
		let config = ChangesTrieConfiguration {
			digest_interval: 2,
			digest_levels: 2,
		};

		backend.changes_tries_storage.min_blocks_to_keep = Some(8);

		// insert some blocks
		let mut blocks = Vec::new();
		let mut last_block = Default::default();
		for i in 0u64..14u64 {
			let key = i.to_le_bytes().to_vec();
			let val = key.clone();
			last_block = insert_header(
				&backend,
				i,
				last_block,
				vec![(key, val)],
				Default::default(),
			);
			blocks.push(last_block);
		}
		backend.changes_tries_storage.meta.write().finalized_number = 13;
		backend.changes_tries_storage.cache.initialize(
			&well_known_cache_keys::CHANGES_TRIE_CONFIG,
			Some(config).encode(),
		).unwrap();

		// check that roots of all tries are in the columns::CHANGES_TRIE
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: blocks[13], number: 13 };
		fn read_changes_trie_root(backend: &Backend<Block>, num: u64) -> H256 {
			backend.blockchain().header(BlockId::Number(num)).unwrap().unwrap().digest().logs().iter()
				.find(|i| i.as_changes_trie_root().is_some()).unwrap().as_changes_trie_root().unwrap().clone()
		}
		let root1 = read_changes_trie_root(&backend, 1);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 1).unwrap(), Some(root1));
		let root2 = read_changes_trie_root(&backend, 2);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 2).unwrap(), Some(root2));
		let root3 = read_changes_trie_root(&backend, 3);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 3).unwrap(), Some(root3));
		let root4 = read_changes_trie_root(&backend, 4);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 4).unwrap(), Some(root4));
		let root5 = read_changes_trie_root(&backend, 5);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 5).unwrap(), Some(root5));
		let root6 = read_changes_trie_root(&backend, 6);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 6).unwrap(), Some(root6));
		let root7 = read_changes_trie_root(&backend, 7);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 7).unwrap(), Some(root7));
		let root8 = read_changes_trie_root(&backend, 8);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 8).unwrap(), Some(root8));
		let root9 = read_changes_trie_root(&backend, 9);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 9).unwrap(), Some(root9));
		let root10 = read_changes_trie_root(&backend, 10);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 10).unwrap(), Some(root10));
		let root11 = read_changes_trie_root(&backend, 11);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 11).unwrap(), Some(root11));
		let root12 = read_changes_trie_root(&backend, 12);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 12).unwrap(), Some(root12));

		// now simulate finalization of block#12, causing prune of tries at #1..#4
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(&mut tx, blocks[0], Default::default(), 12).unwrap();
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root1, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root2, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root3, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root4, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root5, &[]).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root6, &[]).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root7, &[]).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root8, &[]).unwrap().is_some());

		// now simulate finalization of block#16, causing prune of tries at #5..#8
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(&mut tx, blocks[0], Default::default(), 16).unwrap();
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root5, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root6, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root7, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root8, &[]).unwrap().is_none());

		// now "change" pruning mode to archive && simulate finalization of block#20
		// => no changes tries are pruned, because we never prune in archive mode
		backend.changes_tries_storage.min_blocks_to_keep = None;
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(&mut tx, blocks[0], Default::default(), 20).unwrap();
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root9, &[]).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root10, &[]).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root11, &[]).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root12, &[]).unwrap().is_some());
	}

	#[test]
	fn changes_tries_without_digest_are_pruned_on_finalization() {
		let mut backend = Backend::<Block>::new_test(1000, 100);
		let config = ChangesTrieConfiguration {
			digest_interval: 0,
			digest_levels: 0,
		};

		backend.changes_tries_storage.min_blocks_to_keep = Some(4);

		// insert some blocks
		let mut blocks = Vec::new();
		let mut last_block = Default::default();
		for i in 0u64..7u64 {
			let key = i.to_le_bytes().to_vec();
			let val = key.clone();
			last_block = insert_header(
				&backend,
				i,
				last_block,
				vec![(key, val)],
				Default::default(),
			);
			blocks.push(last_block);
		}
		backend.changes_tries_storage.cache.initialize(
			&well_known_cache_keys::CHANGES_TRIE_CONFIG,
			Some(config).encode(),
		).unwrap();

		// check that roots of all tries are in the columns::CHANGES_TRIE
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: blocks[6], number: 6 };
		fn read_changes_trie_root(backend: &Backend<Block>, num: u64) -> H256 {
			backend.blockchain().header(BlockId::Number(num)).unwrap().unwrap().digest().logs().iter()
				.find(|i| i.as_changes_trie_root().is_some()).unwrap().as_changes_trie_root().unwrap().clone()
		}

		let root1 = read_changes_trie_root(&backend, 1);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 1).unwrap(), Some(root1));
		let root2 = read_changes_trie_root(&backend, 2);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 2).unwrap(), Some(root2));
		let root3 = read_changes_trie_root(&backend, 3);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 3).unwrap(), Some(root3));
		let root4 = read_changes_trie_root(&backend, 4);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 4).unwrap(), Some(root4));
		let root5 = read_changes_trie_root(&backend, 5);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 5).unwrap(), Some(root5));
		let root6 = read_changes_trie_root(&backend, 6);
		assert_eq!(backend.changes_tries_storage.root(&anchor, 6).unwrap(), Some(root6));

		// now simulate finalization of block#5, causing prune of trie at #1
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(&mut tx, blocks[1], blocks[5], 5).unwrap();
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root1, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root2, &[]).unwrap().is_some());

		// now simulate finalization of block#6, causing prune of tries at #2
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(&mut tx, blocks[1], blocks[6], 6).unwrap();
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root2, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root3, &[]).unwrap().is_some());
	}

	#[test]
	fn changes_tries_configuration_is_updated_on_block_insert() {
		fn insert_header_with_configuration_change(
			backend: &Backend<Block>,
			number: u64,
			parent_hash: H256,
			changes: Vec<(Vec<u8>, Vec<u8>)>,
			new_configuration: Option<ChangesTrieConfiguration>,
		) -> H256 {
			use runtime_primitives::testing::Digest;

			let (changes_root, changes_trie_update) = prepare_changes(changes);
			let digest = Digest {
				logs: vec![
					DigestItem::ChangesTrieRoot(changes_root),
					DigestItem::ChangesTrieSignal(ChangesTrieSignal::NewConfiguration(new_configuration)),
				],
			};
			let header = Header {
				number,
				parent_hash,
				state_root: BlakeTwo256::trie_root::<_, &[u8], &[u8]>(Vec::new()),
				digest,
				extrinsics_root: Default::default(),
			};
			let header_hash = header.hash();

			let block_id = if number == 0 {
				BlockId::Hash(Default::default())
			} else {
				BlockId::Number(number - 1)
			};
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, block_id).unwrap();
			op.set_block_data(header, None, None, NewBlockState::Best).unwrap();
			op.update_changes_trie(changes_trie_update).unwrap();
			backend.commit_operation(op).unwrap();

			header_hash
		}

		let backend = Backend::<Block>::new_test(1000, 100);

		// configurations at blocks
		let config_at_1 = Some(ChangesTrieConfiguration {
			digest_interval: 4,
			digest_levels: 2,
		});
		let config_at_3 = Some(ChangesTrieConfiguration {
			digest_interval: 8,
			digest_levels: 1,
		});
		let config_at_5 = None;
		let config_at_7 = Some(ChangesTrieConfiguration {
			digest_interval: 8,
			digest_levels: 1,
		});

		// insert some blocks
		let block0 = insert_header(&backend, 0, Default::default(), Vec::new(), Default::default());
		let block1 = insert_header_with_configuration_change(&backend, 1, block0, Vec::new(), config_at_1.clone());
		let block2 = insert_header(&backend, 2, block1, Vec::new(), Default::default());
		let block3 = insert_header_with_configuration_change(&backend, 3, block2, Vec::new(), config_at_3.clone());
		let block4 = insert_header(&backend, 4, block3, Vec::new(), Default::default());
		let block5 = insert_header_with_configuration_change(&backend, 5, block4, Vec::new(), config_at_5.clone());
		let block6 = insert_header(&backend, 6, block5, Vec::new(), Default::default());
		let block7 = insert_header_with_configuration_change(&backend, 7, block6, Vec::new(), config_at_7.clone());

		// test configuration cache
		let storage = &backend.changes_tries_storage;
		assert_eq!(
			storage.configuration_at(&BlockId::Hash(block1)).unwrap().2,
			config_at_1.clone(),
		);
		assert_eq!(
			storage.configuration_at(&BlockId::Hash(block2)).unwrap().2,
			config_at_1.clone(),
		);
		assert_eq!(
			storage.configuration_at(&BlockId::Hash(block3)).unwrap().2,
			config_at_3.clone(),
		);
		assert_eq!(
			storage.configuration_at(&BlockId::Hash(block4)).unwrap().2,
			config_at_3.clone(),
		);
		assert_eq!(
			storage.configuration_at(&BlockId::Hash(block5)).unwrap().2,
			config_at_5.clone(),
		);
		assert_eq!(
			storage.configuration_at(&BlockId::Hash(block6)).unwrap().2,
			config_at_5.clone(),
		);
		assert_eq!(
			storage.configuration_at(&BlockId::Hash(block7)).unwrap().2,
			config_at_7.clone(),
		);
	}
}
