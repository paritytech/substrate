// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! RocksDB-based light client blockchain storage.

use std::{sync::Arc, collections::HashMap};
use parking_lot::RwLock;

use kvdb::{KeyValueDB, DBTransaction};

use client::backend::{AuxStore, NewBlockState};
use client::blockchain::{BlockStatus, Cache as BlockchainCache,
	HeaderBackend as BlockchainHeaderBackend, Info as BlockchainInfo};
use client::cht;
use client::leaves::{LeafSet, FinalizationDisplaced};
use client::error::{Error as ClientError, Result as ClientResult};
use client::light::blockchain::Storage as LightBlockchainStorage;
use parity_codec::{Decode, Encode};
use primitives::Blake2Hasher;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT,
	Zero, One, As, NumberFor, Digest, DigestItem};
use consensus_common::well_known_cache_keys;
use crate::cache::{DbCacheSync, DbCache, ComplexBlockId};
use crate::utils::{self, meta_keys, Meta, db_err, open_database,
	read_db, block_id_to_lookup_key, read_meta};
use crate::DatabaseSettings;
use log::{trace, warn, debug};

pub(crate) mod columns {
	pub const META: Option<u32> = crate::utils::COLUMN_META;
	pub const KEY_LOOKUP: Option<u32> = Some(1);
	pub const HEADER: Option<u32> = Some(2);
	pub const CACHE: Option<u32> = Some(3);
	pub const CHT: Option<u32> = Some(4);
	pub const AUX: Option<u32> = Some(5);
}

/// Prefix for headers CHT.
const HEADER_CHT_PREFIX: u8 = 0;
/// Prefix for changes tries roots CHT.
const CHANGES_TRIE_CHT_PREFIX: u8 = 1;

/// Light blockchain storage. Stores most recent headers + CHTs for older headers.
/// Locks order: meta, leaves, cache.
pub struct LightStorage<Block: BlockT> {
	db: Arc<KeyValueDB>,
	meta: RwLock<Meta<NumberFor<Block>, Block::Hash>>,
	leaves: RwLock<LeafSet<Block::Hash, NumberFor<Block>>>,
	cache: Arc<DbCacheSync<Block>>,
}

impl<Block> LightStorage<Block>
	where
		Block: BlockT,
{
	/// Create new storage with given settings.
	pub fn new(config: DatabaseSettings) -> ClientResult<Self> {
		let db = open_database(&config, columns::META, "light")?;

		Self::from_kvdb(db as Arc<_>)
	}

	#[cfg(any(test, feature = "test-helpers"))]
	pub fn new_test() -> Self {
		use utils::NUM_COLUMNS;

		let db = Arc::new(::kvdb_memorydb::create(NUM_COLUMNS));

		Self::from_kvdb(db as Arc<_>).expect("failed to create test-db")
	}

	fn from_kvdb(db: Arc<KeyValueDB>) -> ClientResult<Self> {
		let meta = read_meta::<Block>(&*db, columns::META, columns::HEADER)?;
		let leaves = LeafSet::read_from_db(&*db, columns::META, meta_keys::LEAF_PREFIX)?;
		let cache = DbCache::new(
			db.clone(),
			columns::KEY_LOOKUP,
			columns::HEADER,
			columns::CACHE,
			ComplexBlockId::new(meta.finalized_hash, meta.finalized_number),
		);

		Ok(LightStorage {
			db,
			meta: RwLock::new(meta),
			cache: Arc::new(DbCacheSync(RwLock::new(cache))),
			leaves: RwLock::new(leaves),
		})
	}

	#[cfg(test)]
	pub(crate) fn cache(&self) -> &DbCacheSync<Block> {
		&self.cache
	}

	fn update_meta(
		&self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		is_best: bool,
		is_finalized: bool,
	) {
		let mut meta = self.meta.write();

		if number.is_zero() {
			meta.genesis_hash = hash;
			meta.finalized_hash = hash;
		}

		if is_best {
			meta.best_number = number;
			meta.best_hash = hash;
		}

		if is_finalized {
			meta.finalized_number = number;
			meta.finalized_hash = hash;
		}
	}
}

impl<Block> BlockchainHeaderBackend<Block> for LightStorage<Block>
	where
		Block: BlockT,
{
	fn header(&self, id: BlockId<Block>) -> ClientResult<Option<Block::Header>> {
		utils::read_header(&*self.db, columns::KEY_LOOKUP, columns::HEADER, id)
	}

	fn info(&self) -> ClientResult<BlockchainInfo<Block>> {
		let meta = self.meta.read();
		Ok(BlockchainInfo {
			best_hash: meta.best_hash,
			best_number: meta.best_number,
			genesis_hash: meta.genesis_hash,
			finalized_hash: meta.finalized_hash,
			finalized_number: meta.finalized_number,
		})
	}

	fn status(&self, id: BlockId<Block>) -> ClientResult<BlockStatus> {
		let exists = match id {
			BlockId::Hash(_) => read_db(
				&*self.db,
				columns::KEY_LOOKUP,
				columns::HEADER,
				id
			)?.is_some(),
			BlockId::Number(n) => n <= self.meta.read().best_number,
		};
		match exists {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	fn number(&self, hash: Block::Hash) -> ClientResult<Option<NumberFor<Block>>> {
		if let Some(lookup_key) = block_id_to_lookup_key::<Block>(&*self.db, columns::KEY_LOOKUP, BlockId::Hash(hash))? {
			let number = utils::lookup_key_to_number(&lookup_key)?;
			Ok(Some(number))
		} else {
			Ok(None)
		}
	}

	fn hash(&self, number: NumberFor<Block>) -> ClientResult<Option<Block::Hash>> {
		Ok(self.header(BlockId::Number(number))?.map(|header| header.hash().clone()))
	}
}

impl<Block: BlockT> LightStorage<Block> {
	// Get block changes trie root, if available.
	fn changes_trie_root(&self, block: BlockId<Block>) -> ClientResult<Option<Block::Hash>> {
		self.header(block)
			.map(|header| header.and_then(|header|
				header.digest().log(DigestItem::as_changes_trie_root)
					.cloned()))
	}

	/// Handle setting head within a transaction. `route_to` should be the last
	/// block that existed in the database. `best_to` should be the best block
	/// to be set.
	///
	/// In the case where the new best block is a block to be imported, `route_to`
	/// should be the parent of `best_to`. In the case where we set an existing block
	/// to be best, `route_to` should equal to `best_to`.
	fn set_head_with_transaction(&self, transaction: &mut DBTransaction, route_to: Block::Hash, best_to: (NumberFor<Block>, Block::Hash)) -> Result<(), client::error::Error> {
		let lookup_key = utils::number_and_hash_to_lookup_key(best_to.0, &best_to.1);

		// handle reorg.
		let meta = self.meta.read();
		if meta.best_hash != Default::default() {
			let tree_route = ::client::blockchain::tree_route(
				self,
				BlockId::Hash(meta.best_hash),
				BlockId::Hash(route_to),
			)?;

			// update block number to hash lookup entries.
			for retracted in tree_route.retracted() {
				if retracted.hash == meta.finalized_hash {
					// TODO: can we recover here?
					warn!("Safety failure: reverting finalized block {:?}",
						  (&retracted.number, &retracted.hash));
				}

				utils::remove_number_to_key_mapping(
					transaction,
					columns::KEY_LOOKUP,
					retracted.number
				);
			}

			for enacted in tree_route.enacted() {
				utils::insert_number_to_key_mapping(
					transaction,
					columns::KEY_LOOKUP,
					enacted.number,
					enacted.hash
				);
			}
		}

		transaction.put(columns::META, meta_keys::BEST_BLOCK, &lookup_key);
		utils::insert_number_to_key_mapping(
			transaction,
			columns::KEY_LOOKUP,
			best_to.0,
			best_to.1,
		);

		Ok(())
	}

	// Note that a block is finalized. Only call with child of last finalized block.
	fn note_finalized(
		&self,
		transaction: &mut DBTransaction,
		header: &Block::Header,
		hash: Block::Hash,
		displaced: &mut Option<FinalizationDisplaced<Block::Hash, NumberFor<Block>>>,
	) -> ClientResult<()> {
		let meta = self.meta.read();
		if &meta.finalized_hash != header.parent_hash() {
			return Err(::client::error::Error::NonSequentialFinalization(
				format!("Last finalized {:?} not parent of {:?}",
					meta.finalized_hash, hash),
			).into())
		}

		let lookup_key = utils::number_and_hash_to_lookup_key(header.number().clone(), hash);
		transaction.put(columns::META, meta_keys::FINALIZED_BLOCK, &lookup_key);

		// build new CHT(s) if required
		if let Some(new_cht_number) = cht::is_build_required(cht::SIZE, *header.number()) {
			let new_cht_start: NumberFor<Block> = cht::start_number(cht::SIZE, new_cht_number);

			let new_header_cht_root = cht::compute_root::<Block::Header, Blake2Hasher, _>(
				cht::SIZE, new_cht_number, (new_cht_start.as_()..)
				.map(|num| self.hash(As::sa(num)))
			)?;
			transaction.put(
				columns::CHT,
				&cht_key(HEADER_CHT_PREFIX, new_cht_start),
				new_header_cht_root.as_ref()
			);

			// if the header includes changes trie root, let's build a changes tries roots CHT
			if header.digest().log(DigestItem::as_changes_trie_root).is_some() {
				let new_changes_trie_cht_root = cht::compute_root::<Block::Header, Blake2Hasher, _>(
					cht::SIZE, new_cht_number, (new_cht_start.as_()..)
					.map(|num| self.changes_trie_root(BlockId::Number(As::sa(num))))
				)?;
				transaction.put(
					columns::CHT,
					&cht_key(CHANGES_TRIE_CHT_PREFIX, new_cht_start),
					new_changes_trie_cht_root.as_ref()
				);
			}

			// prune headers that are replaced with CHT
			let mut prune_block = new_cht_start;
			let new_cht_end = cht::end_number(cht::SIZE, new_cht_number);
			trace!(target: "db", "Replacing blocks [{}..{}] with CHT#{}",
				new_cht_start, new_cht_end, new_cht_number);

			while prune_block <= new_cht_end {
				if let Some(hash) = self.hash(prune_block)? {
					let lookup_key = block_id_to_lookup_key::<Block>(&*self.db, columns::KEY_LOOKUP, BlockId::Number(prune_block))?
						.expect("retrieved hash for `prune_block` right above. therefore retrieving lookup key must succeed. q.e.d.");
					utils::remove_key_mappings(
						transaction,
						columns::KEY_LOOKUP,
						prune_block,
						hash
					);
					transaction.delete(columns::HEADER, &lookup_key);
				}
				prune_block += One::one();
			}
		}

		let new_displaced = self.leaves.write().finalize_height(header.number().clone());
		match displaced {
			x @ &mut None => *x = Some(new_displaced),
			&mut Some(ref mut displaced) => displaced.merge(new_displaced),
		}

		Ok(())
	}

	/// Read CHT root of given type for the block.
	fn read_cht_root(
		&self,
		cht_type: u8,
		cht_size: u64,
		block: NumberFor<Block>
	) -> ClientResult<Block::Hash> {
		let no_cht_for_block = || ClientError::Backend(format!("CHT for block {} not exists", block));

		let cht_number = cht::block_to_cht_number(cht_size, block).ok_or_else(no_cht_for_block)?;
		let cht_start = cht::start_number(cht_size, cht_number);
		self.db.get(columns::CHT, &cht_key(cht_type, cht_start)).map_err(db_err)?
			.ok_or_else(no_cht_for_block)
			.and_then(|hash| Block::Hash::decode(&mut &*hash).ok_or_else(no_cht_for_block))
	}
}

impl<Block> AuxStore for LightStorage<Block>
	where Block: BlockT,
{
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> ClientResult<()> {
		let mut transaction = DBTransaction::new();
		for (k, v) in insert {
			transaction.put(columns::AUX, k, v);
		}
		for k in delete {
			transaction.delete(columns::AUX, k);
		}
		self.db.write(transaction).map_err(db_err)
	}

	fn get_aux(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		self.db.get(columns::AUX, key).map(|r| r.map(|v| v.to_vec())).map_err(db_err)
	}
}

impl<Block> LightBlockchainStorage<Block> for LightStorage<Block>
	where Block: BlockT,
{
	fn import_header(
		&self,
		header: Block::Header,
		cache_at: HashMap<well_known_cache_keys::Id, Vec<u8>>,
		leaf_state: NewBlockState,
		aux_ops: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	) -> ClientResult<()> {
		let mut finalization_displaced_leaves = None;
		let mut transaction = DBTransaction::new();

		let hash = header.hash();
		let number = *header.number();
		let parent_hash = *header.parent_hash();

		for (key, maybe_val) in aux_ops {
			match maybe_val {
				Some(val) => transaction.put_vec(columns::AUX, &key, val),
				None => transaction.delete(columns::AUX, &key),
			}
		}

		// blocks are keyed by number + hash.
		let lookup_key = utils::number_and_hash_to_lookup_key(number, &hash);

		if leaf_state.is_best() {
			self.set_head_with_transaction(&mut transaction, parent_hash, (number, hash))?;
		}

		utils::insert_hash_to_key_mapping(
			&mut transaction,
			columns::KEY_LOOKUP,
			number,
			hash,
		);
		transaction.put(columns::HEADER, &lookup_key, &header.encode());

		let is_genesis = number.is_zero();
		if is_genesis {
			transaction.put(columns::META, meta_keys::GENESIS_HASH, hash.as_ref());
		}

		let finalized = match leaf_state {
			_ if is_genesis => true,
			NewBlockState::Final => true,
			_ => false,
		};

		if finalized {
			self.note_finalized(
				&mut transaction,
				&header,
				hash,
				&mut finalization_displaced_leaves,
			)?;
		}

		{
			let mut leaves = self.leaves.write();
			let displaced_leaf = leaves.import(hash, number, parent_hash);

			let mut cache = self.cache.0.write();
			let cache_ops = cache.transaction(&mut transaction)
				.on_block_insert(
					ComplexBlockId::new(*header.parent_hash(), if number.is_zero() { Zero::zero() } else { number - One::one() }),
					ComplexBlockId::new(hash, number),
					cache_at,
					finalized,
				)?
				.into_ops();

			debug!("Light DB Commit {:?} ({})", hash, number);
			let write_result = self.db.write(transaction).map_err(db_err);
			if let Err(e) = write_result {
				let mut leaves = self.leaves.write();
				let mut undo = leaves.undo();

				// revert leaves set update if there was one.
				if let Some(displaced_leaf) = displaced_leaf {
					undo.undo_import(displaced_leaf);
				}

				if let Some(finalization_displaced) = finalization_displaced_leaves {
					undo.undo_finalization(finalization_displaced);
				}

				return Err(e);
			}

			cache.commit(cache_ops);
		}

		self.update_meta(hash, number, leaf_state.is_best(), finalized);

		Ok(())
	}

	fn set_head(&self, id: BlockId<Block>) -> ClientResult<()> {
		if let Some(header) = self.header(id)? {
			let hash = header.hash();
			let number = header.number();

			let mut transaction = DBTransaction::new();
			self.set_head_with_transaction(&mut transaction, hash.clone(), (number.clone(), hash.clone()))?;
			self.db.write(transaction).map_err(db_err)?;
			Ok(())
		} else {
			Err(ClientError::UnknownBlock(format!("Cannot set head {:?}", id)))
		}
	}

	fn header_cht_root(&self, cht_size: u64, block: NumberFor<Block>) -> ClientResult<Block::Hash> {
		self.read_cht_root(HEADER_CHT_PREFIX, cht_size, block)
	}

	fn changes_trie_cht_root(&self, cht_size: u64, block: NumberFor<Block>) -> ClientResult<Block::Hash> {
		self.read_cht_root(CHANGES_TRIE_CHT_PREFIX, cht_size, block)
	}

	fn finalize_header(&self, id: BlockId<Block>) -> ClientResult<()> {
		if let Some(header) = self.header(id)? {
			let mut displaced = None;
			let mut transaction = DBTransaction::new();
			let hash = header.hash();
			let number = *header.number();
			self.note_finalized(&mut transaction, &header, hash.clone(), &mut displaced)?;
			{
				let mut cache = self.cache.0.write();
				let cache_ops = cache.transaction(&mut transaction)
					.on_block_finalize(
						ComplexBlockId::new(*header.parent_hash(), if number.is_zero() { Zero::zero() } else { number - One::one() }),
						ComplexBlockId::new(hash, number)
					)?
					.into_ops();

				if let Err(e) = self.db.write(transaction).map_err(db_err) {
					if let Some(displaced) = displaced {
						self.leaves.write().undo().undo_finalization(displaced);
					}
					return Err(e);
				}
				cache.commit(cache_ops);
			}
			self.update_meta(hash, header.number().clone(), false, true);

			Ok(())
		} else {
			Err(ClientError::UnknownBlock(format!("Cannot finalize block {:?}", id)))
		}
	}

	fn last_finalized(&self) -> ClientResult<Block::Hash> {
		Ok(self.meta.read().finalized_hash.clone())
	}

	fn cache(&self) -> Option<Arc<BlockchainCache<Block>>> {
		Some(self.cache.clone())
	}
}

/// Build the key for inserting header-CHT at given block.
fn cht_key<N: As<u64>>(cht_type: u8, block: N) -> [u8; 5] {
	let mut key = [cht_type; 5];
	key[1..].copy_from_slice(&utils::number_index_key(block));
	key
}

#[cfg(test)]
pub(crate) mod tests {
	use client::cht;
	use runtime_primitives::generic::DigestItem;
	use runtime_primitives::testing::{H256 as Hash, Header, Block as RawBlock, ExtrinsicWrapper};
	use runtime_primitives::traits::AuthorityIdFor;
	use super::*;

	type Block = RawBlock<ExtrinsicWrapper<u32>>;
	type AuthorityId = AuthorityIdFor<Block>;

	pub fn default_header(parent: &Hash, number: u64) -> Header {
		Header {
			number: number.into(),
			parent_hash: *parent,
			state_root: Hash::random(),
			digest: Default::default(),
			extrinsics_root: Default::default(),
		}
	}

	fn header_with_changes_trie(parent: &Hash, number: u64) -> Header {
		let mut header = default_header(parent, number);
		header.digest.logs.push(DigestItem::ChangesTrieRoot([(number % 256) as u8; 32].into()));
		header
	}

	fn header_with_extrinsics_root(parent: &Hash, number: u64, extrinsics_root: Hash) -> Header {
		let mut header = default_header(parent, number);
		header.extrinsics_root = extrinsics_root;
		header
	}

	pub fn insert_block<F: Fn() -> Header>(
		db: &LightStorage<Block>,
		cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
		header: F,
	) -> Hash {
		let header = header();
		let hash = header.hash();
		db.import_header(header, cache, NewBlockState::Best, Vec::new()).unwrap();
		hash
	}

	fn insert_final_block<F: Fn() -> Header>(
		db: &LightStorage<Block>,
		cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
		header: F,
	) -> Hash {
		let header = header();
		let hash = header.hash();
		db.import_header(header, cache, NewBlockState::Final, Vec::new()).unwrap();
		hash
	}

	fn insert_non_best_block<F: Fn() -> Header>(
		db: &LightStorage<Block>,
		cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
		header: F,
	) -> Hash {
		let header = header();
		let hash = header.hash();
		db.import_header(header, cache, NewBlockState::Normal, Vec::new()).unwrap();
		hash
	}

	#[test]
	fn returns_known_header() {
		let db = LightStorage::new_test();
		let known_hash = insert_block(&db, HashMap::new(), || default_header(&Default::default(), 0));
		let header_by_hash = db.header(BlockId::Hash(known_hash)).unwrap().unwrap();
		let header_by_number = db.header(BlockId::Number(0)).unwrap().unwrap();
		assert_eq!(header_by_hash, header_by_number);
	}

	#[test]
	fn does_not_return_unknown_header() {
		let db = LightStorage::<Block>::new_test();
		assert!(db.header(BlockId::Hash(Hash::from_low_u64_be(1))).unwrap().is_none());
		assert!(db.header(BlockId::Number(0)).unwrap().is_none());
	}

	#[test]
	fn returns_info() {
		let db = LightStorage::new_test();
		let genesis_hash = insert_block(&db, HashMap::new(), || default_header(&Default::default(), 0));
		let info = db.info().unwrap();
		assert_eq!(info.best_hash, genesis_hash);
		assert_eq!(info.best_number, 0);
		assert_eq!(info.genesis_hash, genesis_hash);
		let best_hash = insert_block(&db, HashMap::new(), || default_header(&genesis_hash, 1));
		let info = db.info().unwrap();
		assert_eq!(info.best_hash, best_hash);
		assert_eq!(info.best_number, 1);
		assert_eq!(info.genesis_hash, genesis_hash);
	}

	#[test]
	fn returns_block_status() {
		let db = LightStorage::new_test();
		let genesis_hash = insert_block(&db, HashMap::new(), || default_header(&Default::default(), 0));
		assert_eq!(db.status(BlockId::Hash(genesis_hash)).unwrap(), BlockStatus::InChain);
		assert_eq!(db.status(BlockId::Number(0)).unwrap(), BlockStatus::InChain);
		assert_eq!(db.status(BlockId::Hash(Hash::from_low_u64_be(1))).unwrap(), BlockStatus::Unknown);
		assert_eq!(db.status(BlockId::Number(1)).unwrap(), BlockStatus::Unknown);
	}

	#[test]
	fn returns_block_hash() {
		let db = LightStorage::new_test();
		let genesis_hash = insert_block(&db, HashMap::new(), || default_header(&Default::default(), 0));
		assert_eq!(db.hash(0).unwrap(), Some(genesis_hash));
		assert_eq!(db.hash(1).unwrap(), None);
	}

	#[test]
	fn import_header_works() {
		let db = LightStorage::new_test();

		let genesis_hash = insert_block(&db, HashMap::new(), || default_header(&Default::default(), 0));
		assert_eq!(db.db.iter(columns::HEADER).count(), 1);
		assert_eq!(db.db.iter(columns::KEY_LOOKUP).count(), 2);

		let _ = insert_block(&db, HashMap::new(), || default_header(&genesis_hash, 1));
		assert_eq!(db.db.iter(columns::HEADER).count(), 2);
		assert_eq!(db.db.iter(columns::KEY_LOOKUP).count(), 4);
	}

	#[test]
	fn finalized_ancient_headers_are_replaced_with_cht() {
		fn insert_headers<F: Fn(&Hash, u64) -> Header>(header_producer: F) -> LightStorage<Block> {
			let db = LightStorage::new_test();

			// insert genesis block header (never pruned)
			let mut prev_hash = insert_final_block(&db, HashMap::new(), || header_producer(&Default::default(), 0));

			// insert SIZE blocks && ensure that nothing is pruned
			for number in 0..cht::SIZE {
				prev_hash = insert_block(&db, HashMap::new(), || header_producer(&prev_hash, 1 + number));
			}
			assert_eq!(db.db.iter(columns::HEADER).count(), (1 + cht::SIZE) as usize);
			assert_eq!(db.db.iter(columns::CHT).count(), 0);

			// insert next SIZE blocks && ensure that nothing is pruned
			for number in 0..cht::SIZE {
				prev_hash = insert_block(&db, HashMap::new(), || header_producer(&prev_hash, 1 + cht::SIZE + number));
			}
			assert_eq!(db.db.iter(columns::HEADER).count(), (1 + cht::SIZE + cht::SIZE) as usize);
			assert_eq!(db.db.iter(columns::CHT).count(), 0);

			// insert block #{2 * cht::SIZE + 1} && check that new CHT is created + headers of this CHT are pruned
			// nothing is yet finalized, so nothing is pruned.
			prev_hash = insert_block(&db, HashMap::new(), || header_producer(&prev_hash, 1 + cht::SIZE + cht::SIZE));
			assert_eq!(db.db.iter(columns::HEADER).count(), (2 + cht::SIZE + cht::SIZE) as usize);
			assert_eq!(db.db.iter(columns::CHT).count(), 0);

			// now finalize the block.
			for i in (0..(cht::SIZE + cht::SIZE)).map(|i| i + 1) {
				db.finalize_header(BlockId::Number(i)).unwrap();
			}
			db.finalize_header(BlockId::Hash(prev_hash)).unwrap();
			db
		}

		// when headers are created without changes tries roots
		let db = insert_headers(default_header);
		assert_eq!(db.db.iter(columns::HEADER).count(), (1 + cht::SIZE + 1) as usize);
		assert_eq!(db.db.iter(columns::KEY_LOOKUP).count(), (2 * (1 + cht::SIZE + 1)) as usize);
		assert_eq!(db.db.iter(columns::CHT).count(), 1);
		assert!((0..cht::SIZE).all(|i| db.header(BlockId::Number(1 + i)).unwrap().is_none()));
		assert!(db.header_cht_root(cht::SIZE, cht::SIZE / 2).is_ok());
		assert!(db.header_cht_root(cht::SIZE, cht::SIZE + cht::SIZE / 2).is_err());
		assert!(db.changes_trie_cht_root(cht::SIZE, cht::SIZE / 2).is_err());
		assert!(db.changes_trie_cht_root(cht::SIZE, cht::SIZE + cht::SIZE / 2).is_err());

		// when headers are created with changes tries roots
		let db = insert_headers(header_with_changes_trie);
		assert_eq!(db.db.iter(columns::HEADER).count(), (1 + cht::SIZE + 1) as usize);
		assert_eq!(db.db.iter(columns::CHT).count(), 2);
		assert!((0..cht::SIZE).all(|i| db.header(BlockId::Number(1 + i)).unwrap().is_none()));
		assert!(db.header_cht_root(cht::SIZE, cht::SIZE / 2).is_ok());
		assert!(db.header_cht_root(cht::SIZE, cht::SIZE + cht::SIZE / 2).is_err());
		assert!(db.changes_trie_cht_root(cht::SIZE, cht::SIZE / 2).is_ok());
		assert!(db.changes_trie_cht_root(cht::SIZE, cht::SIZE + cht::SIZE / 2).is_err());
	}

	#[test]
	fn get_cht_fails_for_genesis_block() {
		assert!(LightStorage::<Block>::new_test().header_cht_root(cht::SIZE, 0).is_err());
	}

	#[test]
	fn get_cht_fails_for_non_existant_cht() {
		assert!(LightStorage::<Block>::new_test().header_cht_root(cht::SIZE, (cht::SIZE / 2) as u64).is_err());
	}

	#[test]
	fn get_cht_works() {
		let db = LightStorage::new_test();

		// insert 1 + SIZE + SIZE + 1 blocks so that CHT#0 is created
		let mut prev_hash = insert_final_block(&db, HashMap::new(), || header_with_changes_trie(&Default::default(), 0));
		for i in 1..1 + cht::SIZE + cht::SIZE + 1 {
			prev_hash = insert_block(&db, HashMap::new(), || header_with_changes_trie(&prev_hash, i as u64));
			db.finalize_header(BlockId::Hash(prev_hash)).unwrap();
		}

		let cht_root_1 = db.header_cht_root(cht::SIZE, cht::start_number(cht::SIZE, 0)).unwrap();
		let cht_root_2 = db.header_cht_root(cht::SIZE, (cht::start_number(cht::SIZE, 0) + cht::SIZE / 2) as u64).unwrap();
		let cht_root_3 = db.header_cht_root(cht::SIZE, cht::end_number(cht::SIZE, 0)).unwrap();
		assert_eq!(cht_root_1, cht_root_2);
		assert_eq!(cht_root_2, cht_root_3);

		let cht_root_1 = db.changes_trie_cht_root(cht::SIZE, cht::start_number(cht::SIZE, 0)).unwrap();
		let cht_root_2 = db.changes_trie_cht_root(cht::SIZE, (cht::start_number(cht::SIZE, 0) + cht::SIZE / 2) as u64).unwrap();
		let cht_root_3 = db.changes_trie_cht_root(cht::SIZE, cht::end_number(cht::SIZE, 0)).unwrap();
		assert_eq!(cht_root_1, cht_root_2);
		assert_eq!(cht_root_2, cht_root_3);
	}

	#[test]
	fn tree_route_works() {
		let db = LightStorage::new_test();
		let block0 = insert_block(&db, HashMap::new(), || default_header(&Default::default(), 0));

		// fork from genesis: 3 prong.
		let a1 = insert_block(&db, HashMap::new(), || default_header(&block0, 1));
		let a2 = insert_block(&db, HashMap::new(), || default_header(&a1, 2));
		let a3 = insert_block(&db, HashMap::new(), || default_header(&a2, 3));

		// fork from genesis: 2 prong.
		let b1 = insert_block(&db, HashMap::new(), || header_with_extrinsics_root(&block0, 1, Hash::from([1; 32])));
		let b2 = insert_block(&db, HashMap::new(), || default_header(&b1, 2));

		{
			let tree_route = ::client::blockchain::tree_route(
				&db,
				BlockId::Hash(a3),
				BlockId::Hash(b2)
			).unwrap();

			assert_eq!(tree_route.common_block().hash, block0);
			assert_eq!(tree_route.retracted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![a3, a2, a1]);
			assert_eq!(tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![b1, b2]);
		}

		{
			let tree_route = ::client::blockchain::tree_route(
				&db,
				BlockId::Hash(a1),
				BlockId::Hash(a3),
			).unwrap();

			assert_eq!(tree_route.common_block().hash, a1);
			assert!(tree_route.retracted().is_empty());
			assert_eq!(tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![a2, a3]);
		}

		{
			let tree_route = ::client::blockchain::tree_route(
				&db,
				BlockId::Hash(a3),
				BlockId::Hash(a1),
			).unwrap();

			assert_eq!(tree_route.common_block().hash, a1);
			assert_eq!(tree_route.retracted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![a3, a2]);
			assert!(tree_route.enacted().is_empty());
		}

		{
			let tree_route = ::client::blockchain::tree_route(
				&db,
				BlockId::Hash(a2),
				BlockId::Hash(a2),
			).unwrap();

			assert_eq!(tree_route.common_block().hash, a2);
			assert!(tree_route.retracted().is_empty());
			assert!(tree_route.enacted().is_empty());
		}
	}

	#[test]
	fn authorities_are_cached() {
		let db = LightStorage::new_test();

		fn run_checks(db: &LightStorage<Block>, max: u64, checks: &[(u64, Option<Vec<AuthorityIdFor<Block>>>)]) {
			for (at, expected) in checks.iter().take_while(|(at, _)| *at <= max) {
				let actual = get_authorities(db.cache(), BlockId::Number(*at));
				assert_eq!(*expected, actual);
			}
		}

		fn same_authorities() -> HashMap<well_known_cache_keys::Id, Vec<u8>> {
			HashMap::new()
		}

		fn make_authorities(authorities: Vec<AuthorityId>) -> HashMap<well_known_cache_keys::Id, Vec<u8>> {
			let mut map = HashMap::new();
			map.insert(well_known_cache_keys::AUTHORITIES, authorities.encode());
			map
		}

		fn get_authorities(cache: &BlockchainCache<Block>, at: BlockId<Block>) -> Option<Vec<AuthorityId>> {
			cache.get_at(&well_known_cache_keys::AUTHORITIES, &at).and_then(|val| Decode::decode(&mut &val[..]))
		}

		let auth1 = || AuthorityId::from_raw([1u8; 32]);
		let auth2 = || AuthorityId::from_raw([2u8; 32]);
		let auth3 = || AuthorityId::from_raw([3u8; 32]);
		let auth4 = || AuthorityId::from_raw([4u8; 32]);
		let auth5 = || AuthorityId::from_raw([5u8; 32]);
		let auth6 = || AuthorityId::from_raw([6u8; 32]);

		let (hash2, hash6) = {
			// first few blocks are instantly finalized
			// B0(None) -> B1(None) -> B2(1) -> B3(1) -> B4(1, 2) -> B5(1, 2) -> B6(1, 2)
			let checks = vec![
				(0, None),
				(1, None),
				(2, Some(vec![auth1()])),
				(3, Some(vec![auth1()])),
				(4, Some(vec![auth1(), auth2()])),
				(5, Some(vec![auth1(), auth2()])),
				(6, Some(vec![auth1(), auth2()])),
			];

			let hash0 = insert_final_block(&db, same_authorities(), || default_header(&Default::default(), 0));
			run_checks(&db, 0, &checks);
			let hash1 = insert_final_block(&db, same_authorities(), || default_header(&hash0, 1));
			run_checks(&db, 1, &checks);
			let hash2 = insert_final_block(&db, make_authorities(vec![auth1()]), || default_header(&hash1, 2));
			run_checks(&db, 2, &checks);
			let hash3 = insert_final_block(&db, make_authorities(vec![auth1()]), || default_header(&hash2, 3));
			run_checks(&db, 3, &checks);
			let hash4 = insert_final_block(&db, make_authorities(vec![auth1(), auth2()]), || default_header(&hash3, 4));
			run_checks(&db, 4, &checks);
			let hash5 = insert_final_block(&db, make_authorities(vec![auth1(), auth2()]), || default_header(&hash4, 5));
			run_checks(&db, 5, &checks);
			let hash6 = insert_final_block(&db, same_authorities(), || default_header(&hash5, 6));
			run_checks(&db, 6, &checks);

			(hash2, hash6)
		};

		{
			// some older non-best blocks are inserted
			// ... -> B2(1) -> B2_1(1) -> B2_2(2)
			// => the cache ignores all writes before best finalized block
			let hash2_1 = insert_non_best_block(&db, make_authorities(vec![auth1()]), || default_header(&hash2, 3));
			assert_eq!(None, get_authorities(db.cache(), BlockId::Hash(hash2_1)));
			let hash2_2 = insert_non_best_block(&db, make_authorities(vec![auth1(), auth2()]), || default_header(&hash2_1, 4));
			assert_eq!(None, get_authorities(db.cache(), BlockId::Hash(hash2_2)));
		}

		let (hash7, hash8, hash6_1, hash6_2, hash6_1_1, hash6_1_2) = {
			// inserting non-finalized blocks
			// B6(None) -> B7(3) -> B8(3)
			//          \> B6_1(4) -> B6_2(4)
			//                     \> B6_1_1(5)
			//                     \> B6_1_2(6) -> B6_1_3(7)

			let hash7 = insert_block(&db, make_authorities(vec![auth3()]), || default_header(&hash6, 7));
			assert_eq!(
				get_authorities(db.cache(), BlockId::Hash(hash6)),
				Some(vec![auth1(), auth2()]),
			);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash7)), Some(vec![auth3()]));
			let hash8 = insert_block(&db, make_authorities(vec![auth3()]), || default_header(&hash7, 8));
			assert_eq!(
				get_authorities(db.cache(), BlockId::Hash(hash6)),
				Some(vec![auth1(), auth2()]),
			);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash7)), Some(vec![auth3()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash8)), Some(vec![auth3()]));
			let hash6_1 = insert_block(&db, make_authorities(vec![auth4()]), || default_header(&hash6, 7));
			assert_eq!(
				get_authorities(db.cache(), BlockId::Hash(hash6)),
				Some(vec![auth1(), auth2()]),
			);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash7)), Some(vec![auth3()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash8)), Some(vec![auth3()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1)), Some(vec![auth4()]));
			let hash6_1_1 = insert_non_best_block(&db, make_authorities(vec![auth5()]), || default_header(&hash6_1, 8));
			assert_eq!(
				get_authorities(db.cache(), BlockId::Hash(hash6)),
				Some(vec![auth1(), auth2()]),
			);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash7)), Some(vec![auth3()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash8)), Some(vec![auth3()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1)), Some(vec![auth4()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1_1)), Some(vec![auth5()]));
			let hash6_1_2 = insert_non_best_block(&db, make_authorities(vec![auth6()]), || default_header(&hash6_1, 8));
			assert_eq!(
				get_authorities(db.cache(), BlockId::Hash(hash6)),
				Some(vec![auth1(), auth2()]),
			);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash7)), Some(vec![auth3()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash8)), Some(vec![auth3()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1)), Some(vec![auth4()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1_1)), Some(vec![auth5()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1_2)), Some(vec![auth6()]));
			let hash6_2 = insert_block(&db, make_authorities(vec![auth4()]), || default_header(&hash6_1, 8));
			assert_eq!(
				get_authorities(db.cache(), BlockId::Hash(hash6)),
				Some(vec![auth1(), auth2()]),
			);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash7)), Some(vec![auth3()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash8)), Some(vec![auth3()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1)), Some(vec![auth4()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1_1)), Some(vec![auth5()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1_2)), Some(vec![auth6()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_2)), Some(vec![auth4()]));

			(hash7, hash8, hash6_1, hash6_2, hash6_1_1, hash6_1_2)
		};

		{
			// finalize block hash6_1
			db.finalize_header(BlockId::Hash(hash6_1)).unwrap();
			assert_eq!(
				get_authorities(db.cache(), BlockId::Hash(hash6)),
				Some(vec![auth1(), auth2()]),
			);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash7)), None);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash8)), None);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1)), Some(vec![auth4()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1_1)), Some(vec![auth5()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1_2)), Some(vec![auth6()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_2)), Some(vec![auth4()]));
			// finalize block hash6_2
			db.finalize_header(BlockId::Hash(hash6_2)).unwrap();
			assert_eq!(
				get_authorities(db.cache(), BlockId::Hash(hash6)),
				Some(vec![auth1(), auth2()]),
			);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash7)), None);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash8)), None);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1)), Some(vec![auth4()]));
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1_1)), None);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_1_2)), None);
			assert_eq!(get_authorities(db.cache(), BlockId::Hash(hash6_2)), Some(vec![auth4()]));
		}
	}

	#[test]
	fn database_is_reopened() {
		let db = LightStorage::new_test();
		let hash0 = insert_final_block(&db, HashMap::new(), || default_header(&Default::default(), 0));
		assert_eq!(db.info().unwrap().best_hash, hash0);
		assert_eq!(db.header(BlockId::Hash(hash0)).unwrap().unwrap().hash(), hash0);

		let db = db.db;
		let db = LightStorage::from_kvdb(db).unwrap();
		assert_eq!(db.info().unwrap().best_hash, hash0);
		assert_eq!(db.header(BlockId::Hash::<Block>(hash0)).unwrap().unwrap().hash(), hash0);
	}

	#[test]
	fn aux_store_works() {
		let db = LightStorage::<Block>::new_test();

		// insert aux1 + aux2 using direct store access
		db.insert_aux(&[(&[1][..], &[101][..]), (&[2][..], &[102][..])], ::std::iter::empty()).unwrap();

		// check aux values
		assert_eq!(db.get_aux(&[1]).unwrap(), Some(vec![101]));
		assert_eq!(db.get_aux(&[2]).unwrap(), Some(vec![102]));
		assert_eq!(db.get_aux(&[3]).unwrap(), None);

		// delete aux1 + insert aux3 using import operation
		db.import_header(default_header(&Default::default(), 0), HashMap::new(), NewBlockState::Best, vec![
			(vec![3], Some(vec![103])),
			(vec![1], None),
		]).unwrap();

		// check aux values
		assert_eq!(db.get_aux(&[1]).unwrap(), None);
		assert_eq!(db.get_aux(&[2]).unwrap(), Some(vec![102]));
		assert_eq!(db.get_aux(&[3]).unwrap(), Some(vec![103]));
	}

	#[test]
	fn test_leaves_pruned_on_finality() {
		let db = LightStorage::<Block>::new_test();
		let block0 = insert_block(&db, HashMap::new(), || default_header(&Default::default(), 0));

		let block1_a = insert_block(&db, HashMap::new(), || default_header(&block0, 1));
		let block1_b = insert_block(&db, HashMap::new(), || header_with_extrinsics_root(&block0, 1, [1; 32].into()));
		let block1_c = insert_block(&db, HashMap::new(), || header_with_extrinsics_root(&block0, 1, [2; 32].into()));

		assert_eq!(db.leaves.read().hashes(), vec![block1_a, block1_b, block1_c]);

		let block2_a = insert_block(&db, HashMap::new(), || default_header(&block1_a, 2));
		let block2_b = insert_block(&db, HashMap::new(), || header_with_extrinsics_root(&block1_b, 2, [1; 32].into()));
		let block2_c = insert_block(&db, HashMap::new(), || header_with_extrinsics_root(&block1_b, 2, [2; 32].into()));

		assert_eq!(db.leaves.read().hashes(), vec![block2_a, block2_b, block2_c, block1_c]);

		db.finalize_header(BlockId::hash(block1_a)).unwrap();
		db.finalize_header(BlockId::hash(block2_a)).unwrap();

		// leaves at same height stay. Leaves at lower heights pruned.
		assert_eq!(db.leaves.read().hashes(), vec![block2_a, block2_b, block2_c]);
	}
}
