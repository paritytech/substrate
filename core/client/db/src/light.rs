// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use std::sync::Arc;
use parking_lot::RwLock;

use kvdb::{KeyValueDB, DBTransaction};

use client::backend::NewBlockState;
use client::blockchain::{BlockStatus, Cache as BlockchainCache,
	HeaderBackend as BlockchainHeaderBackend, Info as BlockchainInfo};
use client::{cht, LeafSet};
use client::error::{ErrorKind as ClientErrorKind, Result as ClientResult};
use client::light::blockchain::Storage as LightBlockchainStorage;
use codec::{Decode, Encode};
use primitives::{AuthorityId, Blake2Hasher};
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT,
	Zero, One, As, NumberFor};
use cache::{DbCacheSync, DbCache, ComplexBlockId};
use utils::{meta_keys, Meta, db_err, number_to_lookup_key, open_database,
	read_db, block_id_to_lookup_key, read_meta};
use DatabaseSettings;

pub(crate) mod columns {
	pub const META: Option<u32> = ::utils::COLUMN_META;
	pub const HASH_LOOKUP: Option<u32> = Some(1);
	pub const HEADER: Option<u32> = Some(2);
	pub const CACHE: Option<u32> = Some(3);
	pub const CHT: Option<u32> = Some(4);
}

/// Light blockchain storage. Stores most recent headers + CHTs for older headers.
/// Locks order: meta, leaves, cache.
pub struct LightStorage<Block: BlockT> {
	db: Arc<KeyValueDB>,
	meta: RwLock<Meta<<<Block as BlockT>::Header as HeaderT>::Number, Block::Hash>>,
	leaves: RwLock<LeafSet<Block::Hash, NumberFor<Block>>>,
	cache: DbCacheSync<Block>,
}

#[derive(Clone, PartialEq, Debug)]
struct BestAuthorities<N> {
	/// first block, when this set became actual
	valid_from: N,
	/// None means that we do not know the set starting from `valid_from` block
	authorities: Option<Vec<AuthorityId>>,
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

	#[cfg(test)]
	pub(crate) fn new_test() -> Self {
		use utils::NUM_COLUMNS;

		let db = Arc::new(::kvdb_memorydb::create(NUM_COLUMNS));

		Self::from_kvdb(db as Arc<_>).expect("failed to create test-db")
	}

	fn from_kvdb(db: Arc<KeyValueDB>) -> ClientResult<Self> {
		let meta = read_meta::<Block>(&*db, columns::META, columns::HEADER)?;
		let leaves = LeafSet::read_from_db(&*db, columns::META, meta_keys::LEAF_PREFIX)?;
		let cache = DbCache::new(
			db.clone(),
			columns::HASH_LOOKUP,
			columns::HEADER,
			columns::CACHE,
			ComplexBlockId::new(meta.finalized_hash, meta.finalized_number),
		);

		Ok(LightStorage {
			db,
			meta: RwLock::new(meta),
			cache: DbCacheSync(RwLock::new(cache)),
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
		number: <<Block as BlockT>::Header as HeaderT>::Number,
		is_best: bool,
		is_finalized: bool,
	) {
		let mut meta = self.meta.write();

		if number == Zero::zero() {
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
		::utils::read_header(&*self.db, columns::HASH_LOOKUP, columns::HEADER, id)
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
				columns::HASH_LOOKUP,
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

	fn number(&self, hash: Block::Hash) -> ClientResult<Option<<<Block as BlockT>::Header as HeaderT>::Number>> {
		if let Some(lookup_key) = block_id_to_lookup_key::<Block>(&*self.db, columns::HASH_LOOKUP, BlockId::Hash(hash))? {
			let number = ::utils::lookup_key_to_number(&lookup_key)?;
			Ok(Some(number))
		} else {
			Ok(None)
		}
	}

	fn hash(&self, number: <<Block as BlockT>::Header as HeaderT>::Number) -> ClientResult<Option<Block::Hash>> {
		Ok(self.header(BlockId::Number(number))?.map(|header| header.hash().clone()))
	}
}

impl<Block: BlockT> LightStorage<Block> {
	fn note_finalized(
		&self,
		transaction: &mut DBTransaction,
		header: &Block::Header,
		hash: Block::Hash,
	) -> ClientResult<()> {
		let meta = self.meta.read();
		if &meta.finalized_hash != header.parent_hash() {
			return Err(::client::error::ErrorKind::NonSequentialFinalization(
				format!("Last finalized {:?} not parent of {:?}",
					meta.finalized_hash, hash),
			).into())
		}

		let lookup_key = ::utils::number_to_lookup_key(header.number().clone());
		transaction.put(columns::META, meta_keys::FINALIZED_BLOCK, &lookup_key);

		// build new CHT if required
		if let Some(new_cht_number) = cht::is_build_required(cht::SIZE, *header.number()) {
			let new_cht_start: NumberFor<Block> = cht::start_number(cht::SIZE, new_cht_number);
			let new_cht_root = cht::compute_root::<Block::Header, Blake2Hasher, _>(
				cht::SIZE, new_cht_number, (new_cht_start.as_()..)
				.map(|num| self.hash(As::sa(num)).unwrap_or_default())
			);

			if let Some(new_cht_root) = new_cht_root {
				transaction.put(columns::CHT, &number_to_lookup_key(new_cht_start), new_cht_root.as_ref());

				let mut prune_block = new_cht_start;
				let new_cht_end = cht::end_number(cht::SIZE, new_cht_number);
				trace!(target: "db", "Replacing blocks [{}..{}] with CHT#{}", new_cht_start, new_cht_end, new_cht_number);

				while prune_block <= new_cht_end {
					if let Some(hash) = self.hash(prune_block)? {
						let lookup_key = block_id_to_lookup_key::<Block>(&*self.db, columns::HASH_LOOKUP, BlockId::Number(prune_block))?
							.expect("retrieved hash for `prune_block` right above. therefore retrieving lookup key must succeed. q.e.d.");
						transaction.delete(columns::HASH_LOOKUP, hash.as_ref());
						transaction.delete(columns::HEADER, &lookup_key);
					}
					prune_block += NumberFor::<Block>::one();
				}
			}
		}

		Ok(())
	}
}

impl<Block> LightBlockchainStorage<Block> for LightStorage<Block>
	where Block: BlockT,
{
	fn import_header(
		&self,
		header: Block::Header,
		authorities: Option<Vec<AuthorityId>>,
		leaf_state: NewBlockState,
	) -> ClientResult<()> {
		let mut transaction = DBTransaction::new();

		let hash = header.hash();
		let number = *header.number();
		let parent_hash = *header.parent_hash();

		// blocks in longest chain are keyed by number
		let lookup_key = if leaf_state.is_best() {
			::utils::number_to_lookup_key(number).to_vec()
		} else {
		// other blocks are keyed by number + hash
			::utils::number_and_hash_to_lookup_key(number, hash)
		};

		if leaf_state.is_best() {
			// handle reorg.
			{
				let meta = self.meta.read();
				if meta.best_hash != Default::default() {
					let tree_route = ::client::blockchain::tree_route(
						self,
						BlockId::Hash(meta.best_hash),
						BlockId::Hash(parent_hash),
					)?;

					// update block number to hash lookup entries.
					for retracted in tree_route.retracted() {
						if retracted.hash == meta.finalized_hash {
							// TODO: can we recover here?
							warn!("Safety failure: reverting finalized block {:?}",
								(&retracted.number, &retracted.hash));
						}

						let prev_lookup_key = ::utils::number_to_lookup_key(retracted.number);
						let new_lookup_key = ::utils::number_and_hash_to_lookup_key(retracted.number, retracted.hash);

						// change mapping from `number -> header`
						// to `number + hash -> header`
						let retracted_header = if let Some(header) = self.header(BlockId::Number(retracted.number))? {
							header
						} else {
							return Err(::client::error::ErrorKind::UnknownBlock(format!("retracted {:?}", retracted)).into());
						};
						transaction.delete(columns::HEADER, &prev_lookup_key);
						transaction.put(columns::HEADER, &new_lookup_key, &retracted_header.encode());

						transaction.put(columns::HASH_LOOKUP, retracted.hash.as_ref(), &new_lookup_key);
					}

					for enacted in tree_route.enacted() {
						let prev_lookup_key = ::utils::number_and_hash_to_lookup_key(enacted.number, enacted.hash);
						let new_lookup_key = ::utils::number_to_lookup_key(enacted.number);

						// change mapping from `number + hash -> header`
						// to `number -> header`
						let enacted_header = if let Some(header) = self.header(BlockId::Number(enacted.number))? {
							header
						} else {
							return Err(::client::error::ErrorKind::UnknownBlock(format!("enacted {:?}", enacted)).into());
						};
						transaction.delete(columns::HEADER, &prev_lookup_key);
						transaction.put(columns::HEADER, &new_lookup_key, &enacted_header.encode());

						transaction.put(columns::HASH_LOOKUP, enacted.hash.as_ref(), &new_lookup_key);
					}
				}
			}

			transaction.put(columns::META, meta_keys::BEST_BLOCK, &lookup_key);
		}

		transaction.put(columns::HEADER, &lookup_key, &header.encode());
		transaction.put(columns::HASH_LOOKUP, hash.as_ref(), &lookup_key);

		let finalized = match leaf_state {
			NewBlockState::Final => true,
			_ => false,
		};

		if finalized {
			self.note_finalized(&mut transaction, &header, hash)?;
		}

		{
			let mut leaves = self.leaves.write();
			let displaced_leaf = leaves.import(hash, number, parent_hash);

			let mut cache = self.cache.0.write();
			let cache_ops = cache.transaction(&mut transaction)
				.on_block_insert(
					ComplexBlockId::new(*header.parent_hash(), if number == Zero::zero() { Zero::zero() } else { number - One::one() }),
					ComplexBlockId::new(hash, number),
					authorities,
					finalized,
				)?
				.into_ops();

			debug!("Light DB Commit {:?} ({})", hash, number);
			let write_result = self.db.write(transaction).map_err(db_err);
			if let Err(e) = write_result {
				// revert leaves set update if there was one.
				if let Some(displaced_leaf) = displaced_leaf {
					leaves.undo(displaced_leaf);
				}
				return Err(e);
			}

			cache.commit(cache_ops);
		}

		self.update_meta(hash, number, leaf_state.is_best(), finalized);

		Ok(())
	}

	fn cht_root(&self, cht_size: u64, block: <<Block as BlockT>::Header as HeaderT>::Number) -> ClientResult<Block::Hash> {
		let no_cht_for_block = || ClientErrorKind::Backend(format!("CHT for block {} not exists", block)).into();

		let cht_number = cht::block_to_cht_number(cht_size, block).ok_or_else(no_cht_for_block)?;
		let cht_start = cht::start_number(cht_size, cht_number);
		self.db.get(columns::CHT, &number_to_lookup_key(cht_start)).map_err(db_err)?
			.ok_or_else(no_cht_for_block)
			.and_then(|hash| Block::Hash::decode(&mut &*hash).ok_or_else(no_cht_for_block))
	}

	fn finalize_header(&self, id: BlockId<Block>) -> ClientResult<()> {
		if let Some(header) = self.header(id)? {
			let mut transaction = DBTransaction::new();
			// TODO: ensure best chain contains this block.
			let hash = header.hash();
			let number = *header.number();
			self.note_finalized(&mut transaction, &header, hash.clone())?;
			{
				let mut cache = self.cache.0.write();
				let cache_ops = cache.transaction(&mut transaction)
					.on_block_finalize(
						ComplexBlockId::new(*header.parent_hash(), if number == Zero::zero() { Zero::zero() } else { number - One::one() }),
						ComplexBlockId::new(hash, number)
					)?
					.into_ops();

				self.db.write(transaction).map_err(db_err)?;
				cache.commit(cache_ops);
			}
			self.update_meta(hash, header.number().clone(), false, true);

			Ok(())
		} else {
			Err(ClientErrorKind::UnknownBlock(format!("Cannot finalize block {:?}", id)).into())
		}
	}

	fn last_finalized(&self) -> ClientResult<Block::Hash> {
		Ok(self.meta.read().finalized_hash.clone())
	}

	fn cache(&self) -> Option<&BlockchainCache<Block>> {
		None
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use client::cht;
	use runtime_primitives::testing::{H256 as Hash, Header, Block as RawBlock, ExtrinsicWrapper};
	use super::*;

	type Block = RawBlock<ExtrinsicWrapper<u32>>;

	fn prepare_header(parent: &Hash, number: u64, extrinsics_root: Hash) -> Header {
		Header {
			number: number.into(),
			parent_hash: *parent,
			state_root: Hash::random(),
			digest: Default::default(),
			extrinsics_root,
		}
	}

	pub fn insert_block_with_extrinsics_root(
		db: &LightStorage<Block>,
		parent: &Hash,
		number: u64,
		authorities: Option<Vec<AuthorityId>>,
		extrinsics_root: Hash,
	) -> Hash {
		let header = prepare_header(parent, number, extrinsics_root);
		let hash = header.hash();
		db.import_header(header, authorities, NewBlockState::Best).unwrap();
		hash
	}

	pub fn insert_block(
		db: &LightStorage<Block>,
		parent: &Hash,
		number: u64,
		authorities: Option<Vec<AuthorityId>>
	) -> Hash {
		let header = prepare_header(parent, number, Default::default());
		let hash = header.hash();
		db.import_header(header, authorities, NewBlockState::Best).unwrap();
		hash
	}

	fn insert_final_block(
		db: &LightStorage<Block>,
		parent: &Hash,
		number: u64,
		authorities: Option<Vec<AuthorityId>>
	) -> Hash {
		let header = prepare_header(parent, number, Default::default());
		let hash = header.hash();
		db.import_header(header, authorities, NewBlockState::Final).unwrap();
		hash
	}

	fn insert_non_best_block(
		db: &LightStorage<Block>,
		parent: &Hash,
		number: u64,
		authorities: Option<Vec<AuthorityId>>
	) -> Hash {
		let header = prepare_header(parent, number, Default::default());
		let hash = header.hash();
		db.import_header(header, authorities, NewBlockState::Normal).unwrap();
		hash
	}

	#[test]
	fn returns_known_header() {
		let db = LightStorage::new_test();
		let known_hash = insert_block(&db, &Default::default(), 0, None);
		let header_by_hash = db.header(BlockId::Hash(known_hash)).unwrap().unwrap();
		let header_by_number = db.header(BlockId::Number(0)).unwrap().unwrap();
		assert_eq!(header_by_hash, header_by_number);
	}

	#[test]
	fn does_not_return_unknown_header() {
		let db = LightStorage::<Block>::new_test();
		assert!(db.header(BlockId::Hash(1.into())).unwrap().is_none());
		assert!(db.header(BlockId::Number(0)).unwrap().is_none());
	}

	#[test]
	fn returns_info() {
		let db = LightStorage::new_test();
		let genesis_hash = insert_block(&db, &Default::default(), 0, None);
		let info = db.info().unwrap();
		assert_eq!(info.best_hash, genesis_hash);
		assert_eq!(info.best_number, 0);
		assert_eq!(info.genesis_hash, genesis_hash);
		let best_hash = insert_block(&db, &genesis_hash, 1, None);
		let info = db.info().unwrap();
		assert_eq!(info.best_hash, best_hash);
		assert_eq!(info.best_number, 1);
		assert_eq!(info.genesis_hash, genesis_hash);
	}

	#[test]
	fn returns_block_status() {
		let db = LightStorage::new_test();
		let genesis_hash = insert_block(&db, &Default::default(), 0, None);
		assert_eq!(db.status(BlockId::Hash(genesis_hash)).unwrap(), BlockStatus::InChain);
		assert_eq!(db.status(BlockId::Number(0)).unwrap(), BlockStatus::InChain);
		assert_eq!(db.status(BlockId::Hash(1.into())).unwrap(), BlockStatus::Unknown);
		assert_eq!(db.status(BlockId::Number(1)).unwrap(), BlockStatus::Unknown);
	}

	#[test]
	fn returns_block_hash() {
		let db = LightStorage::new_test();
		let genesis_hash = insert_block(&db, &Default::default(), 0, None);
		assert_eq!(db.hash(0).unwrap(), Some(genesis_hash));
		assert_eq!(db.hash(1).unwrap(), None);
	}

	#[test]
	fn import_header_works() {
		let db = LightStorage::new_test();

		let genesis_hash = insert_block(&db, &Default::default(), 0, None);
		assert_eq!(db.db.iter(columns::HEADER).count(), 1);
		assert_eq!(db.db.iter(columns::HASH_LOOKUP).count(), 1);

		let _ = insert_block(&db, &genesis_hash, 1, None);
		assert_eq!(db.db.iter(columns::HEADER).count(), 2);
		assert_eq!(db.db.iter(columns::HASH_LOOKUP).count(), 2);
	}

	#[test]
	fn finalized_ancient_headers_are_replaced_with_cht() {
		let db = LightStorage::new_test();

		// insert genesis block header (never pruned)
		let mut prev_hash = insert_final_block(&db, &Default::default(), 0, None);

		// insert SIZE blocks && ensure that nothing is pruned
		for number in 0..cht::SIZE {
			prev_hash = insert_block(&db, &prev_hash, 1 + number, None);
		}
		assert_eq!(db.db.iter(columns::HEADER).count(), (1 + cht::SIZE) as usize);
		assert_eq!(db.db.iter(columns::HASH_LOOKUP).count(), (1 + cht::SIZE) as usize);
		assert_eq!(db.db.iter(columns::CHT).count(), 0);

		// insert next SIZE blocks && ensure that nothing is pruned
		for number in 0..cht::SIZE {
			prev_hash = insert_block(&db, &prev_hash, 1 + cht::SIZE + number, None);
		}
		assert_eq!(db.db.iter(columns::HEADER).count(), (1 + cht::SIZE + cht::SIZE) as usize);
		assert_eq!(db.db.iter(columns::HASH_LOOKUP).count(), (1 + cht::SIZE + cht::SIZE) as usize);
		assert_eq!(db.db.iter(columns::CHT).count(), 0);

		// insert block #{2 * cht::SIZE + 1} && check that new CHT is created + headers of this CHT are pruned
		// nothing is yet finalized, so nothing is pruned.
		prev_hash = insert_block(&db, &prev_hash, 1 + cht::SIZE + cht::SIZE, None);
		assert_eq!(db.db.iter(columns::HEADER).count(), (2 + cht::SIZE + cht::SIZE) as usize);
		assert_eq!(db.db.iter(columns::HASH_LOOKUP).count(), (2 + cht::SIZE + cht::SIZE) as usize);
		assert_eq!(db.db.iter(columns::CHT).count(), 0);

		// now finalize the block.
		for i in (0..(cht::SIZE + cht::SIZE)).map(|i| i + 1) {
			db.finalize_header(BlockId::Number(i)).unwrap();
		}
		db.finalize_header(BlockId::Hash(prev_hash)).unwrap();
		assert_eq!(db.db.iter(columns::HEADER).count(), (1 + cht::SIZE + 1) as usize);
		assert_eq!(db.db.iter(columns::HASH_LOOKUP).count(), (1 + cht::SIZE + 1) as usize);
		assert_eq!(db.db.iter(columns::CHT).count(), 1);
		assert!((0..cht::SIZE).all(|i| db.db.get(columns::HEADER, &number_to_lookup_key(1 + i)).unwrap().is_none()));
	}

	#[test]
	fn get_cht_fails_for_genesis_block() {
		assert!(LightStorage::<Block>::new_test().cht_root(cht::SIZE, 0).is_err());
	}

	#[test]
	fn get_cht_fails_for_non_existant_cht() {
		assert!(LightStorage::<Block>::new_test().cht_root(cht::SIZE, (cht::SIZE / 2) as u64).is_err());
	}

	#[test]
	fn get_cht_works() {
		let db = LightStorage::new_test();

		// insert 1 + SIZE + SIZE + 1 blocks so that CHT#0 is created
		let mut prev_hash = insert_final_block(&db, &Default::default(), 0, None);
		for i in 1..1 + cht::SIZE + cht::SIZE + 1 {
			prev_hash = insert_block(&db, &prev_hash, i as u64, None);
			db.finalize_header(BlockId::Hash(prev_hash)).unwrap();
		}

		let cht_root_1 = db.cht_root(cht::SIZE, cht::start_number(cht::SIZE, 0)).unwrap();
		let cht_root_2 = db.cht_root(cht::SIZE, (cht::start_number(cht::SIZE, 0) + cht::SIZE / 2) as u64).unwrap();
		let cht_root_3 = db.cht_root(cht::SIZE, cht::end_number(cht::SIZE, 0)).unwrap();
		assert_eq!(cht_root_1, cht_root_2);
		assert_eq!(cht_root_2, cht_root_3);
	}

	#[test]
	fn tree_route_works() {
		let db = LightStorage::new_test();
		let block0 = insert_block(&db, &Default::default(), 0, None);

		// fork from genesis: 3 prong.
		let a1 = insert_block(&db, &block0, 1, None);
		let a2 = insert_block(&db, &a1, 2, None);
		let a3 = insert_block(&db, &a2, 3, None);

		// fork from genesis: 2 prong.
		let b1 = insert_block_with_extrinsics_root(&db, &block0, 1, None, Hash::from([1; 32]));
		let b2 = insert_block(&db, &b1, 2, None);

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
	fn authorites_are_cached() {
		let db = LightStorage::new_test();

		fn run_checks(db: &LightStorage<Block>, max: u64, checks: &[(u64, Option<Vec<AuthorityId>>)]) {
			for (at, expected) in checks.iter().take_while(|(at, _)| *at <= max) {
				let actual = db.cache().authorities_at(BlockId::Number(*at));
				assert_eq!(*expected, actual);
			}
		}

		let (hash2, hash6) = {
			// first few blocks are instantly finalized
			// B0(None) -> B1(None) -> B2(1) -> B3(1) -> B4(1, 2) -> B5(1, 2) -> B6(None)
			let checks = vec![
				(0, None),
				(1, None),
				(2, Some(vec![[1u8; 32].into()])),
				(3, Some(vec![[1u8; 32].into()])),
				(4, Some(vec![[1u8; 32].into(), [2u8; 32].into()])),
				(5, Some(vec![[1u8; 32].into(), [2u8; 32].into()])),
				(6, None),
				(7, None), // block will work for 'future' block too
			];

			let hash0 = insert_final_block(&db, &Default::default(), 0, None);
			run_checks(&db, 0, &checks);
			let hash1 = insert_final_block(&db, &hash0, 1, None);
			run_checks(&db, 1, &checks);
			let hash2 = insert_final_block(&db, &hash1, 2, Some(vec![[1u8; 32].into()]));
			run_checks(&db, 2, &checks);
			let hash3 = insert_final_block(&db, &hash2, 3, Some(vec![[1u8; 32].into()]));
			run_checks(&db, 3, &checks);
			let hash4 = insert_final_block(&db, &hash3, 4, Some(vec![[1u8; 32].into(), [2u8; 32].into()]));
			run_checks(&db, 4, &checks);
			let hash5 = insert_final_block(&db, &hash4, 5, Some(vec![[1u8; 32].into(), [2u8; 32].into()]));
			run_checks(&db, 5, &checks);
			let hash6 = insert_final_block(&db, &hash5, 6, None);
			run_checks(&db, 7, &checks);

			(hash2, hash6)
		};

		{
			// some older non-best blocks are inserted
			// ... -> B2(1) -> B2_1(1) -> B2_2(2)
			// => the cache ignores all writes before best finalized block
			let hash2_1 = insert_non_best_block(&db, &hash2, 3, Some(vec![[1u8; 32].into()]));
			assert_eq!(None, db.cache().authorities_at(BlockId::Hash(hash2_1)));
			let hash2_2 = insert_non_best_block(&db, &hash2_1, 4, Some(vec![[1u8; 32].into(), [2u8; 32].into()]));
			assert_eq!(None, db.cache().authorities_at(BlockId::Hash(hash2_2)));
		}

		let (hash7, hash8, hash6_1, hash6_2, hash6_1_1, hash6_1_2) = {
			// inserting non-finalized blocks
			// B6(None) -> B7(3) -> B8(3)
			//          \> B6_1(4) -> B6_2(4)
			//                     \> B6_1_1(5)
			//                     \> B6_1_2(6) -> B6_1_3(7)

			let hash7 = insert_block(&db, &hash6, 7, Some(vec![[3u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash7)), Some(vec![[3u8; 32].into()]));
			let hash8 = insert_block(&db, &hash7, 8, Some(vec![[3u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash7)), Some(vec![[3u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash8)), Some(vec![[3u8; 32].into()]));
			let hash6_1 = insert_block(&db, &hash6, 7, Some(vec![[4u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash7)), Some(vec![[3u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash8)), Some(vec![[3u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1)), Some(vec![[4u8; 32].into()]));
			let hash6_1_1 = insert_non_best_block(&db, &hash6_1, 8, Some(vec![[5u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash7)), Some(vec![[3u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash8)), Some(vec![[3u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1)), Some(vec![[4u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1_1)), Some(vec![[5u8; 32].into()]));
			let hash6_1_2 = insert_non_best_block(&db, &hash6_1, 8, Some(vec![[6u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash7)), Some(vec![[3u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash8)), Some(vec![[3u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1)), Some(vec![[4u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1_1)), Some(vec![[5u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1_2)), Some(vec![[6u8; 32].into()]));
			let hash6_2 = insert_block(&db, &hash6_1, 8, Some(vec![[4u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash7)), Some(vec![[3u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash8)), Some(vec![[3u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1)), Some(vec![[4u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1_1)), Some(vec![[5u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1_2)), Some(vec![[6u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_2)), Some(vec![[4u8; 32].into()]));

			(hash7, hash8, hash6_1, hash6_2, hash6_1_1, hash6_1_2)
		};

		{
			// finalize block hash6_1
			db.finalize_header(BlockId::Hash(hash6_1)).unwrap();
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash7)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash8)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1)), Some(vec![[4u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1_1)), Some(vec![[5u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1_2)), Some(vec![[6u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_2)), Some(vec![[4u8; 32].into()]));
			// finalize block hash6_2
			db.finalize_header(BlockId::Hash(hash6_2)).unwrap();
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash7)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash8)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1)), Some(vec![[4u8; 32].into()]));
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1_1)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_1_2)), None);
			assert_eq!(db.cache().authorities_at(BlockId::Hash(hash6_2)), Some(vec![[4u8; 32].into()]));
		}
	}
}
