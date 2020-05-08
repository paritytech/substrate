// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! In memory client backend

use std::collections::HashMap;
use std::sync::Arc;
use parking_lot::RwLock;
use sp_core::storage::well_known_keys;
use sp_core::offchain::storage::{
	InMemOffchainStorage as OffchainStorage
};
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, Zero, NumberFor, HashFor};
use sp_runtime::{Justification, Storage};
use sp_state_machine::{
	ChangesTrieTransaction, InMemoryBackend, Backend as StateBackend, StorageCollection,
	ChildStorageCollection,
};
use sp_blockchain::{CachedHeaderMetadata, HeaderMetadata};

use crate::{
	backend::{self, NewBlockState},
	blockchain::{
		self, BlockStatus, HeaderBackend, well_known_cache_keys::Id as CacheKeyId
	},
	UsageInfo,
	light,
	leaves::LeafSet,
};

struct PendingBlock<B: BlockT> {
	block: StoredBlock<B>,
	state: NewBlockState,
}

#[derive(PartialEq, Eq, Clone)]
enum StoredBlock<B: BlockT> {
	Header(B::Header, Option<Justification>),
	Full(B, Option<Justification>),
}

impl<B: BlockT> StoredBlock<B> {
	fn new(header: B::Header, body: Option<Vec<B::Extrinsic>>, just: Option<Justification>) -> Self {
		match body {
			Some(body) => StoredBlock::Full(B::new(header, body), just),
			None => StoredBlock::Header(header, just),
		}
	}

	fn header(&self) -> &B::Header {
		match *self {
			StoredBlock::Header(ref h, _) => h,
			StoredBlock::Full(ref b, _) => b.header(),
		}
	}

	fn justification(&self) -> Option<&Justification> {
		match *self {
			StoredBlock::Header(_, ref j) | StoredBlock::Full(_, ref j) => j.as_ref()
		}
	}

	fn extrinsics(&self) -> Option<&[B::Extrinsic]> {
		match *self {
			StoredBlock::Header(_, _) => None,
			StoredBlock::Full(ref b, _) => Some(b.extrinsics()),
		}
	}

	fn into_inner(self) -> (B::Header, Option<Vec<B::Extrinsic>>, Option<Justification>) {
		match self {
			StoredBlock::Header(header, just) => (header, None, just),
			StoredBlock::Full(block, just) => {
				let (header, body) = block.deconstruct();
				(header, Some(body), just)
			}
		}
	}
}

#[derive(Clone)]
struct BlockchainStorage<Block: BlockT> {
	blocks: HashMap<Block::Hash, StoredBlock<Block>>,
	hashes: HashMap<NumberFor<Block>, Block::Hash>,
	best_hash: Block::Hash,
	best_number: NumberFor<Block>,
	finalized_hash: Block::Hash,
	finalized_number: NumberFor<Block>,
	genesis_hash: Block::Hash,
	header_cht_roots: HashMap<NumberFor<Block>, Block::Hash>,
	changes_trie_cht_roots: HashMap<NumberFor<Block>, Block::Hash>,
	leaves: LeafSet<Block::Hash, NumberFor<Block>>,
	aux: HashMap<Vec<u8>, Vec<u8>>,
}

/// In-memory blockchain. Supports concurrent reads.
pub struct Blockchain<Block: BlockT> {
	storage: Arc<RwLock<BlockchainStorage<Block>>>,
}

impl<Block: BlockT + Clone> Clone for Blockchain<Block> {
	fn clone(&self) -> Self {
		let storage = Arc::new(RwLock::new(self.storage.read().clone()));
		Blockchain {
			storage: storage.clone(),
		}
	}
}

impl<Block: BlockT> Blockchain<Block> {
	/// Get header hash of given block.
	pub fn id(&self, id: BlockId<Block>) -> Option<Block::Hash> {
		match id {
			BlockId::Hash(h) => Some(h),
			BlockId::Number(n) => self.storage.read().hashes.get(&n).cloned(),
		}
	}

	/// Create new in-memory blockchain storage.
	pub fn new() -> Blockchain<Block> {
		let storage = Arc::new(RwLock::new(
			BlockchainStorage {
				blocks: HashMap::new(),
				hashes: HashMap::new(),
				best_hash: Default::default(),
				best_number: Zero::zero(),
				finalized_hash: Default::default(),
				finalized_number: Zero::zero(),
				genesis_hash: Default::default(),
				header_cht_roots: HashMap::new(),
				changes_trie_cht_roots: HashMap::new(),
				leaves: LeafSet::new(),
				aux: HashMap::new(),
			}));
		Blockchain {
			storage: storage.clone(),
		}
	}

	/// Insert a block header and associated data.
	pub fn insert(
		&self,
		hash: Block::Hash,
		header: <Block as BlockT>::Header,
		justification: Option<Justification>,
		body: Option<Vec<<Block as BlockT>::Extrinsic>>,
		new_state: NewBlockState,
	) -> sp_blockchain::Result<()> {
		let number = header.number().clone();
		if new_state.is_best() {
			self.apply_head(&header)?;
		}

		{
			let mut storage = self.storage.write();
			storage.leaves.import(hash.clone(), number.clone(), header.parent_hash().clone());
			storage.blocks.insert(hash.clone(), StoredBlock::new(header, body, justification));

			if let NewBlockState::Final = new_state {
				storage.finalized_hash = hash;
				storage.finalized_number = number.clone();
			}

			if number == Zero::zero() {
				storage.genesis_hash = hash;
			}
		}

		Ok(())
	}

	/// Get total number of blocks.
	pub fn blocks_count(&self) -> usize {
		self.storage.read().blocks.len()
	}

	/// Compare this blockchain with another in-mem blockchain
	pub fn equals_to(&self, other: &Self) -> bool {
		self.canon_equals_to(other) && self.storage.read().blocks == other.storage.read().blocks
	}

	/// Compare canonical chain to other canonical chain.
	pub fn canon_equals_to(&self, other: &Self) -> bool {
		let this = self.storage.read();
		let other = other.storage.read();
			this.hashes == other.hashes
			&& this.best_hash == other.best_hash
			&& this.best_number == other.best_number
			&& this.genesis_hash == other.genesis_hash
	}

	/// Insert header CHT root.
	pub fn insert_cht_root(&self, block: NumberFor<Block>, cht_root: Block::Hash) {
		self.storage.write().header_cht_roots.insert(block, cht_root);
	}

	/// Set an existing block as head.
	pub fn set_head(&self, id: BlockId<Block>) -> sp_blockchain::Result<()> {
		let header = match self.header(id)? {
			Some(h) => h,
			None => return Err(sp_blockchain::Error::UnknownBlock(format!("{}", id))),
		};

		self.apply_head(&header)
	}

	fn apply_head(&self, header: &<Block as BlockT>::Header) -> sp_blockchain::Result<()> {
		let hash = header.hash();
		let number = header.number();

		// Note: this may lock storage, so it must happen before obtaining storage
		// write lock.
		let best_tree_route = {
			let best_hash = self.storage.read().best_hash;
			if &best_hash == header.parent_hash() {
				None
			} else {
				let route = sp_blockchain::tree_route(self, best_hash, *header.parent_hash())?;
				Some(route)
			}
		};

		let mut storage = self.storage.write();

		if let Some(tree_route) = best_tree_route {
			// apply retraction and enaction when reorganizing up to parent hash
			let enacted = tree_route.enacted();

			for entry in enacted {
				storage.hashes.insert(entry.number, entry.hash);
			}

			for entry in tree_route.retracted().iter().skip(enacted.len()) {
				storage.hashes.remove(&entry.number);
			}
		}

		storage.best_hash = hash.clone();
		storage.best_number = number.clone();
		storage.hashes.insert(number.clone(), hash.clone());

		Ok(())
	}

	fn finalize_header(&self, id: BlockId<Block>, justification: Option<Justification>) -> sp_blockchain::Result<()> {
		let hash = match self.header(id)? {
			Some(h) => h.hash(),
			None => return Err(sp_blockchain::Error::UnknownBlock(format!("{}", id))),
		};

		let mut storage = self.storage.write();
		storage.finalized_hash = hash;

		if justification.is_some() {
			let block = storage.blocks.get_mut(&hash)
				.expect("hash was fetched from a block in the db; qed");

			let block_justification = match block {
				StoredBlock::Header(_, ref mut j) | StoredBlock::Full(_, ref mut j) => j
			};

			*block_justification = justification;
		}

		Ok(())
	}

	fn write_aux(&self, ops: Vec<(Vec<u8>, Option<Vec<u8>>)>) {
		let mut storage = self.storage.write();
		for (k, v) in ops {
			match v {
				Some(v) => storage.aux.insert(k, v),
				None => storage.aux.remove(&k),
			};
		}
	}
}

impl<Block: BlockT> HeaderBackend<Block> for Blockchain<Block> {
	fn header(&self, id: BlockId<Block>) -> sp_blockchain::Result<Option<<Block as BlockT>::Header>> {
		Ok(self.id(id).and_then(|hash| {
			self.storage.read().blocks.get(&hash).map(|b| b.header().clone())
		}))
	}

	fn info(&self) -> blockchain::Info<Block> {
		let storage = self.storage.read();
		blockchain::Info {
			best_hash: storage.best_hash,
			best_number: storage.best_number,
			genesis_hash: storage.genesis_hash,
			finalized_hash: storage.finalized_hash,
			finalized_number: storage.finalized_number,
			number_leaves: storage.leaves.count()
		}
	}

	fn status(&self, id: BlockId<Block>) -> sp_blockchain::Result<BlockStatus> {
		match self.id(id).map_or(false, |hash| self.storage.read().blocks.contains_key(&hash)) {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	fn number(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<NumberFor<Block>>> {
		Ok(self.storage.read().blocks.get(&hash).map(|b| *b.header().number()))
	}

	fn hash(&self, number: <<Block as BlockT>::Header as HeaderT>::Number) -> sp_blockchain::Result<Option<Block::Hash>> {
		Ok(self.id(BlockId::Number(number)))
	}
}

impl<Block: BlockT> HeaderMetadata<Block> for Blockchain<Block> {
	type Error = sp_blockchain::Error;

	fn header_metadata(&self, hash: Block::Hash) -> Result<CachedHeaderMetadata<Block>, Self::Error> {
		self.header(BlockId::hash(hash))?.map(|header| CachedHeaderMetadata::from(&header))
			.ok_or(sp_blockchain::Error::UnknownBlock(format!("header not found: {}", hash)))
	}

	fn insert_header_metadata(&self, _hash: Block::Hash, _metadata: CachedHeaderMetadata<Block>) {
		// No need to implement.
	}
	fn remove_header_metadata(&self, _hash: Block::Hash) {
		// No need to implement.
	}
}

impl<Block: BlockT> blockchain::Backend<Block> for Blockchain<Block> {
	fn body(&self, id: BlockId<Block>) -> sp_blockchain::Result<Option<Vec<<Block as BlockT>::Extrinsic>>> {
		Ok(self.id(id).and_then(|hash| {
			self.storage.read().blocks.get(&hash)
				.and_then(|b| b.extrinsics().map(|x| x.to_vec()))
		}))
	}

	fn justification(&self, id: BlockId<Block>) -> sp_blockchain::Result<Option<Justification>> {
		Ok(self.id(id).and_then(|hash| self.storage.read().blocks.get(&hash).and_then(|b|
			b.justification().map(|x| x.clone()))
		))
	}

	fn last_finalized(&self) -> sp_blockchain::Result<Block::Hash> {
		Ok(self.storage.read().finalized_hash.clone())
	}

	fn cache(&self) -> Option<Arc<dyn blockchain::Cache<Block>>> {
		None
	}

	fn leaves(&self) -> sp_blockchain::Result<Vec<Block::Hash>> {
		Ok(self.storage.read().leaves.hashes())
	}

	fn children(&self, _parent_hash: Block::Hash) -> sp_blockchain::Result<Vec<Block::Hash>> {
		unimplemented!()
	}
}

impl<Block: BlockT> blockchain::ProvideCache<Block> for Blockchain<Block> {
	fn cache(&self) -> Option<Arc<dyn blockchain::Cache<Block>>> {
		None
	}
}

impl<Block: BlockT> backend::AuxStore for Blockchain<Block> {
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> sp_blockchain::Result<()> {
		let mut storage = self.storage.write();
		for (k, v) in insert {
			storage.aux.insert(k.to_vec(), v.to_vec());
		}
		for k in delete {
			storage.aux.remove(*k);
		}
		Ok(())
	}

	fn get_aux(&self, key: &[u8]) -> sp_blockchain::Result<Option<Vec<u8>>> {
		Ok(self.storage.read().aux.get(key).cloned())
	}
}

impl<Block: BlockT> light::Storage<Block> for Blockchain<Block>
	where
		Block::Hash: From<[u8; 32]>,
{
	fn import_header(
		&self,
		header: Block::Header,
		_cache: HashMap<CacheKeyId, Vec<u8>>,
		state: NewBlockState,
		aux_ops: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	) -> sp_blockchain::Result<()> {
		let hash = header.hash();
		self.insert(hash, header, None, None, state)?;

		self.write_aux(aux_ops);
		Ok(())
	}

	fn set_head(&self, id: BlockId<Block>) -> sp_blockchain::Result<()> {
		Blockchain::set_head(self, id)
	}

	fn last_finalized(&self) -> sp_blockchain::Result<Block::Hash> {
		Ok(self.storage.read().finalized_hash.clone())
	}

	fn finalize_header(&self, id: BlockId<Block>) -> sp_blockchain::Result<()> {
		Blockchain::finalize_header(self, id, None)
	}

	fn header_cht_root(
		&self,
		_cht_size: NumberFor<Block>,
		block: NumberFor<Block>,
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.storage.read().header_cht_roots.get(&block).cloned()
			.ok_or_else(|| sp_blockchain::Error::Backend(format!("Header CHT for block {} not exists", block)))
			.map(Some)
	}

	fn changes_trie_cht_root(
		&self,
		_cht_size: NumberFor<Block>,
		block: NumberFor<Block>,
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.storage.read().changes_trie_cht_roots.get(&block).cloned()
			.ok_or_else(|| sp_blockchain::Error::Backend(format!("Changes trie CHT for block {} not exists", block)))
			.map(Some)
	}

	fn cache(&self) -> Option<Arc<dyn blockchain::Cache<Block>>> {
		None
	}

	fn usage_info(&self) -> Option<UsageInfo> {
		None
	}
}

/// In-memory operation.
pub struct BlockImportOperation<Block: BlockT> {
	pending_block: Option<PendingBlock<Block>>,
	pending_cache: HashMap<CacheKeyId, Vec<u8>>,
	old_state: InMemoryBackend<HashFor<Block>>,
	new_state: Option<<InMemoryBackend<HashFor<Block>> as StateBackend<HashFor<Block>>>::Transaction>,
	aux: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	finalized_blocks: Vec<(BlockId<Block>, Option<Justification>)>,
	set_head: Option<BlockId<Block>>,
}

impl<Block: BlockT> backend::BlockImportOperation<Block> for BlockImportOperation<Block> where
	Block::Hash: Ord,
{
	type State = InMemoryBackend<HashFor<Block>>;

	fn state(&self) -> sp_blockchain::Result<Option<&Self::State>> {
		Ok(Some(&self.old_state))
	}

	fn set_block_data(
		&mut self,
		header: <Block as BlockT>::Header,
		body: Option<Vec<<Block as BlockT>::Extrinsic>>,
		justification: Option<Justification>,
		state: NewBlockState,
	) -> sp_blockchain::Result<()> {
		assert!(self.pending_block.is_none(), "Only one block per operation is allowed");
		self.pending_block = Some(PendingBlock {
			block: StoredBlock::new(header, body, justification),
			state,
		});
		Ok(())
	}

	fn update_cache(&mut self, cache: HashMap<CacheKeyId, Vec<u8>>) {
		self.pending_cache = cache;
	}

	fn update_db_storage(
		&mut self,
		update: <InMemoryBackend<HashFor<Block>> as StateBackend<HashFor<Block>>>::Transaction,
	) -> sp_blockchain::Result<()> {
		self.new_state = Some(update);
		Ok(())
	}

	fn update_changes_trie(
		&mut self,
		_update: ChangesTrieTransaction<HashFor<Block>, NumberFor<Block>>,
	) -> sp_blockchain::Result<()> {
		Ok(())
	}

	fn reset_storage(&mut self, storage: Storage) -> sp_blockchain::Result<Block::Hash> {
		check_genesis_storage(&storage)?;

		let child_delta = storage.children_default.into_iter()
			.map(|(_storage_key, child_content)|
				(child_content.child_info, child_content.data.into_iter().map(|(k, v)| (k, Some(v)))));

		let (root, transaction) = self.old_state.full_storage_root(
			storage.top.into_iter().map(|(k, v)| (k, Some(v))),
			child_delta
		);

		self.new_state = Some(transaction);
		Ok(root)
	}

	fn insert_aux<I>(&mut self, ops: I) -> sp_blockchain::Result<()>
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		self.aux.append(&mut ops.into_iter().collect());
		Ok(())
	}

	fn update_storage(
		&mut self,
		_update: StorageCollection,
		_child_update: ChildStorageCollection,
	) -> sp_blockchain::Result<()> {
		Ok(())
	}

	fn mark_finalized(
		&mut self,
		block: BlockId<Block>,
		justification: Option<Justification>,
	) -> sp_blockchain::Result<()> {
		self.finalized_blocks.push((block, justification));
		Ok(())
	}

	fn mark_head(&mut self, block: BlockId<Block>) -> sp_blockchain::Result<()> {
		assert!(self.pending_block.is_none(), "Only one set block per operation is allowed");
		self.set_head = Some(block);
		Ok(())
	}
}

/// In-memory backend. Keeps all states and blocks in memory.
///
/// > **Warning**: Doesn't support all the features necessary for a proper database. Only use this
/// > struct for testing purposes. Do **NOT** use in production.
pub struct Backend<Block: BlockT> where Block::Hash: Ord {
	states: RwLock<HashMap<Block::Hash, InMemoryBackend<HashFor<Block>>>>,
	blockchain: Blockchain<Block>,
	import_lock: RwLock<()>,
}

impl<Block: BlockT> Backend<Block> where Block::Hash: Ord {
	/// Create a new instance of in-mem backend.
	pub fn new() -> Self {
		Backend {
			states: RwLock::new(HashMap::new()),
			blockchain: Blockchain::new(),
			import_lock: Default::default(),
		}
	}
}

impl<Block: BlockT> backend::AuxStore for Backend<Block> where Block::Hash: Ord {
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> sp_blockchain::Result<()> {
		self.blockchain.insert_aux(insert, delete)
	}

	fn get_aux(&self, key: &[u8]) -> sp_blockchain::Result<Option<Vec<u8>>> {
		self.blockchain.get_aux(key)
	}
}

impl<Block: BlockT> backend::Backend<Block> for Backend<Block> where Block::Hash: Ord {
	type BlockImportOperation = BlockImportOperation<Block>;
	type Blockchain = Blockchain<Block>;
	type State = InMemoryBackend<HashFor<Block>>;
	type OffchainStorage = OffchainStorage;

	fn begin_operation(&self) -> sp_blockchain::Result<Self::BlockImportOperation> {
		let old_state = self.state_at(BlockId::Hash(Default::default()))?;
		Ok(BlockImportOperation {
			pending_block: None,
			pending_cache: Default::default(),
			old_state,
			new_state: None,
			aux: Default::default(),
			finalized_blocks: Default::default(),
			set_head: None,
		})
	}

	fn begin_state_operation(
		&self,
		operation: &mut Self::BlockImportOperation,
		block: BlockId<Block>,
	) -> sp_blockchain::Result<()> {
		operation.old_state = self.state_at(block)?;
		Ok(())
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation) -> sp_blockchain::Result<()> {
		if !operation.finalized_blocks.is_empty() {
			for (block, justification) in operation.finalized_blocks {
				self.blockchain.finalize_header(block, justification)?;
			}
		}

		if let Some(pending_block) = operation.pending_block {
			let old_state = &operation.old_state;
			let (header, body, justification) = pending_block.block.into_inner();

			let hash = header.hash();

			let new_state = match operation.new_state {
				Some(state) => old_state.update_backend(*header.state_root(), state),
				None => old_state.clone(),
			};

			self.states.write().insert(hash, new_state);

			self.blockchain.insert(hash, header, justification, body, pending_block.state)?;
		}

		if !operation.aux.is_empty() {
			self.blockchain.write_aux(operation.aux);
		}

		if let Some(set_head) = operation.set_head {
			self.blockchain.set_head(set_head)?;
		}

		Ok(())
	}

	fn finalize_block(
		&self,
		block: BlockId<Block>,
		justification: Option<Justification>,
	) -> sp_blockchain::Result<()> {
		self.blockchain.finalize_header(block, justification)
	}

	fn blockchain(&self) -> &Self::Blockchain {
		&self.blockchain
	}

	fn usage_info(&self) -> Option<UsageInfo> {
		None
	}

	fn changes_trie_storage(&self) -> Option<&dyn backend::PrunableStateChangesTrieStorage<Block>> {
		None
	}

	fn offchain_storage(&self) -> Option<Self::OffchainStorage> {
		None
	}

	fn state_at(&self, block: BlockId<Block>) -> sp_blockchain::Result<Self::State> {
		match block {
			BlockId::Hash(h) if h == Default::default() => {
				return Ok(Self::State::default());
			},
			_ => {},
		}

		match self.blockchain.id(block).and_then(|id| self.states.read().get(&id).cloned()) {
			Some(state) => Ok(state),
			None => Err(sp_blockchain::Error::UnknownBlock(format!("{}", block))),
		}
	}

	fn revert(
		&self,
		_n: NumberFor<Block>,
		_revert_finalized: bool,
	) -> sp_blockchain::Result<NumberFor<Block>> {
		Ok(Zero::zero())
	}

	fn get_import_lock(&self) -> &RwLock<()> {
		&self.import_lock
	}
}

impl<Block: BlockT> backend::LocalBackend<Block> for Backend<Block> where Block::Hash: Ord {}

impl<Block: BlockT> backend::RemoteBackend<Block> for Backend<Block> where Block::Hash: Ord {
	fn is_local_state_available(&self, block: &BlockId<Block>) -> bool {
		self.blockchain.expect_block_number_from_id(block)
			.map(|num| num.is_zero())
			.unwrap_or(false)
	}

	fn remote_blockchain(&self) -> Arc<dyn light::RemoteBlockchain<Block>> {
		unimplemented!()
	}
}

/// Check that genesis storage is valid.
pub fn check_genesis_storage(storage: &Storage) -> sp_blockchain::Result<()> {
	if storage.top.iter().any(|(k, _)| well_known_keys::is_child_storage_key(k)) {
		return Err(sp_blockchain::Error::GenesisInvalid.into());
	}

	if storage.children_default.keys()
		.any(|child_key| !well_known_keys::is_child_storage_key(&child_key)) {
			return Err(sp_blockchain::Error::GenesisInvalid.into());
	}

	Ok(())
}
