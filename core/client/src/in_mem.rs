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

//! In memory client backend

use std::collections::HashMap;
use std::sync::Arc;
use parking_lot::{RwLock, Mutex};
use primitives::{ChangesTrieConfiguration, storage::well_known_keys};
use runtime_primitives::generic::{BlockId, DigestItem};
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Zero, NumberFor};
use runtime_primitives::{Justification, StorageOverlay, ChildrenStorageOverlay};
use state_machine::backend::{Backend as StateBackend, InMemory};
use state_machine::{self, InMemoryChangesTrieStorage, ChangesTrieAnchorBlockId};
use hash_db::Hasher;
use trie::MemoryDB;
use consensus::well_known_cache_keys::Id as CacheKeyId;

use crate::error;
use crate::backend::{self, NewBlockState, StorageCollection, ChildStorageCollection};
use crate::light;
use crate::leaves::LeafSet;
use crate::blockchain::{self, BlockStatus, HeaderBackend};

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
	) -> crate::error::Result<()> {
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
	pub fn set_head(&self, id: BlockId<Block>) -> error::Result<()> {
		let header = match self.header(id)? {
			Some(h) => h,
			None => return Err(error::Error::UnknownBlock(format!("{}", id))),
		};

		self.apply_head(&header)
	}

	fn apply_head(&self, header: &<Block as BlockT>::Header) -> error::Result<()> {
		let hash = header.hash();
		let number = header.number();

		// Note: this may lock storage, so it must happen before obtaining storage
		// write lock.
		let best_tree_route = {
			let best_hash = self.storage.read().best_hash;
			if &best_hash == header.parent_hash() {
				None
			} else {
				let route = crate::blockchain::tree_route(
					self,
					BlockId::Hash(best_hash),
					BlockId::Hash(*header.parent_hash()),
				)?;
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

	fn finalize_header(&self, id: BlockId<Block>, justification: Option<Justification>) -> error::Result<()> {
		let hash = match self.header(id)? {
			Some(h) => h.hash(),
			None => return Err(error::Error::UnknownBlock(format!("{}", id))),
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
	fn header(&self, id: BlockId<Block>) -> error::Result<Option<<Block as BlockT>::Header>> {
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
		}
	}

	fn status(&self, id: BlockId<Block>) -> error::Result<BlockStatus> {
		match self.id(id).map_or(false, |hash| self.storage.read().blocks.contains_key(&hash)) {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	fn number(&self, hash: Block::Hash) -> error::Result<Option<NumberFor<Block>>> {
		Ok(self.storage.read().blocks.get(&hash).map(|b| *b.header().number()))
	}

	fn hash(&self, number: <<Block as BlockT>::Header as HeaderT>::Number) -> error::Result<Option<Block::Hash>> {
		Ok(self.id(BlockId::Number(number)))
	}
}


impl<Block: BlockT> blockchain::Backend<Block> for Blockchain<Block> {
	fn body(&self, id: BlockId<Block>) -> error::Result<Option<Vec<<Block as BlockT>::Extrinsic>>> {
		Ok(self.id(id).and_then(|hash| {
			self.storage.read().blocks.get(&hash)
				.and_then(|b| b.extrinsics().map(|x| x.to_vec()))
		}))
	}

	fn justification(&self, id: BlockId<Block>) -> error::Result<Option<Justification>> {
		Ok(self.id(id).and_then(|hash| self.storage.read().blocks.get(&hash).and_then(|b|
			b.justification().map(|x| x.clone()))
		))
	}

	fn last_finalized(&self) -> error::Result<Block::Hash> {
		Ok(self.storage.read().finalized_hash.clone())
	}

	fn cache(&self) -> Option<Arc<dyn blockchain::Cache<Block>>> {
		None
	}

	fn leaves(&self) -> error::Result<Vec<Block::Hash>> {
		Ok(self.storage.read().leaves.hashes())
	}

	fn children(&self, _parent_hash: Block::Hash) -> error::Result<Vec<Block::Hash>> {
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
	>(&self, insert: I, delete: D) -> error::Result<()> {
		let mut storage = self.storage.write();
		for (k, v) in insert {
			storage.aux.insert(k.to_vec(), v.to_vec());
		}
		for k in delete {
			storage.aux.remove(*k);
		}
		Ok(())
	}

	fn get_aux(&self, key: &[u8]) -> error::Result<Option<Vec<u8>>> {
		Ok(self.storage.read().aux.get(key).cloned())
	}
}

impl<Block: BlockT> light::blockchain::Storage<Block> for Blockchain<Block>
	where
		Block::Hash: From<[u8; 32]>,
{
	fn import_header(
		&self,
		header: Block::Header,
		_cache: HashMap<CacheKeyId, Vec<u8>>,
		state: NewBlockState,
		aux_ops: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	) -> error::Result<()> {
		let hash = header.hash();
		self.insert(hash, header, None, None, state)?;

		self.write_aux(aux_ops);
		Ok(())
	}

	fn set_head(&self, id: BlockId<Block>) -> error::Result<()> {
		Blockchain::set_head(self, id)
	}

	fn last_finalized(&self) -> error::Result<Block::Hash> {
		Ok(self.storage.read().finalized_hash.clone())
	}

	fn finalize_header(&self, id: BlockId<Block>) -> error::Result<()> {
		Blockchain::finalize_header(self, id, None)
	}

	fn header_cht_root(
		&self,
		_cht_size: NumberFor<Block>,
		block: NumberFor<Block>,
	) -> error::Result<Block::Hash> {
		self.storage.read().header_cht_roots.get(&block).cloned()
			.ok_or_else(|| error::Error::Backend(format!("Header CHT for block {} not exists", block)))
	}

	fn changes_trie_cht_root(
		&self,
		_cht_size: NumberFor<Block>,
		block: NumberFor<Block>,
	) -> error::Result<Block::Hash> {
		self.storage.read().changes_trie_cht_roots.get(&block).cloned()
			.ok_or_else(|| error::Error::Backend(format!("Changes trie CHT for block {} not exists", block)))
	}

	fn cache(&self) -> Option<Arc<dyn blockchain::Cache<Block>>> {
		None
	}
}

/// In-memory operation.
pub struct BlockImportOperation<Block: BlockT, H: Hasher> {
	pending_block: Option<PendingBlock<Block>>,
	pending_cache: HashMap<CacheKeyId, Vec<u8>>,
	old_state: InMemory<H>,
	new_state: Option<InMemory<H>>,
	changes_trie_update: Option<MemoryDB<H>>,
	aux: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	finalized_blocks: Vec<(BlockId<Block>, Option<Justification>)>,
	set_head: Option<BlockId<Block>>,
}

impl<Block, H> backend::BlockImportOperation<Block, H> for BlockImportOperation<Block, H>
where
	Block: BlockT,
	H: Hasher<Out=Block::Hash>,

	H::Out: Ord,
{
	type State = InMemory<H>;

	fn state(&self) -> error::Result<Option<&Self::State>> {
		Ok(Some(&self.old_state))
	}

	fn set_block_data(
		&mut self,
		header: <Block as BlockT>::Header,
		body: Option<Vec<<Block as BlockT>::Extrinsic>>,
		justification: Option<Justification>,
		state: NewBlockState,
	) -> error::Result<()> {
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

	fn update_db_storage(&mut self, update: <InMemory<H> as StateBackend<H>>::Transaction) -> error::Result<()> {
		self.new_state = Some(self.old_state.update(update));
		Ok(())
	}

	fn update_changes_trie(&mut self, update: MemoryDB<H>) -> error::Result<()> {
		self.changes_trie_update = Some(update);
		Ok(())
	}

	fn reset_storage(&mut self, top: StorageOverlay, children: ChildrenStorageOverlay) -> error::Result<H::Out> {
		check_genesis_storage(&top, &children)?;

		let child_delta = children.into_iter()
			.map(|(storage_key, child_overlay)|
				(storage_key, child_overlay.into_iter().map(|(k, v)| (k, Some(v)))));

		let (root, transaction) = self.old_state.full_storage_root(
			top.into_iter().map(|(k, v)| (k, Some(v))),
			child_delta
		);

		self.new_state = Some(InMemory::from(transaction));
		Ok(root)
	}

	fn insert_aux<I>(&mut self, ops: I) -> error::Result<()>
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		self.aux.append(&mut ops.into_iter().collect());
		Ok(())
	}

	fn update_storage(
		&mut self,
		_update: StorageCollection,
		_child_update: ChildStorageCollection,
	) -> error::Result<()> {
		Ok(())
	}

	fn mark_finalized(&mut self, block: BlockId<Block>, justification: Option<Justification>) -> error::Result<()> {
		self.finalized_blocks.push((block, justification));
		Ok(())
	}

	fn mark_head(&mut self, block: BlockId<Block>) -> error::Result<()> {
		assert!(self.pending_block.is_none(), "Only one set block per operation is allowed");
		self.set_head = Some(block);
		Ok(())
	}
}

/// In-memory backend. Keeps all states and blocks in memory. Useful for testing.
pub struct Backend<Block, H>
where
	Block: BlockT,
	H: Hasher<Out=Block::Hash>,
	H::Out: Ord,
{
	states: RwLock<HashMap<Block::Hash, InMemory<H>>>,
	changes_trie_storage: ChangesTrieStorage<Block, H>,
	blockchain: Blockchain<Block>,
	import_lock: Mutex<()>,
}

impl<Block, H> Backend<Block, H>
where
	Block: BlockT,
	H: Hasher<Out=Block::Hash>,
	H::Out: Ord,
{
	/// Create a new instance of in-mem backend.
	pub fn new() -> Backend<Block, H> {
		Backend {
			states: RwLock::new(HashMap::new()),
			changes_trie_storage: ChangesTrieStorage(InMemoryChangesTrieStorage::new()),
			blockchain: Blockchain::new(),
			import_lock: Default::default(),
		}
	}
}

impl<Block, H> backend::AuxStore for Backend<Block, H>
where
	Block: BlockT,
	H: Hasher<Out=Block::Hash>,
	H::Out: Ord,
{
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> error::Result<()> {
		self.blockchain.insert_aux(insert, delete)
	}

	fn get_aux(&self, key: &[u8]) -> error::Result<Option<Vec<u8>>> {
		self.blockchain.get_aux(key)
	}
}

impl<Block, H> backend::Backend<Block, H> for Backend<Block, H>
where
	Block: BlockT,
	H: Hasher<Out=Block::Hash>,
	H::Out: Ord,
{
	type BlockImportOperation = BlockImportOperation<Block, H>;
	type Blockchain = Blockchain<Block>;
	type State = InMemory<H>;
	type ChangesTrieStorage = ChangesTrieStorage<Block, H>;

	fn begin_operation(&self) -> error::Result<Self::BlockImportOperation> {
		let old_state = self.state_at(BlockId::Hash(Default::default()))?;
		Ok(BlockImportOperation {
			pending_block: None,
			pending_cache: Default::default(),
			old_state,
			new_state: None,
			changes_trie_update: None,
			aux: Default::default(),
			finalized_blocks: Default::default(),
			set_head: None,
		})
	}

	fn begin_state_operation(&self, operation: &mut Self::BlockImportOperation, block: BlockId<Block>) -> error::Result<()> {
		operation.old_state = self.state_at(block)?;
		Ok(())
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation) -> error::Result<()> {
		if !operation.finalized_blocks.is_empty() {
			for (block, justification) in operation.finalized_blocks {
				self.blockchain.finalize_header(block, justification)?;
			}
		}

		if let Some(pending_block) = operation.pending_block {
			let old_state = &operation.old_state;
			let (header, body, justification) = pending_block.block.into_inner();

			let hash = header.hash();

			self.states.write().insert(hash, operation.new_state.unwrap_or_else(|| old_state.clone()));

			let maybe_changes_trie_root = header.digest().log(DigestItem::as_changes_trie_root).cloned();
			if let Some(changes_trie_root) = maybe_changes_trie_root {
				if let Some(changes_trie_update) = operation.changes_trie_update {
					self.changes_trie_storage.0.insert(
						*header.number(),
						changes_trie_root,
						changes_trie_update
					);
				}
			}

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

	fn finalize_block(&self, block: BlockId<Block>, justification: Option<Justification>) -> error::Result<()> {
		self.blockchain.finalize_header(block, justification)
	}

	fn blockchain(&self) -> &Self::Blockchain {
		&self.blockchain
	}

	fn used_state_cache_size(&self) -> Option<usize> {
		None
	}

	fn changes_trie_storage(&self) -> Option<&Self::ChangesTrieStorage> {
		Some(&self.changes_trie_storage)
	}

	fn state_at(&self, block: BlockId<Block>) -> error::Result<Self::State> {
		match block {
			BlockId::Hash(h) if h == Default::default() => {
				return Ok(Self::State::default());
			},
			_ => {},
		}

		match self.blockchain.id(block).and_then(|id| self.states.read().get(&id).cloned()) {
			Some(state) => Ok(state),
			None => Err(error::Error::UnknownBlock(format!("{}", block))),
		}
	}

	fn revert(&self, _n: NumberFor<Block>) -> error::Result<NumberFor<Block>> {
		Ok(Zero::zero())
	}

	fn get_import_lock(&self) -> &Mutex<()> {
		&self.import_lock
	}
}

impl<Block, H> backend::LocalBackend<Block, H> for Backend<Block, H>
where
	Block: BlockT,
	H: Hasher<Out=Block::Hash>,
	H::Out: Ord,
{}

impl<Block, H> backend::RemoteBackend<Block, H> for Backend<Block, H>
where
	Block: BlockT,
	H: Hasher<Out=Block::Hash>,
	H::Out: Ord,
{
	fn is_local_state_available(&self, block: &BlockId<Block>) -> bool {
		self.blockchain.expect_block_number_from_id(block)
			.map(|num| num.is_zero())
			.unwrap_or(false)
	}
}

/// Prunable in-memory changes trie storage.
pub struct ChangesTrieStorage<Block: BlockT, H: Hasher>(InMemoryChangesTrieStorage<H, NumberFor<Block>>);
impl<Block: BlockT, H: Hasher> backend::PrunableStateChangesTrieStorage<Block, H> for ChangesTrieStorage<Block, H> {
	fn oldest_changes_trie_block(
		&self,
		_config: &ChangesTrieConfiguration,
		_best_finalized: NumberFor<Block>,
	) -> NumberFor<Block> {
		Zero::zero()
	}
}

impl<Block, H> state_machine::ChangesTrieRootsStorage<H, NumberFor<Block>> for ChangesTrieStorage<Block, H>
	where
		Block: BlockT,
		H: Hasher,
{
	fn build_anchor(
		&self,
		_hash: H::Out,
	) -> Result<state_machine::ChangesTrieAnchorBlockId<H::Out, NumberFor<Block>>, String> {
		Err("Dummy implementation".into())
	}

	fn root(
		&self,
		_anchor: &ChangesTrieAnchorBlockId<H::Out, NumberFor<Block>>,
		_block: NumberFor<Block>,
	) -> Result<Option<H::Out>, String> {
		Err("Dummy implementation".into())
	}
}

impl<Block, H> state_machine::ChangesTrieStorage<H, NumberFor<Block>> for ChangesTrieStorage<Block, H>
	where
		Block: BlockT,
		H: Hasher,
{
	fn get(&self, _key: &H::Out, _prefix: &[u8]) -> Result<Option<state_machine::DBValue>, String> {
		Err("Dummy implementation".into())
	}
}

/// Check that genesis storage is valid.
pub fn check_genesis_storage(top: &StorageOverlay, children: &ChildrenStorageOverlay) -> error::Result<()> {
	if top.iter().any(|(k, _)| well_known_keys::is_child_storage_key(k)) {
		return Err(error::Error::GenesisInvalid.into());
	}

	if children.keys().any(|child_key| !well_known_keys::is_child_storage_key(&child_key)) {
		return Err(error::Error::GenesisInvalid.into());
	}

	Ok(())
}

#[cfg(test)]
mod tests {
	use std::sync::Arc;
	use test_client;
	use primitives::Blake2Hasher;

	type TestBackend = test_client::client::in_mem::Backend<test_client::runtime::Block, Blake2Hasher>;

	#[test]
	fn test_leaves_with_complex_block_tree() {
		let backend = Arc::new(TestBackend::new());

		test_client::trait_tests::test_leaves_for_backend(backend);
	}

	#[test]
	fn test_blockchain_query_by_number_gets_canonical() {
		let backend = Arc::new(TestBackend::new());

		test_client::trait_tests::test_blockchain_query_by_number_gets_canonical(backend);
	}
}
