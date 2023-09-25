// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! In memory client backend

use parking_lot::RwLock;
use sp_blockchain::{CachedHeaderMetadata, HeaderMetadata};
use sp_core::{
	offchain::storage::InMemOffchainStorage as OffchainStorage, storage::well_known_keys,
};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, HashingFor, Header as HeaderT, NumberFor, Zero},
	Justification, Justifications, StateVersion, Storage,
};
use sp_state_machine::{
	Backend as StateBackend, BackendTransaction, ChildStorageCollection, InMemoryBackend,
	IndexOperation, StorageCollection,
};
use std::{
	collections::{HashMap, HashSet},
	ptr,
	sync::Arc,
};

use crate::{
	backend::{self, NewBlockState},
	blockchain::{self, BlockStatus, HeaderBackend},
	leaves::LeafSet,
	UsageInfo,
};

struct PendingBlock<B: BlockT> {
	block: StoredBlock<B>,
	state: NewBlockState,
}

#[derive(PartialEq, Eq, Clone)]
enum StoredBlock<B: BlockT> {
	Header(B::Header, Option<Justifications>),
	Full(B, Option<Justifications>),
}

impl<B: BlockT> StoredBlock<B> {
	fn new(
		header: B::Header,
		body: Option<Vec<B::Extrinsic>>,
		just: Option<Justifications>,
	) -> Self {
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

	fn justifications(&self) -> Option<&Justifications> {
		match *self {
			StoredBlock::Header(_, ref j) | StoredBlock::Full(_, ref j) => j.as_ref(),
		}
	}

	fn extrinsics(&self) -> Option<&[B::Extrinsic]> {
		match *self {
			StoredBlock::Header(_, _) => None,
			StoredBlock::Full(ref b, _) => Some(b.extrinsics()),
		}
	}

	fn into_inner(self) -> (B::Header, Option<Vec<B::Extrinsic>>, Option<Justifications>) {
		match self {
			StoredBlock::Header(header, just) => (header, None, just),
			StoredBlock::Full(block, just) => {
				let (header, body) = block.deconstruct();
				(header, Some(body), just)
			},
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
	leaves: LeafSet<Block::Hash, NumberFor<Block>>,
	aux: HashMap<Vec<u8>, Vec<u8>>,
}

/// In-memory blockchain. Supports concurrent reads.
#[derive(Clone)]
pub struct Blockchain<Block: BlockT> {
	storage: Arc<RwLock<BlockchainStorage<Block>>>,
}

impl<Block: BlockT> Default for Blockchain<Block> {
	fn default() -> Self {
		Self::new()
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
		let storage = Arc::new(RwLock::new(BlockchainStorage {
			blocks: HashMap::new(),
			hashes: HashMap::new(),
			best_hash: Default::default(),
			best_number: Zero::zero(),
			finalized_hash: Default::default(),
			finalized_number: Zero::zero(),
			genesis_hash: Default::default(),
			header_cht_roots: HashMap::new(),
			leaves: LeafSet::new(),
			aux: HashMap::new(),
		}));
		Blockchain { storage }
	}

	/// Insert a block header and associated data.
	pub fn insert(
		&self,
		hash: Block::Hash,
		header: <Block as BlockT>::Header,
		justifications: Option<Justifications>,
		body: Option<Vec<<Block as BlockT>::Extrinsic>>,
		new_state: NewBlockState,
	) -> sp_blockchain::Result<()> {
		let number = *header.number();
		if new_state.is_best() {
			self.apply_head(&header)?;
		}

		{
			let mut storage = self.storage.write();
			storage.leaves.import(hash, number, *header.parent_hash());
			storage.blocks.insert(hash, StoredBlock::new(header, body, justifications));

			if let NewBlockState::Final = new_state {
				storage.finalized_hash = hash;
				storage.finalized_number = number;
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
		// Check ptr equality first to avoid double read locks.
		if ptr::eq(self, other) {
			return true
		}
		self.canon_equals_to(other) && self.storage.read().blocks == other.storage.read().blocks
	}

	/// Compare canonical chain to other canonical chain.
	pub fn canon_equals_to(&self, other: &Self) -> bool {
		// Check ptr equality first to avoid double read locks.
		if ptr::eq(self, other) {
			return true
		}
		let this = self.storage.read();
		let other = other.storage.read();
		this.hashes == other.hashes &&
			this.best_hash == other.best_hash &&
			this.best_number == other.best_number &&
			this.genesis_hash == other.genesis_hash
	}

	/// Insert header CHT root.
	pub fn insert_cht_root(&self, block: NumberFor<Block>, cht_root: Block::Hash) {
		self.storage.write().header_cht_roots.insert(block, cht_root);
	}

	/// Set an existing block as head.
	pub fn set_head(&self, hash: Block::Hash) -> sp_blockchain::Result<()> {
		let header = self
			.header(hash)?
			.ok_or_else(|| sp_blockchain::Error::UnknownBlock(format!("{}", hash)))?;

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

		storage.best_hash = hash;
		storage.best_number = *number;
		storage.hashes.insert(*number, hash);

		Ok(())
	}

	fn finalize_header(
		&self,
		block: Block::Hash,
		justification: Option<Justification>,
	) -> sp_blockchain::Result<()> {
		let mut storage = self.storage.write();
		storage.finalized_hash = block;

		if justification.is_some() {
			let block = storage
				.blocks
				.get_mut(&block)
				.expect("hash was fetched from a block in the db; qed");

			let block_justifications = match block {
				StoredBlock::Header(_, ref mut j) | StoredBlock::Full(_, ref mut j) => j,
			};

			*block_justifications = justification.map(Justifications::from);
		}

		Ok(())
	}

	fn append_justification(
		&self,
		hash: Block::Hash,
		justification: Justification,
	) -> sp_blockchain::Result<()> {
		let mut storage = self.storage.write();

		let block = storage
			.blocks
			.get_mut(&hash)
			.expect("hash was fetched from a block in the db; qed");

		let block_justifications = match block {
			StoredBlock::Header(_, ref mut j) | StoredBlock::Full(_, ref mut j) => j,
		};

		if let Some(stored_justifications) = block_justifications {
			if !stored_justifications.append(justification) {
				return Err(sp_blockchain::Error::BadJustification(
					"Duplicate consensus engine ID".into(),
				))
			}
		} else {
			*block_justifications = Some(Justifications::from(justification));
		};

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
	fn header(
		&self,
		hash: Block::Hash,
	) -> sp_blockchain::Result<Option<<Block as BlockT>::Header>> {
		Ok(self.storage.read().blocks.get(&hash).map(|b| b.header().clone()))
	}

	fn info(&self) -> blockchain::Info<Block> {
		let storage = self.storage.read();
		blockchain::Info {
			best_hash: storage.best_hash,
			best_number: storage.best_number,
			genesis_hash: storage.genesis_hash,
			finalized_hash: storage.finalized_hash,
			finalized_number: storage.finalized_number,
			finalized_state: if storage.finalized_hash != Default::default() {
				Some((storage.finalized_hash, storage.finalized_number))
			} else {
				None
			},
			number_leaves: storage.leaves.count(),
			block_gap: None,
		}
	}

	fn status(&self, hash: Block::Hash) -> sp_blockchain::Result<BlockStatus> {
		match self.storage.read().blocks.contains_key(&hash) {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	fn number(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<NumberFor<Block>>> {
		Ok(self.storage.read().blocks.get(&hash).map(|b| *b.header().number()))
	}

	fn hash(
		&self,
		number: <<Block as BlockT>::Header as HeaderT>::Number,
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		Ok(self.id(BlockId::Number(number)))
	}
}

impl<Block: BlockT> HeaderMetadata<Block> for Blockchain<Block> {
	type Error = sp_blockchain::Error;

	fn header_metadata(
		&self,
		hash: Block::Hash,
	) -> Result<CachedHeaderMetadata<Block>, Self::Error> {
		self.header(hash)?
			.map(|header| CachedHeaderMetadata::from(&header))
			.ok_or_else(|| {
				sp_blockchain::Error::UnknownBlock(format!("header not found: {}", hash))
			})
	}

	fn insert_header_metadata(&self, _hash: Block::Hash, _metadata: CachedHeaderMetadata<Block>) {
		// No need to implement.
	}
	fn remove_header_metadata(&self, _hash: Block::Hash) {
		// No need to implement.
	}
}

impl<Block: BlockT> blockchain::Backend<Block> for Blockchain<Block> {
	fn body(
		&self,
		hash: Block::Hash,
	) -> sp_blockchain::Result<Option<Vec<<Block as BlockT>::Extrinsic>>> {
		Ok(self
			.storage
			.read()
			.blocks
			.get(&hash)
			.and_then(|b| b.extrinsics().map(|x| x.to_vec())))
	}

	fn justifications(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<Justifications>> {
		Ok(self.storage.read().blocks.get(&hash).and_then(|b| b.justifications().cloned()))
	}

	fn last_finalized(&self) -> sp_blockchain::Result<Block::Hash> {
		Ok(self.storage.read().finalized_hash)
	}

	fn leaves(&self) -> sp_blockchain::Result<Vec<Block::Hash>> {
		Ok(self.storage.read().leaves.hashes())
	}

	fn displaced_leaves_after_finalizing(
		&self,
		block_number: NumberFor<Block>,
	) -> sp_blockchain::Result<Vec<Block::Hash>> {
		Ok(self
			.storage
			.read()
			.leaves
			.displaced_by_finalize_height(block_number)
			.leaves()
			.cloned()
			.collect::<Vec<_>>())
	}

	fn children(&self, _parent_hash: Block::Hash) -> sp_blockchain::Result<Vec<Block::Hash>> {
		unimplemented!()
	}

	fn indexed_transaction(&self, _hash: Block::Hash) -> sp_blockchain::Result<Option<Vec<u8>>> {
		unimplemented!("Not supported by the in-mem backend.")
	}

	fn block_indexed_body(
		&self,
		_hash: Block::Hash,
	) -> sp_blockchain::Result<Option<Vec<Vec<u8>>>> {
		unimplemented!("Not supported by the in-mem backend.")
	}
}

impl<Block: BlockT> backend::AuxStore for Blockchain<Block> {
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item = &'a (&'c [u8], &'c [u8])>,
		D: IntoIterator<Item = &'a &'b [u8]>,
	>(
		&self,
		insert: I,
		delete: D,
	) -> sp_blockchain::Result<()> {
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

/// In-memory operation.
pub struct BlockImportOperation<Block: BlockT> {
	pending_block: Option<PendingBlock<Block>>,
	old_state: InMemoryBackend<HashingFor<Block>>,
	new_state: Option<BackendTransaction<HashingFor<Block>>>,
	aux: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	finalized_blocks: Vec<(Block::Hash, Option<Justification>)>,
	set_head: Option<Block::Hash>,
}

impl<Block: BlockT> BlockImportOperation<Block> {
	fn apply_storage(
		&mut self,
		storage: Storage,
		commit: bool,
		state_version: StateVersion,
	) -> sp_blockchain::Result<Block::Hash> {
		check_genesis_storage(&storage)?;

		let child_delta = storage.children_default.values().map(|child_content| {
			(
				&child_content.child_info,
				child_content.data.iter().map(|(k, v)| (k.as_ref(), Some(v.as_ref()))),
			)
		});

		let (root, transaction) = self.old_state.full_storage_root(
			storage.top.iter().map(|(k, v)| (k.as_ref(), Some(v.as_ref()))),
			child_delta,
			state_version,
		);

		if commit {
			self.new_state = Some(transaction);
		}
		Ok(root)
	}
}

impl<Block: BlockT> backend::BlockImportOperation<Block> for BlockImportOperation<Block> {
	type State = InMemoryBackend<HashingFor<Block>>;

	fn state(&self) -> sp_blockchain::Result<Option<&Self::State>> {
		Ok(Some(&self.old_state))
	}

	fn set_block_data(
		&mut self,
		header: <Block as BlockT>::Header,
		body: Option<Vec<<Block as BlockT>::Extrinsic>>,
		_indexed_body: Option<Vec<Vec<u8>>>,
		justifications: Option<Justifications>,
		state: NewBlockState,
	) -> sp_blockchain::Result<()> {
		assert!(self.pending_block.is_none(), "Only one block per operation is allowed");
		self.pending_block =
			Some(PendingBlock { block: StoredBlock::new(header, body, justifications), state });
		Ok(())
	}

	fn update_db_storage(
		&mut self,
		update: BackendTransaction<HashingFor<Block>>,
	) -> sp_blockchain::Result<()> {
		self.new_state = Some(update);
		Ok(())
	}

	fn set_genesis_state(
		&mut self,
		storage: Storage,
		commit: bool,
		state_version: StateVersion,
	) -> sp_blockchain::Result<Block::Hash> {
		self.apply_storage(storage, commit, state_version)
	}

	fn reset_storage(
		&mut self,
		storage: Storage,
		state_version: StateVersion,
	) -> sp_blockchain::Result<Block::Hash> {
		self.apply_storage(storage, true, state_version)
	}

	fn insert_aux<I>(&mut self, ops: I) -> sp_blockchain::Result<()>
	where
		I: IntoIterator<Item = (Vec<u8>, Option<Vec<u8>>)>,
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
		hash: Block::Hash,
		justification: Option<Justification>,
	) -> sp_blockchain::Result<()> {
		self.finalized_blocks.push((hash, justification));
		Ok(())
	}

	fn mark_head(&mut self, hash: Block::Hash) -> sp_blockchain::Result<()> {
		assert!(self.pending_block.is_none(), "Only one set block per operation is allowed");
		self.set_head = Some(hash);
		Ok(())
	}

	fn update_transaction_index(
		&mut self,
		_index: Vec<IndexOperation>,
	) -> sp_blockchain::Result<()> {
		Ok(())
	}
}

/// In-memory backend. Keeps all states and blocks in memory.
///
/// > **Warning**: Doesn't support all the features necessary for a proper database. Only use this
/// > struct for testing purposes. Do **NOT** use in production.
pub struct Backend<Block: BlockT> {
	states: RwLock<HashMap<Block::Hash, InMemoryBackend<HashingFor<Block>>>>,
	blockchain: Blockchain<Block>,
	import_lock: RwLock<()>,
	pinned_blocks: RwLock<HashMap<Block::Hash, i64>>,
}

impl<Block: BlockT> Backend<Block> {
	/// Create a new instance of in-mem backend.
	///
	/// # Warning
	///
	/// For testing purposes only!
	pub fn new() -> Self {
		Backend {
			states: RwLock::new(HashMap::new()),
			blockchain: Blockchain::new(),
			import_lock: Default::default(),
			pinned_blocks: Default::default(),
		}
	}

	/// Return the number of references active for a pinned block.
	///
	/// # Warning
	///
	/// For testing purposes only!
	pub fn pin_refs(&self, hash: &<Block as BlockT>::Hash) -> Option<i64> {
		let blocks = self.pinned_blocks.read();
		blocks.get(hash).map(|value| *value)
	}
}

impl<Block: BlockT> backend::AuxStore for Backend<Block> {
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item = &'a (&'c [u8], &'c [u8])>,
		D: IntoIterator<Item = &'a &'b [u8]>,
	>(
		&self,
		insert: I,
		delete: D,
	) -> sp_blockchain::Result<()> {
		self.blockchain.insert_aux(insert, delete)
	}

	fn get_aux(&self, key: &[u8]) -> sp_blockchain::Result<Option<Vec<u8>>> {
		self.blockchain.get_aux(key)
	}
}

impl<Block: BlockT> backend::Backend<Block> for Backend<Block> {
	type BlockImportOperation = BlockImportOperation<Block>;
	type Blockchain = Blockchain<Block>;
	type State = InMemoryBackend<HashingFor<Block>>;
	type OffchainStorage = OffchainStorage;

	fn begin_operation(&self) -> sp_blockchain::Result<Self::BlockImportOperation> {
		let old_state = self.state_at(Default::default())?;
		Ok(BlockImportOperation {
			pending_block: None,
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
		block: Block::Hash,
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
		hash: Block::Hash,
		justification: Option<Justification>,
	) -> sp_blockchain::Result<()> {
		self.blockchain.finalize_header(hash, justification)
	}

	fn append_justification(
		&self,
		hash: Block::Hash,
		justification: Justification,
	) -> sp_blockchain::Result<()> {
		self.blockchain.append_justification(hash, justification)
	}

	fn blockchain(&self) -> &Self::Blockchain {
		&self.blockchain
	}

	fn usage_info(&self) -> Option<UsageInfo> {
		None
	}

	fn offchain_storage(&self) -> Option<Self::OffchainStorage> {
		None
	}

	fn state_at(&self, hash: Block::Hash) -> sp_blockchain::Result<Self::State> {
		if hash == Default::default() {
			return Ok(Self::State::default())
		}

		self.states
			.read()
			.get(&hash)
			.cloned()
			.ok_or_else(|| sp_blockchain::Error::UnknownBlock(format!("{}", hash)))
	}

	fn revert(
		&self,
		_n: NumberFor<Block>,
		_revert_finalized: bool,
	) -> sp_blockchain::Result<(NumberFor<Block>, HashSet<Block::Hash>)> {
		Ok((Zero::zero(), HashSet::new()))
	}

	fn remove_leaf_block(&self, _hash: Block::Hash) -> sp_blockchain::Result<()> {
		Ok(())
	}

	fn get_import_lock(&self) -> &RwLock<()> {
		&self.import_lock
	}

	fn requires_full_sync(&self) -> bool {
		false
	}

	fn pin_block(&self, hash: <Block as BlockT>::Hash) -> blockchain::Result<()> {
		let mut blocks = self.pinned_blocks.write();
		*blocks.entry(hash).or_default() += 1;
		Ok(())
	}

	fn unpin_block(&self, hash: <Block as BlockT>::Hash) {
		let mut blocks = self.pinned_blocks.write();
		blocks.entry(hash).and_modify(|counter| *counter -= 1).or_insert(-1);
	}
}

impl<Block: BlockT> backend::LocalBackend<Block> for Backend<Block> {}

/// Check that genesis storage is valid.
pub fn check_genesis_storage(storage: &Storage) -> sp_blockchain::Result<()> {
	if storage.top.iter().any(|(k, _)| well_known_keys::is_child_storage_key(k)) {
		return Err(sp_blockchain::Error::InvalidState)
	}

	if storage
		.children_default
		.keys()
		.any(|child_key| !well_known_keys::is_child_storage_key(child_key))
	{
		return Err(sp_blockchain::Error::InvalidState)
	}

	Ok(())
}

#[cfg(test)]
mod tests {
	use crate::{in_mem::Blockchain, NewBlockState};
	use sp_api::HeaderT;
	use sp_blockchain::Backend;
	use sp_runtime::{ConsensusEngineId, Justifications};
	use substrate_test_runtime::{Block, Header, H256};

	pub const ID1: ConsensusEngineId = *b"TST1";
	pub const ID2: ConsensusEngineId = *b"TST2";

	fn header(number: u64) -> Header {
		let parent_hash = match number {
			0 => Default::default(),
			_ => header(number - 1).hash(),
		};
		Header::new(
			number,
			H256::from_low_u64_be(0),
			H256::from_low_u64_be(0),
			parent_hash,
			Default::default(),
		)
	}

	fn test_blockchain() -> Blockchain<Block> {
		let blockchain = Blockchain::<Block>::new();
		let just0 = Some(Justifications::from((ID1, vec![0])));
		let just1 = Some(Justifications::from((ID1, vec![1])));
		let just2 = None;
		let just3 = Some(Justifications::from((ID1, vec![3])));
		blockchain
			.insert(header(0).hash(), header(0), just0, None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(1).hash(), header(1), just1, None, NewBlockState::Final)
			.unwrap();
		blockchain
			.insert(header(2).hash(), header(2), just2, None, NewBlockState::Best)
			.unwrap();
		blockchain
			.insert(header(3).hash(), header(3), just3, None, NewBlockState::Final)
			.unwrap();
		blockchain
	}

	#[test]
	fn append_and_retrieve_justifications() {
		let blockchain = test_blockchain();
		let last_finalized = blockchain.last_finalized().unwrap();

		blockchain.append_justification(last_finalized, (ID2, vec![4])).unwrap();
		let justifications = {
			let mut just = Justifications::from((ID1, vec![3]));
			just.append((ID2, vec![4]));
			just
		};
		assert_eq!(blockchain.justifications(last_finalized).unwrap(), Some(justifications));
	}

	#[test]
	fn store_duplicate_justifications_is_forbidden() {
		let blockchain = test_blockchain();
		let last_finalized = blockchain.last_finalized().unwrap();

		blockchain.append_justification(last_finalized, (ID2, vec![0])).unwrap();
		assert!(matches!(
			blockchain.append_justification(last_finalized, (ID2, vec![1])),
			Err(sp_blockchain::Error::BadJustification(_)),
		));
	}
}
