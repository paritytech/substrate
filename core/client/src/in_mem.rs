// Copyright 2017 Parity Technologies (UK) Ltd.
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
use error;
use backend::{self, NewBlockState};
use light;
use primitives::AuthorityId;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Zero,
	NumberFor, As, Digest, DigestItem};
use runtime_primitives::bft::Justification;
use blockchain::{self, BlockStatus, HeaderBackend};
use state_machine::backend::{Backend as StateBackend, InMemory};
use state_machine::InMemoryChangesTrieStorage;
use patricia_trie::NodeCodec;
use hashdb::Hasher;
use heapsize::HeapSizeOf;
use memorydb::MemoryDB;

struct PendingBlock<B: BlockT> {
	block: StoredBlock<B>,
	state: NewBlockState,
}

#[derive(PartialEq, Eq, Clone)]
enum StoredBlock<B: BlockT> {
	Header(B::Header, Option<Justification<B::Hash>>),
	Full(B, Option<Justification<B::Hash>>),
}

impl<B: BlockT> StoredBlock<B> {
	fn new(header: B::Header, body: Option<Vec<B::Extrinsic>>, just: Option<Justification<B::Hash>>) -> Self {
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

	fn justification(&self) -> Option<&Justification<B::Hash>> {
		match *self {
			StoredBlock::Header(_, ref j) | StoredBlock::Full(_, ref j) => j.as_ref()
		}
	}

	fn extrinsics(&self) -> Option<&[B::Extrinsic]> {
		match *self {
			StoredBlock::Header(_, _) => None,
			StoredBlock::Full(ref b, _) => Some(b.extrinsics())
		}
	}

	fn into_inner(self) -> (B::Header, Option<Vec<B::Extrinsic>>, Option<Justification<B::Hash>>) {
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
	genesis_hash: Block::Hash,
	cht_roots: HashMap<NumberFor<Block>, Block::Hash>,
	leaves: Vec<Block::Hash>,
}

/// In-memory blockchain. Supports concurrent reads.
pub struct Blockchain<Block: BlockT> {
	storage: Arc<RwLock<BlockchainStorage<Block>>>,
	cache: Cache<Block>,
}

struct Cache<Block: BlockT> {
	storage: Arc<RwLock<BlockchainStorage<Block>>>,
	authorities_at: RwLock<HashMap<Block::Hash, Option<Vec<AuthorityId>>>>,
}

impl<Block: BlockT + Clone> Clone for Blockchain<Block> {
	fn clone(&self) -> Self {
		let storage = Arc::new(RwLock::new(self.storage.read().clone()));
		Blockchain {
			storage: storage.clone(),
			cache: Cache {
				storage,
				authorities_at: RwLock::new(self.cache.authorities_at.read().clone()),
			},
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
				genesis_hash: Default::default(),
				cht_roots: HashMap::new(),
				leaves: Vec::new(),
			}));
		Blockchain {
			storage: storage.clone(),
			cache: Cache {
				storage: storage,
				authorities_at: Default::default(),
			},
		}
	}

	/// Insert a block header and associated data.
	pub fn insert(
		&self,
		hash: Block::Hash,
		header: <Block as BlockT>::Header,
		justification: Option<Justification<Block::Hash>>,
		body: Option<Vec<<Block as BlockT>::Extrinsic>>,
		new_state: NewBlockState,
	) {
		// remember for after header is moved
		let number = header.number().clone();
		let parent_hash = header.parent_hash().clone();

		let mut storage = self.storage.write();
		storage.blocks.insert(hash.clone(), StoredBlock::new(header, body, justification));
		storage.hashes.insert(number, hash.clone());

		if new_state.is_best() {
			storage.best_hash = hash.clone();
			storage.best_number = number.clone();
		}
		if let NewBlockState::Final = new_state {
			storage.finalized_hash = hash;
		}

		if number == Zero::zero() {
			storage.genesis_hash = hash;
		}

		// TODO [snd] reduce complexity of leaf list update code

		// new block is leaf by definition. insert into leaf list.
		let mut maybe_insertion_position = None;
		for i in 0..storage.leaves.len() {
			let leaf_number = {
				storage.blocks.get(&storage.leaves[i]).expect("leaf hash must reference block in storage. q.e.d.").header().number().clone()
			};
			if leaf_number < number {
				maybe_insertion_position = Some(i);
				break;
			}
		}
		if let Some(insertion_position) = maybe_insertion_position {
			// TODO [snd] this moves all elements after `insert_at`. make it more efficient
			storage.leaves.insert(insertion_position, hash);
		} else {
			// new number is smallest or first entry in leaf list
			storage.leaves.push(hash);
		}

		// genesis block does not have parent to remove
		if number == Zero::zero() {
			return;
		}

		// either first block or inserted at end which means parent wasn't in leaf list
		if maybe_insertion_position.is_none() {
			return;
		}
		let insertion_position = maybe_insertion_position.expect("early return right above. q.e.d.");

		let parent_header = storage.blocks.get(&parent_hash).expect("parent hash must reference block in storage. q.e.d.").header().clone();

		// parent of new block is no longer leaf by definition. remove from leaf list if present
		// parent comes somewhere after child in leaf list since it's ordered by block number
		// descending.
		for i in insertion_position..storage.leaves.len() {
			let leaf_hash = storage.leaves[i];
			if leaf_hash == parent_header.hash() {
				// TODO [snd] this moves all elements after `i`. make it more efficient
				storage.leaves.remove(i);
				break;
			}
			let leaf_number = {
				storage.blocks.get(&leaf_hash).expect("leaf hash must reference block in storage. q.e.d.").header().number().clone()
			};
			if leaf_number < *parent_header.number() {
				// parent was not in leaf list
				break;
			}
		}

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

	/// Insert CHT root.
	pub fn insert_cht_root(&self, block: NumberFor<Block>, cht_root: Block::Hash) {
		self.storage.write().cht_roots.insert(block, cht_root);
	}

	fn finalize_header(&self, id: BlockId<Block>) -> error::Result<()> {
		let hash = match self.header(id)? {
			Some(h) => h.hash(),
			None => return Err(error::ErrorKind::UnknownBlock(format!("{}", id)).into()),
		};

		self.storage.write().finalized_hash = hash;
		Ok(())
	}
}

impl<Block: BlockT> HeaderBackend<Block> for Blockchain<Block> {
	fn header(&self, id: BlockId<Block>) -> error::Result<Option<<Block as BlockT>::Header>> {
		Ok(self.id(id).and_then(|hash| {
			self.storage.read().blocks.get(&hash).map(|b| b.header().clone())
		}))
	}

	fn info(&self) -> error::Result<blockchain::Info<Block>> {
		let storage = self.storage.read();
		Ok(blockchain::Info {
			best_hash: storage.best_hash,
			best_number: storage.best_number,
			genesis_hash: storage.genesis_hash,
			finalized_hash: storage.finalized_hash,
		})
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

	fn justification(&self, id: BlockId<Block>) -> error::Result<Option<Justification<Block::Hash>>> {
		Ok(self.id(id).and_then(|hash| self.storage.read().blocks.get(&hash).and_then(|b|
			b.justification().map(|x| x.clone()))
		))
	}

	fn last_finalized(&self) -> error::Result<Block::Hash> {
		Ok(self.storage.read().finalized_hash.clone())
	}

	fn cache(&self) -> Option<&blockchain::Cache<Block>> {
		Some(&self.cache)
	}

	fn leaves(&self) -> error::Result<Vec<Block::Hash>> {
		// TODO [snd] get rid of this clone
		Ok(self.storage.read().leaves.clone())
	}
}

impl<Block: BlockT> light::blockchain::Storage<Block> for Blockchain<Block>
	where
		Block::Hash: From<[u8; 32]>,
{
	fn import_header(
		&self,
		header: Block::Header,
		authorities: Option<Vec<AuthorityId>>,
		state: NewBlockState,
	) -> error::Result<()> {
		let hash = header.hash();
		let parent_hash = *header.parent_hash();
		self.insert(hash, header, None, None, state);
		if state.is_best() {
			self.cache.insert(parent_hash, authorities);
		}

		Ok(())
	}

	fn last_finalized(&self) -> error::Result<Block::Hash> {
		Ok(self.storage.read().finalized_hash.clone())
	}

	fn finalize_header(&self, id: BlockId<Block>) -> error::Result<()> {
		Blockchain::finalize_header(self, id)
	}

	fn cht_root(&self, _cht_size: u64, block: NumberFor<Block>) -> error::Result<Block::Hash> {
		self.storage.read().cht_roots.get(&block).cloned()
			.ok_or_else(|| error::ErrorKind::Backend(format!("CHT for block {} not exists", block)).into())
	}

	fn cache(&self) -> Option<&blockchain::Cache<Block>> {
		Some(&self.cache)
	}
}

/// In-memory operation.
pub struct BlockImportOperation<Block: BlockT, H: Hasher, C: NodeCodec<H>> {
	pending_block: Option<PendingBlock<Block>>,
	pending_authorities: Option<Vec<AuthorityId>>,
	old_state: InMemory<H, C>,
	new_state: Option<InMemory<H, C>>,
	changes_trie_update: Option<MemoryDB<H>>,
}

impl<Block, H, C> backend::BlockImportOperation<Block, H, C> for BlockImportOperation<Block, H, C>
where
	Block: BlockT,
	H: Hasher,
	C: NodeCodec<H>,
	H::Out: HeapSizeOf,
{
	type State = InMemory<H, C>;

	fn state(&self) -> error::Result<Option<&Self::State>> {
		Ok(Some(&self.old_state))
	}

	fn set_block_data(
		&mut self,
		header: <Block as BlockT>::Header,
		body: Option<Vec<<Block as BlockT>::Extrinsic>>,
		justification: Option<Justification<Block::Hash>>,
		state: NewBlockState,
	) -> error::Result<()> {
		assert!(self.pending_block.is_none(), "Only one block per operation is allowed");
		self.pending_block = Some(PendingBlock {
			block: StoredBlock::new(header, body, justification),
			state,
		});
		Ok(())
	}

	fn update_authorities(&mut self, authorities: Vec<AuthorityId>) {
		self.pending_authorities = Some(authorities);
	}

	fn update_storage(&mut self, update: <InMemory<H, C> as StateBackend<H, C>>::Transaction) -> error::Result<()> {
		self.new_state = Some(self.old_state.update(update));
		Ok(())
	}

	fn update_changes_trie(&mut self, update: MemoryDB<H>) -> error::Result<()> {
		self.changes_trie_update = Some(update);
		Ok(())
	}

	fn reset_storage<I: Iterator<Item=(Vec<u8>, Vec<u8>)>>(&mut self, iter: I) -> error::Result<()> {
		self.new_state = Some(InMemory::from(iter.collect::<HashMap<_, _>>()));
		Ok(())
	}
}

/// In-memory backend. Keeps all states and blocks in memory. Useful for testing.
pub struct Backend<Block, H, C>
where
	Block: BlockT,
	H: Hasher,
	C: NodeCodec<H>,
	H::Out: HeapSizeOf + From<Block::Hash>,
{
	states: RwLock<HashMap<Block::Hash, InMemory<H, C>>>,
	changes_trie_storage: InMemoryChangesTrieStorage<H>,
	blockchain: Blockchain<Block>,
}

impl<Block, H, C> Backend<Block, H, C>
where
	Block: BlockT,
	H: Hasher,
	C: NodeCodec<H>,
	H::Out: HeapSizeOf + From<Block::Hash>,
{
	/// Create a new instance of in-mem backend.
	pub fn new() -> Backend<Block, H, C> {
		Backend {
			states: RwLock::new(HashMap::new()),
			changes_trie_storage: InMemoryChangesTrieStorage::new(),
			blockchain: Blockchain::new(),
		}
	}
}

impl<Block, H, C> backend::Backend<Block, H, C> for Backend<Block, H, C>
where
	Block: BlockT,
	H: Hasher,
	H::Out: HeapSizeOf + From<Block::Hash>,
	C: NodeCodec<H> + Send + Sync,
{
	type BlockImportOperation = BlockImportOperation<Block, H, C>;
	type Blockchain = Blockchain<Block>;
	type State = InMemory<H, C>;
	type ChangesTrieStorage = InMemoryChangesTrieStorage<H>;

	fn begin_operation(&self, block: BlockId<Block>) -> error::Result<Self::BlockImportOperation> {
		let state = match block {
			BlockId::Hash(ref h) if h.clone() == Default::default() => Self::State::default(),
			_ => self.state_at(block)?,
		};

		Ok(BlockImportOperation {
			pending_block: None,
			pending_authorities: None,
			old_state: state,
			new_state: None,
			changes_trie_update: None,
		})
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation) -> error::Result<()> {
		if let Some(pending_block) = operation.pending_block {
			let old_state = &operation.old_state;
			let (header, body, justification) = pending_block.block.into_inner();

			let hash = header.hash();
			let parent_hash = *header.parent_hash();

			self.states.write().insert(hash, operation.new_state.unwrap_or_else(|| old_state.clone()));

			let changes_trie_root = header.digest().logs().iter()
				.find(|log| log.as_changes_trie_root().is_some())
				.and_then(DigestItem::as_changes_trie_root)
				.cloned();
			if let Some(changes_trie_root) = changes_trie_root {
				if let Some(changes_trie_update) = operation.changes_trie_update {
					let changes_trie_root: H::Out = changes_trie_root.into();
					self.changes_trie_storage.insert(header.number().as_(), changes_trie_root, changes_trie_update);
				}
			}

			self.blockchain.insert(hash, header, justification, body, pending_block.state);
			// dumb implementation - store value for each block
			if pending_block.state.is_best() {
				self.blockchain.cache.insert(parent_hash, operation.pending_authorities);
			}
		}
		Ok(())
	}

	fn finalize_block(&self, block: BlockId<Block>) -> error::Result<()> {
		self.blockchain.finalize_header(block)
	}

	fn blockchain(&self) -> &Self::Blockchain {
		&self.blockchain
	}

	fn changes_trie_storage(&self) -> Option<&Self::ChangesTrieStorage> {
		Some(&self.changes_trie_storage)
	}

	fn state_at(&self, block: BlockId<Block>) -> error::Result<Self::State> {
		match self.blockchain.id(block).and_then(|id| self.states.read().get(&id).cloned()) {
			Some(state) => Ok(state),
			None => Err(error::ErrorKind::UnknownBlock(format!("{}", block)).into()),
		}
	}

	fn revert(&self, _n: NumberFor<Block>) -> error::Result<NumberFor<Block>> {
		Ok(As::sa(0))
	}
}

impl<Block, H, C> backend::LocalBackend<Block, H, C> for Backend<Block, H, C>
where
	Block: BlockT,
	H: Hasher,
	H::Out: HeapSizeOf + From<Block::Hash>,
	C: NodeCodec<H> + Send + Sync,
{}

impl<Block: BlockT> Cache<Block> {
	fn insert(&self, at: Block::Hash, authorities: Option<Vec<AuthorityId>>) {
		self.authorities_at.write().insert(at, authorities);
	}
}

impl<Block: BlockT> blockchain::Cache<Block> for Cache<Block> {
	fn authorities_at(&self, block: BlockId<Block>) -> Option<Vec<AuthorityId>> {
		let hash = match block {
			BlockId::Hash(hash) => hash,
			BlockId::Number(number) => self.storage.read().hashes.get(&number).cloned()?,
		};

		self.authorities_at.read().get(&hash).cloned().unwrap_or(None)
	}
}

/// Insert authorities entry into in-memory blockchain cache. Extracted as a separate function to use it in tests.
pub fn cache_authorities_at<Block: BlockT>(
	blockchain: &Blockchain<Block>,
	at: Block::Hash,
	authorities: Option<Vec<AuthorityId>>
) {
	blockchain.cache.insert(at, authorities);
}

#[cfg(test)]
mod tests {
	use std::sync::Arc;
	use primitives::{KeccakHasher, RlpCodec};
	use test_client;
	use test_client::TestClient;
	use runtime_primitives::traits::Block as BlockT;
	use test_client::backend::Backend as ClientBackendT;
	use test_client::client::BlockOrigin;
	use test_client::blockchain::Backend as BlockChainBackendT;

	type TestBackend = test_client::client::in_mem::Backend<test_client::runtime::Block, KeccakHasher, RlpCodec>;

	#[test]
	fn test_leaves() {
		// block tree:
		// G -> A1 -> A2

		let backend = Arc::new(TestBackend::new());
		let client = test_client::new_with_backend(backend.clone()).unwrap();

		// G -> A1
		let a1 = client.new_block().unwrap().bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, a1.clone()).unwrap();
		assert_eq!(
			backend.blockchain().leaves().unwrap(),
			vec![a1.hash()]);

		// A1 -> A2
		let a2 = client.new_block().unwrap().bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, a2.clone()).unwrap();
		assert_eq!(
			backend.blockchain().leaves().unwrap(),
			vec![a2.hash()]);
	}
}
