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
use backend;
use light;
use primitives::AuthorityId;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Chain, Header as HeaderT,
	Consensus as ConsensusT, Zero, NumberFor, As, Digest, DigestItem};
use blockchain::{self, BlockStatus};
use state_machine::backend::{Backend as StateBackend, InMemory};
use state_machine::InMemoryChangesTrieStorage;
use patricia_trie::NodeCodec;
use hashdb::Hasher;
use heapsize::HeapSizeOf;
use memorydb::MemoryDB;

struct PendingBlock<Ch: Chain> {
	block: StoredBlock<Ch>,
	is_best: bool,
}

#[derive(PartialEq, Eq, Clone)]
enum StoredBlock<Ch: Chain> {
	Header(<Ch::Block as BlockT>::Header, Option<<Ch::Consensus as ConsensusT>::Signature>),
	Full(Ch::Block, Option<<Ch::Consensus as ConsensusT>::Signature>),
}

impl<Ch: Chain> StoredBlock<Ch> {
	fn new(
		header: <Ch::Block as BlockT>::Header,
		body: Option<Vec<<Ch::Block as BlockT>::Extrinsic>>,
		just: Option<<Ch::Consensus as ConsensusT>::Signature>
	) -> Self {
		match body {
			Some(body) => StoredBlock::Full(<Ch::Block as BlockT>::new(header, body), just),
			None => StoredBlock::Header(header, just),
		}
	}

	fn header(&self) -> &<Ch::Block as BlockT>::Header {
		match *self {
			StoredBlock::Header(ref h, _) => h,
			StoredBlock::Full(ref b, _) => b.header(),
		}
	}

	fn justification(&self) -> Option<&<Ch::Consensus as ConsensusT>::Signature> {
		match *self {
			StoredBlock::Header(_, ref j) | StoredBlock::Full(_, ref j) => j.as_ref()
		}
	}

	fn extrinsics(&self) -> Option<&[<Ch::Block as BlockT>::Extrinsic]> {
		match *self {
			StoredBlock::Header(_, _) => None,
			StoredBlock::Full(ref b, _) => Some(b.extrinsics())
		}
	}

	fn into_inner(self) -> (
		<Ch::Block as BlockT>::Header,
		Option<Vec<<Ch::Block as BlockT>::Extrinsic>>,
		Option<<Ch::Consensus as ConsensusT>::Signature>
	) {
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
struct BlockchainStorage<Ch: Chain> {
	blocks: HashMap<<Ch::Block as BlockT>::Hash, StoredBlock<Ch>>,
	hashes: HashMap<<NumberFor<Ch::Block>, <Ch::Block as BlockT>::Hash>,
	best_hash: <Ch::Block as BlockT>::Hash,
	best_number: <<Ch::Block as BlockT>::Header as HeaderT>::Number,
	genesis_hash: <Ch::Block as BlockT>::Hash,
	cht_roots: HashMap<NumberFor<Ch::Block>, <Ch::Block as BlockT>::Hash>>,
}

/// In-memory blockchain. Supports concurrent reads.
pub struct Blockchain<Ch: Chain> {
	storage: Arc<RwLock<BlockchainStorage<Ch>>>,
	cache: Cache<Ch>,
}

struct Cache<Ch: Chain> {
	storage: Arc<RwLock<BlockchainStorage<Ch>>>,
	authorities_at: RwLock<HashMap<<Ch::Block as BlockT>::Hash, Option<Vec<AuthorityId>>>>,
}

impl<Ch: Chain> Clone for Blockchain<Ch> {
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

impl<Ch: Chain> Blockchain<Ch> {
	/// Get header hash of given block.
	pub fn id(&self, id: BlockId<Ch::Block>) -> Option<<Ch::Block as BlockT>::Hash> {
		match id {
			BlockId::Hash(h) => Some(h),
			BlockId::Number(n) => self.storage.read().hashes.get(&n).cloned(),
		}
	}

	/// Create new in-memory blockchain storage.
	pub fn new() -> Blockchain<Ch> {
		let storage = Arc::new(RwLock::new(
			BlockchainStorage {
				blocks: HashMap::new(),
				hashes: HashMap::new(),
				best_hash: Default::default(),
				best_number: Zero::zero(),
				genesis_hash: Default::default(),
				cht_roots: HashMap::new(),
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
		hash: <Ch::Block as BlockT>::Hash,
		header: <Ch::Block as BlockT>::Header,
		justification: Option<<Ch::Consensus as ConsensusT>::Signature>,
		body: Option<Vec<<Ch::Block as BlockT>::Extrinsic>>,
		is_new_best: bool
	) {
		let number = header.number().clone();
		let mut storage = self.storage.write();
		storage.blocks.insert(hash.clone(), StoredBlock::new(header, body, justification));
		storage.hashes.insert(number, hash.clone());
		if is_new_best {
			storage.best_hash = hash.clone();
			storage.best_number = number.clone();
		}
		if number == Zero::zero() {
			storage.genesis_hash = hash;
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
	pub fn insert_cht_root(&self, block: NumberFor<Ch::Block>, cht_root: <Ch::Block as BlockT>::Hash) {
		self.storage.write().cht_roots.insert(block, cht_root);
	}
}

impl<Ch: Chain> blockchain::HeaderBackend<Ch> for Blockchain<Ch> {
	fn header(&self, id: BlockId<Ch::Block>) -> error::Result<Option<<Ch::Block as BlockT>::Header>> {
		Ok(self.id(id).and_then(|hash| {
			self.storage.read().blocks.get(&hash).map(|b| b.header().clone())
		}))
	}

	fn info(&self) -> error::Result<blockchain::Info<Ch::Block>> {
		let storage = self.storage.read();
		Ok(blockchain::Info {
			best_hash: storage.best_hash,
			best_number: storage.best_number,
			genesis_hash: storage.genesis_hash,
		})
	}

	fn status(&self, id: BlockId<Ch::Block>) -> error::Result<BlockStatus> {
		match self.id(id).map_or(false, |hash| self.storage.read().blocks.contains_key(&hash)) {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	fn number(&self, hash: <Ch::Block as BlockT>::Hash) -> error::Result<Option<NumberFor<Ch::Block>>> {
		Ok(self.storage.read().blocks.get(&hash).map(|b| *b.header().number()))
	}

	fn hash(&self, number: <<Ch::Block as BlockT>::Header as HeaderT>::Number) -> error::Result<Option<<Ch::Block as BlockT>::Hash>> {
		Ok(self.id(BlockId::Number(number)))
	}
}


impl<Ch: Chain> blockchain::Backend<Ch> for Blockchain<Ch> {
	fn body(&self, id: BlockId<Ch::Block>) -> error::Result<Option<Vec<<Ch::Block as BlockT>::Extrinsic>>> {
		Ok(self.id(id).and_then(|hash| {
			self.storage.read().blocks.get(&hash)
				.and_then(|b| b.extrinsics().map(|x| x.to_vec()))
		}))
	}

	fn justification(&self, id: BlockId<Ch::Block>) -> error::Result<Option<<Ch::Consensus as ConsensusT>::Signature>> {
		Ok(self.id(id).and_then(|hash| self.storage.read().blocks.get(&hash).and_then(|b|
			b.justification().map(|x| x.clone()))
		))
	}

	fn cache(&self) -> Option<&blockchain::Cache<Ch::Block>> {
		Some(&self.cache)
	}
}

impl<Ch: Chain> light::blockchain::Storage<Ch> for Blockchain<Ch>
	where
		<Ch::Block as BlockT>::Hash: From<[u8; 32]>,
{
	fn import_header(
		&self,
		is_new_best: bool,
		header: <Ch::Block as BlockT>::Header,
		authorities: Option<Vec<AuthorityId>>
	) -> error::Result<()> {
		let hash = header.hash();
		let parent_hash = *header.parent_hash();
		self.insert(hash, header, None, None, is_new_best);
		if is_new_best {
			self.cache.insert(parent_hash, authorities);
		}
		Ok(())
	}

	fn cht_root(&self, _cht_size: u64, block: NumberFor<Ch::Block>) -> error::Result<<Ch::Block as BlockT>::Hash> {
		self.storage.read().cht_roots.get(&block).cloned()
			.ok_or_else(|| error::ErrorKind::Backend(format!("CHT for block {} not exists", block)).into())
	}

	fn cache(&self) -> Option<&blockchain::Cache<Ch::Block>> {
		Some(&self.cache)
	}
}

/// In-memory operation.
pub struct BlockImportOperation<H: Hasher, C: NodeCodec<H>, Ch: Chain> {
	pending_block: Option<PendingBlock<Ch>>,
	pending_authorities: Option<Vec<AuthorityId>>,
	old_state: InMemory<H, C>,
	new_state: Option<InMemory<H, C>>,
	changes_trie_update: Option<MemoryDB<H>>,
}

impl<H, C, Ch> backend::BlockImportOperation<H, C, Ch> for BlockImportOperation<H, C, Ch>
where
	H: Hasher,
	C: NodeCodec<H>,
	H::Out: HeapSizeOf,
	Ch: Chain,
{
	type State = InMemory<H, C>;

	fn state(&self) -> error::Result<Option<&Self::State>> {
		Ok(Some(&self.old_state))
	}

	fn set_block_data(
		&mut self,
		header: <Ch::Block as BlockT>::Header,
		body: Option<Vec<<Ch::Block as BlockT>::Extrinsic>>,
		justification: Option<<Ch::Consensus as ConsensusT>::Signature>,
		is_new_best: bool
	) -> error::Result<()> {
		assert!(self.pending_block.is_none(), "Only one block per operation is allowed");
		self.pending_block = Some(PendingBlock {
			block: StoredBlock::new(header, body, justification),
			is_best: is_new_best,
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
pub struct Backend<H, C, Ch>
where
	H: Hasher,
	C: NodeCodec<H>,
	H::Out: HeapSizeOf + From<Block::Hash>,
	Ch: Chain
{
	states: RwLock<HashMap<<Ch::Block as BlockT>::Hash, InMemory<H, C>>>,
	changes_trie_storage: InMemoryChangesTrieStorage<H>,
	blockchain: Blockchain<Ch>,
}

impl<H, C, Ch> Backend<H, C, Ch>
where
	H: Hasher,
	C: NodeCodec<H>,
	H::Out: HeapSizeOf + From<Block::Hash>,
	Ch: Chain
{
	/// Create a new instance of in-mem backend.
	pub fn new() -> Backend<H, C, Ch> {
		Backend {
			states: RwLock::new(HashMap::new()),
			changes_trie_storage: InMemoryChangesTrieStorage::new(),
			blockchain: Blockchain::new(),
		}
	}
}

impl<H, C, Ch> backend::Backend<H, C, Ch> for Backend<H, C, Ch>
where
	H: Hasher,
	H::Out: HeapSizeOf + From<Block::Hash>,
	C: NodeCodec<H> + Send + Sync,
	Ch: Chain
{
	type BlockImportOperation = BlockImportOperation<H, C, Ch>;
	type Blockchain = Blockchain<Ch>;
	type State = InMemory<H, C>;
	type ChangesTrieStorage = InMemoryChangesTrieStorage<H>;

	fn begin_operation(&self, block: BlockId<Ch::Block>) -> error::Result<Self::BlockImportOperation> {
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
			self.blockchain.insert(hash, header, justification, body, pending_block.is_best);
			// dumb implementation - store value for each block
			if pending_block.is_best {
				self.blockchain.cache.insert(parent_hash, operation.pending_authorities);
			}
		}
		Ok(())
	}

	fn blockchain(&self) -> &Self::Blockchain {
		&self.blockchain
	}

	fn changes_trie_storage(&self) -> Option<&Self::ChangesTrieStorage> {
		Some(&self.changes_trie_storage)
	}

	fn state_at(&self, block: BlockId<Ch::Block>) -> error::Result<Self::State> {
		match self.blockchain.id(block).and_then(|id| self.states.read().get(&id).cloned()) {
			Some(state) => Ok(state),
			None => Err(error::ErrorKind::UnknownBlock(format!("{}", block)).into()),
		}
	}

	fn revert(&self, _n: NumberFor<Ch::Block>) -> error::Result<NumberFor<Ch::Block>> {
		Ok(As::sa(0))
	}
}

impl<H, C, Ch> backend::LocalBackend<H, C, Ch> for Backend<H, C, Ch>
where
	H: Hasher,
	H::Out: HeapSizeOf + From<Block::Hash>,
	C: NodeCodec<H> + Send + Sync,
	Ch: Chain
{}

impl<Ch: Chain> Cache<Ch> {
	fn insert(&self, at: <Ch::Block as BlockT>::Hash, authorities: Option<Vec<AuthorityId>>) {
		self.authorities_at.write().insert(at, authorities);
	}
}

impl<Ch: Chain> blockchain::Cache<Ch::Block> for Cache<Ch> {
	fn authorities_at(&self, block: BlockId<Ch::Block>) -> Option<Vec<AuthorityId>> {
		let hash = match block {
			BlockId::Hash(hash) => hash,
			BlockId::Number(number) => self.storage.read().hashes.get(&number).cloned()?,
		};

		self.authorities_at.read().get(&hash).cloned().unwrap_or(None)
	}
}

/// Insert authorities entry into in-memory blockchain cache. Extracted as a separate function to use it in tests.
pub fn cache_authorities_at<Ch: Chain>(
	blockchain: &Blockchain<Ch>,
	at: <Ch::Block as BlockT>::Hash,
	authorities: Option<Vec<AuthorityId>>
) {
	blockchain.cache.insert(at, authorities);
}
