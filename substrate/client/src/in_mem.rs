// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! In memory client backend

use std::collections::HashMap;
use std::marker::PhantomData;
use parking_lot::RwLock;
use error;
use backend;
use codec::Slicable;
use primitives;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Hashing as HashingT, Zero};
use blockchain::{self, BlockStatus};
use state_machine::backend::{Backend as StateBackend, InMemory};

struct PendingBlock<Block: BlockT> {
	block: Block,
	is_best: bool,
}

#[derive(PartialEq, Eq, Clone)]
struct Block<Block: BlockT> {
	header: Block::Header,
	justification: Option<primitives::bft::Justification>,
	body: Option<Vec<Block::Extrinsic>>,
}

#[derive(Clone)]
struct BlockchainStorage<Block: BlockT> {
	blocks: HashMap<Block::Header::Hash, Block>,
	hashes: HashMap<Block::Header::Number, Block::Header::Hash>,
	best_hash: Block::Header::Hash,
	best_number: Block::Header::Number,
	genesis_hash: Block::Header::Hash,
}

/// In-memory blockchain. Supports concurrent reads.
pub struct Blockchain<BlockT: Block> {
	storage: RwLock<BlockchainStorage<Block>>,
}

impl<BlockT: Block> Clone for Blockchain<Block> {
	fn clone(&self) -> Self {
		Blockchain {
			storage: RwLock::new(self.storage.read().clone()),
		}
	}
}

impl<Block: BlockT> Blockchain<Block> {
	fn id(&self, id: BlockId<Block>) -> Option<Block::Header::Hash> {
		match id {
			BlockId::Hash(h) => Some(h),
			BlockId::Number(n) => self.storage.read().hashes.get(&n).cloned(),
		}
	}

	fn new() -> Self {
		Blockchain {
			storage: RwLock::new(
				BlockchainStorage {
					blocks: HashMap::new(),
					hashes: HashMap::new(),
					best_hash: Default::default(),
					best_number: Zero::zero(),
					genesis_hash: Default::default(),
				})
		}
	}

	fn insert(
		&self,
		hash: Block::Header::Hash,
		header: Block::Header,
		justification: Option<primitives::bft::Justification>,
		body: Option<Vec<Block::Extrinsic>>,
		is_new_best: bool
	) {
		let number = header.number;
		let mut storage = self.storage.write();
		storage.blocks.insert(hash, Block::new(header, body, justification));
		storage.hashes.insert(number, hash);
		if is_new_best {
			storage.best_hash = hash;
			storage.best_number = number;
		}
		if number == 0 {
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
}

impl<Block: BlockT> blockchain::Backend<Block> for Blockchain<Block> {
	fn header(&self, id: BlockId<Block>) -> error::Result<Option<Block::Header>> {
		Ok(self.id(id).and_then(|hash| self.storage.read().blocks.get(&hash).map(|b| b.header.clone())))
	}

	fn body(&self, id: BlockId<Block>) -> error::Result<Option<Vec<Block::Extrinsic>>> {
		Ok(self.id(id).and_then(|hash| self.storage.read().blocks.get(&hash).and_then(|b| b.body.clone())))
	}

	fn justification(&self, id: BlockId<Block>) -> error::Result<Option<primitives::bft::Justification>> {
		Ok(self.id(id).and_then(|hash| self.storage.read().blocks.get(&hash).and_then(|b| b.justification.clone())))
	}

	fn info(&self) -> error::Result<blockchain::Info<Block>> {
		let storage = self.storage.read();
		Ok(blockchain::Info {
			best_hash: storage.best_hash,
			best_number: storage.best_number,
			genesis_hash: storage.genesis_hash,
		})
	}

	fn status(&self, id: BlockId) -> error::Result<BlockStatus> {
		match self.id(id).map_or(false, |hash| self.storage.read().blocks.contains_key(&hash)) {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	fn hash(&self, number: Block::Header::Number) -> error::Result<Option<Block::Header::Hash>> {
		Ok(self.id(BlockId::Number(number)))
	}
}

/// In-memory operation.
pub struct BlockImportOperation<Block: BlockT> {
	pending_block: Option<PendingBlock<Block>>,
	old_state: InMemory,
	new_state: Option<InMemory>,
}

impl<Block: BlockT> backend::BlockImportOperation<Block> for BlockImportOperation<Block> {
	type State = InMemory;

	fn state(&self) -> error::Result<&Self::State> {
		Ok(&self.old_state)
	}

	fn set_block_data(
		&mut self,
		header: Block::Header,
		body: Option<Vec<Block::Extrinsic>>,
		justification: Option<primitives::bft::Justification>,
		is_new_best: bool
	) -> error::Result<()> {
		assert!(self.pending_block.is_none(), "Only one block per operation is allowed");
		self.pending_block = Some(PendingBlock {
			block: Block::new(header, body, justification),
			is_best: is_new_best,
		});
		Ok(())
	}

	fn update_storage(&mut self, update: <InMemory as StateBackend>::Transaction) -> error::Result<()> {
		self.new_state = Some(self.old_state.update(update));
		Ok(())
	}

	fn reset_storage<I: Iterator<Item=(Vec<u8>, Vec<u8>)>>(&mut self, iter: I) -> error::Result<()> {
		self.new_state = Some(InMemory::from(iter.collect::<HashMap<_, _>>()));
		Ok(())
	}
}

/// In-memory backend. Keeps all states and blocks in memory. Useful for testing.
pub struct Backend<Block: BlockT, Hashing: HashingT + Hash> {
	states: RwLock<HashMap<Block::Header::Hash, InMemory>>,
	blockchain: Blockchain<Block>,
	dummy: PhantomData<Hashing>,
}

impl<Block: BlockT, Hashing: HashingT + Hash> Backend<Block, Hashing> {
	/// Create a new instance of in-mem backend.
	pub fn new() -> Backend {
		Backend {
			states: RwLock::new(HashMap::new()),
			blockchain: Blockchain::new(),
			dummy: PhantomData::new(),
		}
	}
}

impl<
	Block: BlockT,
	Hashing: HashingT + Hash
> Backend<Block, Hashing> for backend::Backend<Block, Hashing> {
	type BlockImportOperation = BlockImportOperation<Block>;
	type Blockchain = Blockchain<Block>;
	type State = InMemory;

	fn begin_operation(&self, block: BlockId<Block>) -> error::Result<Self::BlockImportOperation> {
		let state = match block {
			BlockId::Hash(h) if h.is_zero() => Self::State::default(),
			_ => self.state_at(block)?,
		};

		Ok(BlockImportOperation {
			pending_block: None,
			old_state: state,
			new_state: None,
		})
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation) -> error::Result<()> {
		if let Some(pending_block) = operation.pending_block {
			let hash = Hashing::hash_of(&pending_block.block.header);
			let old_state = &operation.old_state;
			self.states.write().insert(hash, operation.new_state.unwrap_or_else(|| old_state.clone()));
			self.blockchain.insert(hash, pending_block.block.header, pending_block.block.justification, pending_block.block.body, pending_block.is_best);
		}
		Ok(())
	}

	fn blockchain(&self) -> &Self::Blockchain {
		&self.blockchain
	}

	fn state_at(&self, block: BlockId) -> error::Result<Self::State> {
		match self.blockchain.id(block).and_then(|id| self.states.read().get(&id).cloned()) {
			Some(state) => Ok(state),
			None => Err(error::ErrorKind::UnknownBlock(Box::new(block)).into()),
		}
	}
}
