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
use parking_lot::RwLock;
use state_machine;
use error;
use backend;
use primitives;
use ser;
use primitives::block::{self, HeaderHash};
use blockchain::{self, BlockId, BlockStatus};

fn header_hash(header: &block::Header) -> block::HeaderHash {
	primitives::hashing::blake2_256(&ser::to_vec(header)).into()
}

struct PendingBlock {
	block: Block,
	is_best: bool,
}

#[derive(PartialEq, Eq, Clone)]
struct Block {
	header: block::Header,
	body: Option<block::Body>,
}

/// In-memory transaction.
pub struct BlockImportOperation {
	pending_block: Option<PendingBlock>,
	pending_state: state_machine::backend::InMemory,
}

#[derive(Clone)]
struct BlockchainStorage {
	blocks: HashMap<HeaderHash, Block>,
	hashes: HashMap<block::Number, HeaderHash>,
	best_hash: HeaderHash,
	best_number: block::Number,
	genesis_hash: HeaderHash,
}

/// In-memory blockchain. Supports concurrent reads.
pub struct Blockchain {
	storage: RwLock<BlockchainStorage>,
}

impl Clone for Blockchain {
	fn clone(&self) -> Blockchain {
		Blockchain {
			storage: RwLock::new(self.storage.read().clone()),
		}
	}
}

impl Blockchain {
	fn id(&self, id: BlockId) -> Option<HeaderHash> {
		match id {
			BlockId::Hash(h) => Some(h),
			BlockId::Number(n) => self.storage.read().hashes.get(&n).cloned(),
		}
	}

	fn new() -> Blockchain {
		Blockchain {
			storage: RwLock::new(
				BlockchainStorage {
					blocks: HashMap::new(),
					hashes: HashMap::new(),
					best_hash: HeaderHash::default(),
					best_number: 0,
					genesis_hash: HeaderHash::default(),
				})
		}
	}

	fn insert(&self, hash: HeaderHash, header: block::Header, body: Option<block::Body>, is_new_best: bool) {
		let number = header.number;
		let mut storage = self.storage.write();
		storage.blocks.insert(hash, Block {
			header: header,
			body: body,
		});
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
	pub fn equals_to(&self, other: &Blockchain) -> bool {
		self.canon_equals_to(other) && self.storage.read().blocks == other.storage.read().blocks
	}

	/// Compare canonical chain to other canonical chain.
	pub fn canon_equals_to(&self, other: &Blockchain) -> bool {
		let this = self.storage.read();
		let other = other.storage.read();
			this.hashes == other.hashes
		    && this.best_hash == other.best_hash
			&& this.best_number == other.best_number
			&& this.genesis_hash == other.genesis_hash
	}
}

impl blockchain::Backend for Blockchain {
	fn header(&self, id: BlockId) -> error::Result<Option<block::Header>> {
		Ok(self.id(id).and_then(|hash| self.storage.read().blocks.get(&hash).map(|b| b.header.clone())))
	}

	fn body(&self, id: BlockId) -> error::Result<Option<block::Body>> {
		Ok(self.id(id).and_then(|hash| self.storage.read().blocks.get(&hash).and_then(|b| b.body.clone())))
	}

	fn info(&self) -> error::Result<blockchain::Info> {
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

	fn hash(&self, number: block::Number) -> error::Result<Option<block::HeaderHash>> {
		Ok(self.id(BlockId::Number(number)))
	}
}

impl backend::BlockImportOperation for BlockImportOperation {
	type State = state_machine::backend::InMemory;

	fn state(&self) -> error::Result<Self::State> {
		Ok(self.pending_state.clone())
	}

	fn import_block(&mut self, header: block::Header, body: Option<block::Body>, is_new_best: bool) -> error::Result<()> {
		assert!(self.pending_block.is_none(), "Only one block per transaction is allowed");
		self.pending_block = Some(PendingBlock {
			block: Block {
				header: header,
				body: body,
			},
			is_best: is_new_best,
		});
		Ok(())
	}

	fn reset_storage<I: Iterator<Item=(Vec<u8>, Vec<u8>)>>(&mut self, iter: I) -> error::Result<()> {
		self.pending_state = state_machine::backend::InMemory::from(iter.collect());
		Ok(())
	}
}

/// In-memory backend. Keeps all states and blocks in memory. Useful for testing.
pub struct Backend {
	states: RwLock<HashMap<block::HeaderHash, state_machine::backend::InMemory>>,
	blockchain: Blockchain,
}

impl Backend {
	/// Create a new instance of in-mem backend.
	pub fn new() -> Backend {
		Backend {
			states: RwLock::new(HashMap::new()),
			blockchain: Blockchain::new(),
		}
	}

	/// Generate and import a sequence of blocks. A user supplied function is allowed to modify each block header. Useful for testing.
	pub fn generate_blocks<F>(&self, count: usize, edit_header: F) where F: Fn(&mut block::Header) {
		use backend::{Backend, BlockImportOperation};
		let info = blockchain::Backend::info(&self.blockchain).expect("In-memory backend never fails");
		let mut best_num = info.best_number;
		let mut best_hash = info.best_hash;
		let state_root = blockchain::Backend::header(&self.blockchain, BlockId::Hash(best_hash))
			.expect("In-memory backend never fails")
			.expect("Best header always exists in the blockchain")
			.state_root;
		for _ in 0 .. count {
			best_num = best_num + 1;
			let mut header = block::Header {
				parent_hash: best_hash,
				number: best_num,
				state_root: state_root,
				transaction_root: Default::default(),
				digest: Default::default(),
			};
			edit_header(&mut header);

			let mut tx = self.begin_transaction(BlockId::Hash(best_hash)).expect("In-memory backend does not fail");
			best_hash = header_hash(&header);
			tx.import_block(header, None, true).expect("In-memory backend does not fail");
			self.commit_transaction(tx).expect("In-memory backend does not fail");
		}
	}

	/// Generate and import a sequence of blocks. Useful for testing.
	pub fn push_blocks(&self, count: usize) {
		self.generate_blocks(count, |_| {})
	}
}

impl backend::Backend for Backend {
	type BlockImportOperation = BlockImportOperation;
	type Blockchain = Blockchain;
	type State = state_machine::backend::InMemory;

	fn begin_transaction(&self, block: BlockId) -> error::Result<Self::BlockImportOperation> {
		let state = match block {
			BlockId::Hash(h) if h.is_zero() => Self::State::default(),
			_ => self.state_at(block)?,
		};

		Ok(BlockImportOperation {
			pending_block: None,
			pending_state: state,
		})
	}

	fn commit_transaction(&self, transaction: Self::BlockImportOperation) -> error::Result<()> {
		if let Some(pending_block) = transaction.pending_block {
			let hash = header_hash(&pending_block.block.header);
			self.states.write().insert(hash, transaction.pending_state);
			self.blockchain.insert(hash, pending_block.block.header, pending_block.block.body, pending_block.is_best);
		}
		Ok(())
	}

	fn blockchain(&self) -> &Blockchain {
		&self.blockchain
	}

	fn state_at(&self, block: BlockId) -> error::Result<Self::State> {
		match self.blockchain.id(block).and_then(|id| self.states.read().get(&id).cloned()) {
			Some(state) => Ok(state),
			None => Err(error::ErrorKind::UnknownBlock(block).into()),
		}
	}
}
