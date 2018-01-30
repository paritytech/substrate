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

fn header_hash(header: &primitives::block::Header) -> primitives::block::HeaderHash {
	primitives::hash(&ser::to_vec(header))
}

struct PendingBlock {
	block: Block,
	is_best: bool,
}

struct Block {
	header: block::Header,
	body: Option<block::Body>,
}

/// In-memory transaction.
pub struct BlockImportOperation {
	pending_block: Option<PendingBlock>,
	pending_state: state_machine::backend::InMemory,
}

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

