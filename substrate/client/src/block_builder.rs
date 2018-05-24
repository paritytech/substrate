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

//! Utility struct to build a block.

use std::vec::Vec;
use codec::{Joiner, Slicable};
use state_machine::{self, CodeExecutor};
use runtime_primitives::traits::{Header as HeaderT, Hashing as HashingT, Block as BlockT};
use runtime_primitives::generic::BlockId;
use {backend, error, Client};
use triehash::ordered_trie_root;

/// Utility for building new (valid) blocks from a stream of extrinsics.
pub struct BlockBuilder<B, E, Block, Hashing> where
	B: backend::Backend<Block>,
	E: CodeExecutor + Clone,
	Block: BlockT,
	Hashing: HashingT<Output = Block::Header::Hash>,
	error::Error: From<<<B as backend::Backend<Block>>::State as state_machine::backend::Backend>::Error>,
{
	header: Header,
	extrinsics: Vec<Block::Extrinsic>,
	executor: E,
	state: B::State,
	changes: state_machine::OverlayedChanges,
	// will probably need PhantomData<Hashing> here...
}

impl<B, E, Block, Hashing> BlockBuilder<B, E, Block, Hashing> where
	B: backend::Backend<Block>,
	E: CodeExecutor + Clone,
	Block: BlockT,
	Hashing: HashingT<Output = Block::Header::Hash>,
	error::Error: From<<<B as backend::Backend<Block>>::State as state_machine::backend::Backend>::Error>,
{
	/// Create a new instance of builder from the given client, building on the latest block.
	pub fn new(client: &Client<B, E, Block>) -> error::Result<Self> {
		client.info().and_then(|i| Self::at_block(&BlockId::<Block>::Hash(i.chain.best_hash), client))
	}

	/// Create a new instance of builder from the given client using a particular block's ID to
	/// build upon.
	pub fn at_block(block_id: &BlockId<Block>, client: &Client<B, E, Block>) -> error::Result<Self> {
		Ok(BlockBuilder {
			header: Header {
				number: client.block_number_from_id(block_id)?.ok_or(error::ErrorKind::UnknownBlock(Box::new(block_id.clone())))? + 1,
				parent_hash: client.block_hash_from_id(block_id)?.ok_or(error::ErrorKind::UnknownBlock(Box::new(block_id.clone())))?,
				state_root: Default::default(),
				extrinsics_root: Default::default(),
				digest: Default::default(),
			},
			extrinsics: Default::default(),
			executor: client.clone_executor(),
			state: client.state_at(block_id)?,
			changes: Default::default(),
		})
	}

	/// Push a transaction onto the block's list of extrinsics. This will ensure the transaction
	/// can be validly executed (by executing it); if it is invalid, it'll be returned along with
	/// the error. Otherwise, it will return a mutable reference to self (in order to chain).
	pub fn push(&mut self, xt: Block::Extrinsic) -> error::Result<()> {
		let (output, _) = state_machine::execute(&self.state, &mut self.changes, &self.executor, "execute_transaction",
			&vec![].and(&self.header).and(&xt))?;
		self.header = Block::Header::decode(&mut &output[..]).expect("Header came straight out of runtime so must be valid");
		self.extrinsics.push(xt);
		Ok(())
	}

	/// Consume the builder to return a valid `Block` containing all pushed extrinsics.
	pub fn bake(mut self) -> error::Result<Block> {
		self.header.extrinsics_root = Hashing::ordered_trie_root(self.extrinsics.iter().map(Slicable::encode));
		let (output, _) = state_machine::execute(&self.state, &mut self.changes, &self.executor, "finalise_block",
			&self.header.encode())?;
		self.header = Block::Header::decode(&mut &output[..]).expect("Header came straight out of runtime so must be valid");
		Ok(Block::new(self.header, self.extrinsics))
	}
}
