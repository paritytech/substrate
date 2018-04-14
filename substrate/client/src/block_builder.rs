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
use primitives::{Header, Block};
use primitives::block::{Id as BlockId, Extrinsic};
use {backend, error, Client};
use triehash::ordered_trie_root;

/// Utility for building new (valid) blocks from a stream of transactions.
pub struct BlockBuilder<B, E> where
	B: backend::Backend,
	E: CodeExecutor + Clone,
	error::Error: From<<<B as backend::Backend>::State as state_machine::backend::Backend>::Error>,
{
	header: Header,
	transactions: Vec<Extrinsic>,
	executor: E,
	state: B::State,
	changes: state_machine::OverlayedChanges,
}

impl<B, E> BlockBuilder<B, E> where
	B: backend::Backend,
	E: CodeExecutor + Clone,
	error::Error: From<<<B as backend::Backend>::State as state_machine::backend::Backend>::Error>,
{
	/// Create a new instance of builder from the given client, building on the latest block.
	pub fn new(client: &Client<B, E>) -> error::Result<Self> {
		client.info().and_then(|i| Self::at_block(&BlockId::Hash(i.chain.best_hash), client))
	}

	/// Create a new instance of builder from the given client using a particular block's ID to
	/// build upon.
	pub fn at_block(block_id: &BlockId, client: &Client<B, E>) -> error::Result<Self> {
		Ok(BlockBuilder {
			header: Header {
				number: client.block_number_from_id(block_id)?.ok_or(error::ErrorKind::UnknownBlock(*block_id))? + 1,
				parent_hash: client.block_hash_from_id(block_id)?.ok_or(error::ErrorKind::UnknownBlock(*block_id))?,
				state_root: Default::default(),
				extrinsics_root: Default::default(),
				digest: Default::default(),
			},
			transactions: Default::default(),
			executor: client.clone_executor(),
			state: client.state_at(block_id)?,
			changes: Default::default(),
		})
	}

	/// Push a transaction onto the block's list of transactions. This will ensure the transaction
	/// can be validly executed (by executing it); if it is invalid, it'll be returned along with
	/// the error. Otherwise, it will return a mutable reference to self (in order to chain).
	pub fn push(&mut self, tx: Extrinsic) -> error::Result<()> {
		let output = state_machine::execute(&self.state, &mut self.changes, &self.executor, "execute_transaction",
			&vec![].and(&self.header).and(&tx))?;
		self.header = Header::decode(&mut &output[..]).expect("Header came straight out of runtime so must be valid");
		self.transactions.push(tx);
		Ok(())
	}

	/// Consume the builder to return a valid `Block` containing all pushed transactions.
	pub fn bake(mut self) -> error::Result<Block> {
		self.header.extrinsics_root = ordered_trie_root(self.transactions.iter().map(Slicable::encode)).0.into();
		let output = state_machine::execute(&self.state, &mut self.changes, &self.executor, "finalise_block",
			&self.header.encode())?;
		self.header = Header::decode(&mut &output[..]).expect("Header came straight out of runtime so must be valid");
		Ok(Block {
			header: self.header,
			transactions: self.transactions,
		})
	}
}
