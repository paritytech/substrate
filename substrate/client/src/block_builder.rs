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
use codec::{Decode, Encode};
use state_machine::{self, native_when_possible};
use runtime_primitives::traits::{Header as HeaderT, Hash, Block as BlockT, One, HashFor};
use runtime_primitives::generic::BlockId;
use {backend, error, Client, CallExecutor};
use runtime_primitives::{ApplyResult, ApplyOutcome};

/// Utility for building new (valid) blocks from a stream of extrinsics.
pub struct BlockBuilder<B, E, Block> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block> + Clone,
	Block: BlockT,
{
	header: <Block as BlockT>::Header,
	extrinsics: Vec<<Block as BlockT>::Extrinsic>,
	executor: E,
	state: B::State,
	changes: state_machine::OverlayedChanges,
}

impl<B, E, Block> BlockBuilder<B, E, Block> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block> + Clone,
	Block: BlockT,
{
	/// Create a new instance of builder from the given client, building on the latest block.
	pub fn new(client: &Client<B, E, Block>) -> error::Result<Self> {
		client.info().and_then(|i| Self::at_block(&BlockId::Hash(i.chain.best_hash), client))
	}

	/// Create a new instance of builder from the given client using a particular block's ID to
	/// build upon.
	pub fn at_block(block_id: &BlockId<Block>, client: &Client<B, E, Block>) -> error::Result<Self> {
		let number = client.block_number_from_id(block_id)?
			.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("{}", block_id)))?
			+ One::one();

		let parent_hash = client.block_hash_from_id(block_id)?
			.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("{}", block_id)))?;

		let executor = client.executor().clone();
		let state = client.state_at(block_id)?;
		let mut changes = Default::default();
		let header = <<Block as BlockT>::Header as HeaderT>::new(
			number,
			Default::default(),
			Default::default(),
			parent_hash,
			Default::default()
		);

		executor.call_at_state(&state, &mut changes, "initialise_block", &header.encode(), native_when_possible())?;
		changes.commit_prospective();

		Ok(BlockBuilder {
			header,
			extrinsics: Vec::new(),
			executor,
			state,
			changes,
		})
	}

	/// Push onto the block's list of extrinsics. This will ensure the extrinsic
	/// can be validly executed (by executing it); if it is invalid, it'll be returned along with
	/// the error. Otherwise, it will return a mutable reference to self (in order to chain).
	pub fn push(&mut self, xt: <Block as BlockT>::Extrinsic) -> error::Result<()> {
		match self.executor.call_at_state(&self.state, &mut self.changes, "apply_extrinsic", &xt.encode(), native_when_possible()) {
			Ok((result, _)) => {
				match ApplyResult::decode(&mut result.as_slice()) {
					Some(Ok(ApplyOutcome::Success)) | Some(Ok(ApplyOutcome::Fail)) => {
						self.extrinsics.push(xt);
						self.changes.commit_prospective();
						Ok(())
					}
					Some(Err(e)) => {
						self.changes.discard_prospective();
						Err(error::ErrorKind::ApplyExtinsicFailed(e).into())
					}
					None => {
						self.changes.discard_prospective();
						Err(error::ErrorKind::CallResultDecode("apply_extrinsic").into())
					}
				}
			}
			Err(e) => {
				self.changes.discard_prospective();
				Err(e)
			}
		}
	}

	/// Consume the builder to return a valid `Block` containing all pushed extrinsics.
	pub fn bake(mut self) -> error::Result<Block> {
		let (output, _) = self.executor.call_at_state(
			&self.state,
			&mut self.changes,
			"finalise_block",
			&[],
			native_when_possible(),
		)?;
		self.header = <<Block as BlockT>::Header as Decode>::decode(&mut &output[..])
			.expect("Header came straight out of runtime so must be valid");

		debug_assert_eq!(
			self.header.extrinsics_root().clone(),
			HashFor::<Block>::ordered_trie_root(self.extrinsics.iter().map(Encode::encode)),
		);

		Ok(<Block as BlockT>::new(self.header, self.extrinsics))
	}
}
