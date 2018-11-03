// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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
use codec::Encode;
use blockchain::HeaderBackend;
use state_machine::{self, OverlayedChanges};
use runtime_primitives::traits::{Header as HeaderT, Hash, Block as BlockT, One, HashFor, ProvideRuntimeApi};
use runtime_primitives::generic::BlockId;
use runtime_api::{BlockBuilder as BlockBuilderAPI, Core};
use error;
use runtime_primitives::ApplyOutcome;
use primitives::AuthorityId;

/// Utility for building new (valid) blocks from a stream of extrinsics.
pub struct BlockBuilder<'a, Block, A> where Block: BlockT {
	header: <Block as BlockT>::Header,
	extrinsics: Vec<<Block as BlockT>::Extrinsic>,
	api: &'a A,
	block_id: BlockId<Block>,
	changes: state_machine::OverlayedChanges,
}

impl<'a, Block, A> BlockBuilder<'a, Block, A>
where
	Block: BlockT<Hash=H256>,
	A: ProvideRuntimeApi + HeaderBackend<Block> + 'a,
	A::Api: BlockBuilderAPI<Block, Error=error::Error, OverlayedChanges=OverlayedChanges> +
			Core<Block, AuthorityId, OverlayedChanges=OverlayedChanges, Error=error::Error>
{
	/// Create a new instance of builder from the given client, building on the latest block.
	pub fn new(api: &'a A) -> error::Result<Self> {
		api.info().and_then(|i| Self::at_block(&BlockId::Hash(i.best_hash), api))
	}

	/// Create a new instance of builder from the given client using a particular block's ID to
	/// build upon.
	pub fn at_block(block_id: &BlockId<Block>, api: &'a A) -> error::Result<Self> {
		let number = api.block_number_from_id(block_id)?
			.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("{}", block_id)))?
			+ One::one();

		let parent_hash = api.block_hash_from_id(block_id)?
			.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("{}", block_id)))?;

		let mut changes = Default::default();
		let header = <<Block as BlockT>::Header as HeaderT>::new(
			number,
			Default::default(),
			Default::default(),
			parent_hash,
			Default::default()
		);

		api.runtime_api().initialise_block(block_id, &mut changes, &header)?;
		changes.commit_prospective();

		Ok(BlockBuilder {
			header,
			extrinsics: Vec::new(),
			api,
			block_id: *block_id,
			changes,
		})
	}

	/// Push onto the block's list of extrinsics. This will ensure the extrinsic
	/// can be validly executed (by executing it); if it is invalid, it'll be returned along with
	/// the error. Otherwise, it will return a mutable reference to self (in order to chain).
	pub fn push(&mut self, xt: <Block as BlockT>::Extrinsic) -> error::Result<()> {
		match self.api.runtime_api().apply_extrinsic(&self.block_id, &mut self.changes, &xt) {
			Ok(result) => {
				match result {
					Ok(ApplyOutcome::Success) | Ok(ApplyOutcome::Fail) => {
						self.extrinsics.push(xt);
						self.changes.commit_prospective();
						Ok(())
					}
					Err(e) => {
						self.changes.discard_prospective();
						Err(error::ErrorKind::ApplyExtrinsicFailed(e).into())
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
		self.header = self.api.runtime_api().finalise_block(&self.block_id, &mut self.changes)?;

		debug_assert_eq!(
			self.header.extrinsics_root().clone(),
			HashFor::<Block>::ordered_trie_root(self.extrinsics.iter().map(Encode::encode)),
		);

		Ok(<Block as BlockT>::new(self.header, self.extrinsics))
	}
}
