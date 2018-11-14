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

use super::api::BlockBuilder as BlockBuilderApi;
use std::vec::Vec;
use codec::Encode;
use blockchain::HeaderBackend;
use runtime_primitives::traits::{
	Header as HeaderT, Hash, Block as BlockT, One, HashFor, ProvideRuntimeApi, ApiRef
};
use primitives::H256;
use runtime_primitives::generic::BlockId;
use runtime_api::Core;
use error;
use runtime_primitives::ApplyOutcome;

/// Utility for building new (valid) blocks from a stream of extrinsics.
pub struct BlockBuilder<'a, Block, A: ProvideRuntimeApi> where Block: BlockT {
	header: <Block as BlockT>::Header,
	extrinsics: Vec<<Block as BlockT>::Extrinsic>,
	api: ApiRef<'a, A::Api>,
	block_id: BlockId<Block>,
}

impl<'a, Block, A> BlockBuilder<'a, Block, A>
where
	Block: BlockT<Hash=H256>,
	A: ProvideRuntimeApi + HeaderBackend<Block> + 'a,
	A::Api: BlockBuilderApi<Block>,
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

		let header = <<Block as BlockT>::Header as HeaderT>::new(
			number,
			Default::default(),
			Default::default(),
			parent_hash,
			Default::default()
		);

		let api = api.runtime_api();
		api.initialise_block(block_id, &header)?;

		Ok(BlockBuilder {
			header,
			extrinsics: Vec::new(),
			api,
			block_id: *block_id,
		})
	}

	/// Push onto the block's list of extrinsics. This will ensure the extrinsic
	/// can be validly executed (by executing it); if it is invalid, it'll be returned along with
	/// the error. Otherwise, it will return a mutable reference to self (in order to chain).
	pub fn push(&mut self, xt: <Block as BlockT>::Extrinsic) -> error::Result<()> {
		fn impl_push<'a, T, Block: BlockT>(
			api: &mut ApiRef<'a, T>,
			block_id: &BlockId<Block>,
			xt: Block::Extrinsic,
			extrinsics: &mut Vec<Block::Extrinsic>
		) -> error::Result<()> where T: BlockBuilderApi<Block> {
			api.map_api_result(|api| {
				match api.apply_extrinsic(block_id, &xt)? {
					Ok(ApplyOutcome::Success) | Ok(ApplyOutcome::Fail) => {
						extrinsics.push(xt);
						Ok(())
					}
					Err(e) => {
						Err(error::ErrorKind::ApplyExtrinsicFailed(e).into())
					}
				}
			})
		}

		//FIXME: Please NLL, help me!
		impl_push(&mut self.api, &self.block_id, xt, &mut self.extrinsics)
	}

	/// Consume the builder to return a valid `Block` containing all pushed extrinsics.
	pub fn bake(mut self) -> error::Result<Block> {
		self.header = self.api.finalise_block(&self.block_id)?;

		debug_assert_eq!(
			self.header.extrinsics_root().clone(),
			HashFor::<Block>::ordered_trie_root(self.extrinsics.iter().map(Encode::encode)),
		);

		Ok(<Block as BlockT>::new(self.header, self.extrinsics))
	}
}
