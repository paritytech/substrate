// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use parity_codec::Encode;
use runtime_primitives::ApplyOutcome;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{
	Header as HeaderT, Hash, Block as BlockT, One, HashFor, ProvideRuntimeApi, ApiRef
};
use primitives::{H256, ExecutionContext};
use crate::blockchain::HeaderBackend;
use crate::runtime_api::{Core, ApiExt};
use crate::error;

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
		api.info().and_then(|i|
			Self::at_block(&BlockId::Hash(i.best_hash), api, false)
		)
	}

	/// Create a new instance of builder from the given client using a
	/// particular block's ID to build upon with optional proof recording enabled.
	///
	/// While proof recording is enabled, all accessed trie nodes are saved.
	/// These recorded trie nodes can be used by a third party to proof the
	/// output of this block builder without having access to the full storage.
	pub fn at_block(
		block_id: &BlockId<Block>,
		api: &'a A,
		proof_recording: bool
	) -> error::Result<Self> {
		let number = api.block_number_from_id(block_id)?
			.ok_or_else(|| error::Error::UnknownBlock(format!("{}", block_id)))?
			+ One::one();

		let parent_hash = api.block_hash_from_id(block_id)?
			.ok_or_else(|| error::Error::UnknownBlock(format!("{}", block_id)))?;
		let header = <<Block as BlockT>::Header as HeaderT>::new(
			number,
			Default::default(),
			Default::default(),
			parent_hash,
			Default::default()
		);

		let mut api = api.runtime_api();

		if proof_recording {
			api.record_proof();
		}

		api.initialize_block_with_context(
			block_id, ExecutionContext::BlockConstruction, &header
		)?;

		Ok(BlockBuilder {
			header,
			extrinsics: Vec::new(),
			api,
			block_id: *block_id,
		})
	}

	/// Push onto the block's list of extrinsics.
	///
	/// This will ensure the extrinsic can be validly executed (by executing it);
	pub fn push(&mut self, xt: <Block as BlockT>::Extrinsic) -> error::Result<()> {
		let block_id = &self.block_id;
		let extrinsics = &mut self.extrinsics;

		self.api.map_api_result(|api| {
			match api.apply_extrinsic_with_context(
				block_id,
				ExecutionContext::BlockConstruction,
				xt.clone()
			)? {
				Ok(ApplyOutcome::Success) | Ok(ApplyOutcome::Fail) => {
					extrinsics.push(xt);
					Ok(())
				}
				Err(e) => {
					Err(error::Error::ApplyExtrinsicFailed(e))
				}
			}
		})
	}

	/// Consume the builder to return a valid `Block` containing all pushed extrinsics.
	pub fn bake(mut self) -> error::Result<Block> {
		self.bake_impl()?;
		Ok(<Block as BlockT>::new(self.header, self.extrinsics))
	}

	fn bake_impl(&mut self) -> error::Result<()> {
		self.header = self.api.finalize_block_with_context(
			&self.block_id, ExecutionContext::BlockConstruction
		)?;

		debug_assert_eq!(
			self.header.extrinsics_root().clone(),
			HashFor::<Block>::ordered_trie_root(
				self.extrinsics.iter().map(Encode::encode)
			),
		);

		Ok(())
	}

	/// Consume the builder to return a valid `Block` containing all pushed extrinsics
	/// and the generated proof.
	///
	/// The proof will be `Some(_)`, if proof recording was enabled while creating
	/// the block builder.
	pub fn bake_and_extract_proof(mut self) -> error::Result<(Block, Option<Vec<Vec<u8>>>)> {
		self.bake_impl()?;

		let proof = self.api.extract_proof();
		Ok((<Block as BlockT>::new(self.header, self.extrinsics), proof))
	}
}
