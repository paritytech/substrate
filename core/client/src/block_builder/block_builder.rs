// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
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
use crate::runtime_api::Core;
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
		api.initialize_block_with_context(block_id, ExecutionContext::BlockConstruction, &header)?;
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
		use crate::runtime_api::ApiExt;

		let block_id = &self.block_id;
		let extrinsics = &mut self.extrinsics;

		self.api.map_api_result(|api| {
			match api.apply_extrinsic_with_context(block_id, ExecutionContext::BlockConstruction, xt.clone())? {
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

	/// Consume the builder to return a valid `Block` containing all pushed extrinsics.
	pub fn bake(mut self) -> error::Result<Block> {
		self.header = self.api.finalize_block_with_context(&self.block_id, ExecutionContext::BlockConstruction)?;

		debug_assert_eq!(
			self.header.extrinsics_root().clone(),
			HashFor::<Block>::ordered_trie_root(self.extrinsics.iter().map(Encode::encode)),
		);

		Ok(<Block as BlockT>::new(self.header, self.extrinsics))
	}
}
