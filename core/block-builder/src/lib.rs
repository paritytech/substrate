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

//! Substrate block builder
//!
//! This crate provides the [`BlockBuilder`] utility and the corresponding runtime api
//! [`BlockBuilder`](api::BlockBuilder).
//!
//! The block builder utility is used in the node as an abstraction over the runtime api to
//! initialize a block, to push extrinsics and to finalize a block.

#![warn(missing_docs)]

use codec::Encode;

use sr_primitives::{
	generic::BlockId,
	traits::{
		Header as HeaderT, Hash, Block as BlockT, HashFor, ProvideRuntimeApi, ApiRef, DigestFor,
		NumberFor, One,
	},
};

use primitives::ExecutionContext;

use state_machine::StorageProof;

use sr_api::{Core, ApiExt, ApiErrorFor};

pub use runtime_api::BlockBuilder as BlockBuilderApi;

/// Error when the runtime failed to apply an extrinsic.
pub struct ApplyExtrinsicFailed(pub sr_primitives::ApplyError);

/// Utility for building new (valid) blocks from a stream of extrinsics.
pub struct BlockBuilder<'a, Block: BlockT, A: ProvideRuntimeApi> {
	header: Block::Header,
	extrinsics: Vec<Block::Extrinsic>,
	api: ApiRef<'a, A::Api>,
	block_id: BlockId<Block>,
}

impl<'a, Block, A> BlockBuilder<'a, Block, A>
where
	Block: BlockT,
	A: ProvideRuntimeApi + 'a,
	A::Api: BlockBuilderApi<Block>,
	ApiErrorFor<A, Block>: From<ApplyExtrinsicFailed>,
{
	/// Create a new instance of builder based on the given `parent_hash` and `parent_number`.
	///
	/// While proof recording is enabled, all accessed trie nodes are saved.
	/// These recorded trie nodes can be used by a third party to prove the
	/// output of this block builder without having access to the full storage.
	pub fn new(
		api: &'a A,
		parent_hash: Block::Hash,
		parent_number: NumberFor<Block>,
		proof_recording: bool,
		inherent_digests: DigestFor<Block>,
	) -> Result<Self, ApiErrorFor<A, Block>> {
		let header = <<Block as BlockT>::Header as HeaderT>::new(
			parent_number + One::one(),
			Default::default(),
			Default::default(),
			parent_hash,
			inherent_digests,
		);

		let mut api = api.runtime_api();

		if proof_recording {
			api.record_proof();
		}

		let block_id = BlockId::Hash(parent_hash);

		api.initialize_block_with_context(
			&block_id, ExecutionContext::BlockConstruction, &header,
		)?;

		Ok(Self {
			header,
			extrinsics: Vec::new(),
			api,
			block_id,
		})
	}

	/// Push onto the block's list of extrinsics.
	///
	/// This will ensure the extrinsic can be validly executed (by executing it);
	pub fn push(&mut self, xt: <Block as BlockT>::Extrinsic) -> Result<(), ApiErrorFor<A, Block>> {
		let block_id = &self.block_id;
		let extrinsics = &mut self.extrinsics;

		self.api.map_api_result(|api| {
			match api.apply_extrinsic_with_context(
				block_id,
				ExecutionContext::BlockConstruction,
				xt.clone()
			)? {
				Ok(_) => {
					extrinsics.push(xt);
					Ok(())
				}
				Err(e) => {
					Err(ApplyExtrinsicFailed(e))?
				}
			}
		})
	}

	/// Consume the builder to return a valid `Block` containing all pushed extrinsics.
	pub fn bake(mut self) -> Result<Block, ApiErrorFor<A, Block>> {
		self.bake_impl()?;
		Ok(<Block as BlockT>::new(self.header, self.extrinsics))
	}

	fn bake_impl(&mut self) -> Result<(), ApiErrorFor<A, Block>> {
		self.header = self.api.finalize_block_with_context(
			&self.block_id, ExecutionContext::BlockConstruction
		)?;

		debug_assert_eq!(
			self.header.extrinsics_root().clone(),
			HashFor::<Block>::ordered_trie_root(
				self.extrinsics.iter().map(Encode::encode).collect(),
			),
		);

		Ok(())
	}

	/// Consume the builder to return a valid `Block` containing all pushed extrinsics
	/// and the generated proof.
	///
	/// The proof will be `Some(_)`, if proof recording was enabled while creating
	/// the block builder.
	pub fn bake_and_extract_proof(mut self)
		-> Result<(Block, Option<StorageProof>), ApiErrorFor<A, Block>>
	{
		self.bake_impl()?;

		let proof = self.api.extract_proof();
		Ok((<Block as BlockT>::new(self.header, self.extrinsics), proof))
	}
}
