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
//! [`BlockBuilder`](api::BlockBuilder).Error
//!
//! The block builder utility is used in the node as an abstraction over the runtime api to
//! initialize a block, to push extrinsics and to finalize a block.

#![warn(missing_docs)]

use codec::Encode;

use sp_runtime::{
	generic::BlockId,
	traits::{Header as HeaderT, Hash, Block as BlockT, HashFor, DigestFor, NumberFor, One},
};
use sp_blockchain::{ApplyExtrinsicFailed, Error};
use primitives::ExecutionContext;

use sp_api::{Core, ApiExt, ApiErrorFor, ApiRef, ProvideRuntimeApi, StorageChanges, StorageProof};

use sp_consensus::RecordProof;

pub use runtime_api::BlockBuilder as BlockBuilderApi;

use client_api::backend;

/// Utility for building new (valid) blocks from a stream of extrinsics.
pub struct BlockBuilder<'a, Block: BlockT, A: ProvideRuntimeApi<Block>, B> {
	extrinsics: Vec<Block::Extrinsic>,
	api: ApiRef<'a, A::Api>,
	block_id: BlockId<Block>,
	parent_hash: Block::Hash,
	backend: &'a B,
}

impl<'a, Block, A, B> BlockBuilder<'a, Block, A, B>
where
	Block: BlockT,
	A: ProvideRuntimeApi<Block> + 'a,
	A::Api: BlockBuilderApi<Block, Error = Error> +
		ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>,
	B: backend::Backend<Block>,
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
		record_proof: RecordProof,
		inherent_digests: DigestFor<Block>,
		backend: &'a B,
	) -> Result<Self, ApiErrorFor<A, Block>> {
		let header = <<Block as BlockT>::Header as HeaderT>::new(
			parent_number + One::one(),
			Default::default(),
			Default::default(),
			parent_hash,
			inherent_digests,
		);

		let mut api = api.runtime_api();

		if record_proof.yes() {
			api.record_proof();
		}

		let block_id = BlockId::Hash(parent_hash);

		api.initialize_block_with_context(
			&block_id, ExecutionContext::BlockConstruction, &header,
		)?;

		Ok(Self {
			parent_hash,
			extrinsics: Vec::new(),
			api,
			block_id,
			backend,
		})
	}

	/// Push onto the block's list of extrinsics.
	///
	/// This will ensure the extrinsic can be validly executed (by executing it);
	pub fn push(&mut self, xt: <Block as BlockT>::Extrinsic) -> Result<(), ApiErrorFor<A, Block>> {
		let block_id = &self.block_id;
		let extrinsics = &mut self.extrinsics;

		if self
			.api
			.has_api_with::<dyn BlockBuilderApi<Block, Error = ApiErrorFor<A, Block>>, _>(
				block_id,
				|version| version < 4,
			)?
		{
			// Run compatibility fallback for v3.
			self.api.map_api_result(|api| {
				#[allow(deprecated)]
				match api.apply_extrinsic_before_version_4_with_context(
					block_id,
					ExecutionContext::BlockConstruction,
					xt.clone(),
				)? {
					Ok(_) => {
						extrinsics.push(xt);
						Ok(())
					}
					Err(e) => Err(ApplyExtrinsicFailed::from(e).into()),
				}
			})
		} else {
			self.api.map_api_result(|api| {
				match api.apply_extrinsic_with_context(
					block_id,
					ExecutionContext::BlockConstruction,
					xt.clone(),
				)? {
					Ok(_) => {
						extrinsics.push(xt);
						Ok(())
					}
					Err(tx_validity) => Err(ApplyExtrinsicFailed::Validity(tx_validity).into()),
				}
			})
		}
	}

	/// Consume the builder to "bake" a valid `Block` containing all pushed extrinsics.
	///
	/// Returns the build `Block`, the changes to the storage and an optional `StorageProof`.
	/// The storage proof will be `Some(_)` when proof recording was enabled.
	pub fn bake(mut self) -> Result<
		(
			Block,
			StorageChanges<backend::StateBackendFor<B, Block>, Block>,
			Option<StorageProof>
		),
		ApiErrorFor<A, Block>
	> {
		let header = self.api.finalize_block_with_context(
			&self.block_id, ExecutionContext::BlockConstruction
		)?;

		debug_assert_eq!(
			header.extrinsics_root().clone(),
			HashFor::<Block>::ordered_trie_root(
				self.extrinsics.iter().map(Encode::encode).collect(),
			),
		);

		let proof = self.api.extract_proof();

		let state = self.backend.state_at(self.block_id)?;
		let changes_trie_storage = self.backend.changes_trie_storage();
		let parent_hash = self.parent_hash;

		// The unsafe is required because the consume requires that we drop/consume the inner api
		// (what we do here).
		let storage_changes = unsafe {
			self.api.consume_inner(|a|
				a.into_storage_changes(&state, changes_trie_storage, parent_hash)
			)
		};

		{
			let _lock = self.backend.get_import_lock().read();
			self.backend.destroy_state(state)?;
		}

		Ok((<Block as BlockT>::new(header, self.extrinsics), storage_changes?, proof))
	}
}
