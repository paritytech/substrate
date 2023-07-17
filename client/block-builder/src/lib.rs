// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Substrate block builder
//!
//! This crate provides the [`BlockBuilder`] utility and the corresponding runtime api
//! [`BlockBuilder`](sp_block_builder::BlockBuilder).
//!
//! The block builder utility is used in the node as an abstraction over the runtime api to
//! initialize a block, to push extrinsics and to finalize a block.

#![warn(missing_docs)]

use std::marker::PhantomData;

use codec::Encode;

use sp_api::{
	ApiExt, ApiRef, CallApiAt, Core, DisableProofRecorder, EnableProofRecorder, RuntimeInstance,
	StorageChanges, StorageProof, TransactionOutcome,
};
use sp_blockchain::{ApplyExtrinsicFailed, Error};
use sp_core::traits::CallContext;
use sp_runtime::{
	legacy,
	traits::{Block as BlockT, Hash, HashFor, Header as HeaderT, NumberFor, One},
	Digest,
};

use sc_client_api::backend;
pub use sp_block_builder::BlockBuilder as BlockBuilderApi;

/// Used as parameter to [`BlockBuilderProvider`] to express if proof recording should be enabled.
///
/// When `RecordProof::Yes` is given, all accessed trie nodes should be saved. These recorded
/// trie nodes can be used by a third party to proof this proposal without having access to the
/// full storage.
#[derive(Copy, Clone, PartialEq)]
pub enum RecordProof {
	/// `Yes`, record a proof.
	Yes,
	/// `No`, don't record any proof.
	No,
}

impl RecordProof {
	/// Returns if `Self` == `Yes`.
	pub fn yes(&self) -> bool {
		matches!(self, Self::Yes)
	}
}

/// Will return [`RecordProof::No`] as default value.
impl Default for RecordProof {
	fn default() -> Self {
		Self::No
	}
}

impl From<bool> for RecordProof {
	fn from(val: bool) -> Self {
		if val {
			Self::Yes
		} else {
			Self::No
		}
	}
}

/// A block that was build by [`BlockBuilder`] plus some additional data.
///
/// This additional data includes the `storage_changes`, these changes can be applied to the
/// backend to get the state of the block. Furthermore an optional `proof` is included which
/// can be used to proof that the build block contains the expected data. The `proof` will
/// only be set when proof recording was activated.
pub struct BuiltBlock<Block: BlockT, StateBackend: backend::StateBackend<HashFor<Block>>> {
	/// The actual block that was build.
	pub block: Block,
	/// The changes that need to be applied to the backend to get the state of the build block.
	pub storage_changes: StorageChanges<StateBackend, Block>,
	/// An optional proof that was recorded while building the block.
	pub proof: Option<StorageProof>,
}

impl<Block: BlockT, StateBackend: backend::StateBackend<HashFor<Block>>>
	BuiltBlock<Block, StateBackend>
{
	/// Convert into the inner values.
	pub fn into_inner(self) -> (Block, StorageChanges<StateBackend, Block>, Option<StorageProof>) {
		(self.block, self.storage_changes, self.proof)
	}
}

/// Utility for building new (valid) blocks from a stream of extrinsics.
pub struct BlockBuilder<
	'a,
	Block: BlockT,
	Backend,
	CallApiAt: sp_api::CallApiAt<Block>,
	ProofRecorder,
> {
	extrinsics: Vec<Block::Extrinsic>,
	runtime_instance: RuntimeInstance<CallApiAt, Block, ProofRecorder>,
	version: u32,
	parent_hash: Block::Hash,
	backend: &'a Backend,
	/// The estimated size of the block header.
	estimated_header_size: usize,
	_phantom: PhantomData<ProofRecorder>,
}

impl<'a, Block, Backend, CallApiAt>
	BlockBuilder<'a, Block, Backend, CallApiAt, DisableProofRecorder>
where
	Block: BlockT,
	Backend: backend::Backend<Block>,
	CallApiAt: sp_api::CallApiAt<Block>,
{
	/// Create a new instance of builder based on the given `parent_hash` and `parent_number`.
	///
	/// While proof recording is enabled, all accessed trie nodes are saved.
	/// These recorded trie nodes can be used by a third party to prove the
	/// output of this block builder without having access to the full storage.
	pub fn with_proof_recording(
		call_api_at: CallApiAt,
		parent_hash: Block::Hash,
		parent_number: NumberFor<Block>,
		inherent_digests: Digest,
		backend: &'a Backend,
	) -> Result<BlockBuilder<Block, Backend, CallApiAt, EnableProofRecorder<Block>>, Error> {
		let header = <<Block as BlockT>::Header as HeaderT>::new(
			parent_number + One::one(),
			Default::default(),
			Default::default(),
			parent_hash,
			inherent_digests,
		);

		let estimated_header_size = header.encoded_size();

		let runtime_instance = RuntimeInstance::builder(call_api_at, parent_hash)
			.on_chain_context()
			.with_recorder()
			.build();

		let version = runtime_instance
			.api_version::<dyn BlockBuilderApi<Block>>()?
			.ok_or_else(|| Error::VersionInvalid("BlockBuilderApi".to_string()))?;

		Ok(BlockBuilder {
			parent_hash,
			extrinsics: Vec::new(),
			runtime_instance,
			version,
			backend,
			estimated_header_size,
			_phantom: PhantomData,
		})
	}

	pub fn without_proof_recording(
		call_api_at: CallApiAt,
		parent_hash: Block::Hash,
		parent_number: NumberFor<Block>,
		inherent_digests: Digest,
		backend: &'a Backend,
	) -> Result<Self, Error> {
		let header = <<Block as BlockT>::Header as HeaderT>::new(
			parent_number + One::one(),
			Default::default(),
			Default::default(),
			parent_hash,
			inherent_digests,
		);

		let estimated_header_size = header.encoded_size();

		let runtime_instance =
			RuntimeInstance::builder(call_api_at, parent_hash).on_chain_context().build();

		let version = runtime_instance
			.api_version::<dyn BlockBuilderApi<Block>>()?
			.ok_or_else(|| Error::VersionInvalid("BlockBuilderApi".to_string()))?;

		Ok(Self {
			parent_hash,
			extrinsics: Vec::new(),
			runtime_instance,
			version,
			backend,
			estimated_header_size,
			_phantom: PhantomData,
		})
	}
}

impl<'a, Block, Backend, CallApiAt, ProofRecorder>
	BlockBuilder<'a, Block, Backend, CallApiAt, ProofRecorder>
where
	Block: BlockT,
	Backend: backend::Backend<Block>,
	CallApiAt: sp_api::CallApiAt<Block>,
	ProofRecorder: sp_api::GetProofRecorder<Block>,
{
	/// Push onto the block's list of extrinsics.
	///
	/// This will ensure the extrinsic can be validly executed (by executing it).
	pub fn push(&mut self, xt: <Block as BlockT>::Extrinsic) -> Result<(), Error> {
		let parent_hash = self.parent_hash;
		let extrinsics = &mut self.extrinsics;
		let version = self.version;

		self.runtime_instance.execute_in_transaction(|api| {
			let res = if version < 6 {
				#[allow(deprecated)]
				BlockBuilderApi::<Block>::apply_extrinsic_before_version_6(api, xt.clone())
					.map(legacy::byte_sized_error::convert_to_latest)
			} else {
				BlockBuilderApi::<Block>::apply_extrinsic(api, xt.clone())
			};

			match res {
				Ok(Ok(_)) => {
					extrinsics.push(xt);
					TransactionOutcome::Commit(Ok(()))
				},
				Ok(Err(tx_validity)) => TransactionOutcome::Rollback(Err(
					ApplyExtrinsicFailed::Validity(tx_validity).into(),
				)),
				Err(e) => TransactionOutcome::Rollback(Err(Error::from(e))),
			}
		})
	}

	/// Consume the builder to build a valid `Block` containing all pushed extrinsics.
	///
	/// Returns the build `Block`, the changes to the storage and an optional `StorageProof`
	/// supplied by `self.api`, combined as [`BuiltBlock`].
	/// The storage proof will be `Some(_)` when proof recording was enabled.
	pub fn build(
		mut self,
	) -> Result<BuiltBlock<Block, backend::StateBackendFor<Backend, Block>>, Error> {
		let header: Block::Header = self.runtime_instance.finalize_block()?;

		debug_assert_eq!(
			header.extrinsics_root().clone(),
			HashFor::<Block>::ordered_trie_root(
				self.extrinsics.iter().map(Encode::encode).collect(),
				sp_runtime::StateVersion::V0,
			),
		);

		let proof = self.runtime_instance.extract_proof();

		let state = self.backend.state_at(self.parent_hash)?;

		let storage_changes = self
			.runtime_instance
			.into_storage_changes(&state, self.parent_hash)
			.map_err(sp_blockchain::Error::StorageChanges)?;

		Ok(BuiltBlock {
			block: <Block as BlockT>::new(header, self.extrinsics),
			storage_changes,
			proof,
		})
	}

	/// Create the inherents for the block.
	///
	/// Returns the inherents created by the runtime or an error if something failed.
	pub fn create_inherents(
		&mut self,
		inherent_data: sp_inherents::InherentData,
	) -> Result<Vec<Block::Extrinsic>, Error> {
		/*
		let parent_hash = self.parent_hash;
		self.api.execute_in_transaction(move |api| {
			// `create_inherents` should not change any state, to ensure this we always rollback
			// the transaction.
			// TransactionOutcome::Rollback(api.inherent_extrinsics(parent_hash, inherent_data))
			TransactionOutcome::Rollback(Ok(Vec::new()))
		})
		// .map_err(|e: String| Error::Application(Box::new(e)))
		*/
		Ok(Vec::new())
	}

	/// Estimate the size of the block in the current state.
	///
	/// If `include_proof` is `true`, the estimated size of the storage proof will be added
	/// to the estimation.
	pub fn estimate_block_size(&self, include_proof: bool) -> usize {
		let size = self.estimated_header_size + self.extrinsics.encoded_size();

		if include_proof {
			// size + self.api.proof_recorder().map(|pr| pr.estimate_encoded_size()).unwrap_or(0)
			size
		} else {
			size
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_blockchain::HeaderBackend;
	use sp_core::Blake2Hasher;
	use sp_state_machine::Backend;
	use substrate_test_runtime_client::{
		runtime::ExtrinsicBuilder, DefaultTestClientBuilderExt, TestClientBuilderExt,
	};

	#[test]
	fn block_building_storage_proof_does_not_include_runtime_by_default() {
		let builder = substrate_test_runtime_client::TestClientBuilder::new();
		let backend = builder.backend();
		let client = builder.build();

		let genesis_hash = client.info().best_hash;

		let block = BlockBuilder::new(
			&client,
			genesis_hash,
			client.info().best_number,
			RecordProof::Yes,
			Default::default(),
			&*backend,
		)
		.unwrap()
		.build()
		.unwrap();

		let proof = block.proof.expect("Proof is build on request");
		let genesis_state_root = client.header(genesis_hash).unwrap().unwrap().state_root;

		let backend =
			sp_state_machine::create_proof_check_backend::<Blake2Hasher>(genesis_state_root, proof)
				.unwrap();

		assert!(backend
			.storage(&sp_core::storage::well_known_keys::CODE)
			.unwrap_err()
			.contains("Database missing expected key"),);
	}

	#[test]
	fn failing_extrinsic_rolls_back_changes_in_storage_proof() {
		let builder = substrate_test_runtime_client::TestClientBuilder::new();
		let backend = builder.backend();
		let client = builder.build();

		let mut block_builder = BlockBuilder::new(
			&client,
			client.info().best_hash,
			client.info().best_number,
			RecordProof::Yes,
			Default::default(),
			&*backend,
		)
		.unwrap();

		block_builder.push(ExtrinsicBuilder::new_read_and_panic(8).build()).unwrap_err();

		let block = block_builder.build().unwrap();

		let proof_with_panic = block.proof.expect("Proof is build on request").encoded_size();

		let mut block_builder = BlockBuilder::new(
			&client,
			client.info().best_hash,
			client.info().best_number,
			RecordProof::Yes,
			Default::default(),
			&*backend,
		)
		.unwrap();

		block_builder.push(ExtrinsicBuilder::new_read(8).build()).unwrap();

		let block = block_builder.build().unwrap();

		let proof_without_panic = block.proof.expect("Proof is build on request").encoded_size();

		let block = BlockBuilder::new(
			&client,
			client.info().best_hash,
			client.info().best_number,
			RecordProof::Yes,
			Default::default(),
			&*backend,
		)
		.unwrap()
		.build()
		.unwrap();

		let proof_empty_block = block.proof.expect("Proof is build on request").encoded_size();

		// Ensure that we rolled back the changes of the panicked transaction.
		assert!(proof_without_panic > proof_with_panic);
		assert!(proof_without_panic > proof_empty_block);
		assert_eq!(proof_empty_block, proof_with_panic);
	}
}
