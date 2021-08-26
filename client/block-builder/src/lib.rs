// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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
//! [`BlockBuilder`](sp_block_builder::BlockBuilder).Error
//!
//! The block builder utility is used in the node as an abstraction over the runtime api to
//! initialize a block, to push extrinsics and to finalize a block.

#![warn(missing_docs)]

use codec::Encode;
use log;
use log::info;

use sp_runtime::{
	generic::BlockId,
	traits::{BlakeTwo256, Header as HeaderT, Hash, Block as BlockT, HashFor, DigestFor, NumberFor, One},
};
use sp_blockchain::{ApplyExtrinsicFailed, Error};
use sp_core::ExecutionContext;
use sp_api::{
	Core, ApiExt, ApiErrorFor, ApiRef, ProvideRuntimeApi, StorageChanges, StorageProof,
	TransactionOutcome,
};
use sp_consensus::RecordProof;

use pallet_random_seed::SeedType;
use extrinsic_info_runtime_api::runtime_api::ExtrinsicInfoRuntimeApi;
pub use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sp_blockchain::Backend;
use sc_client_api::backend;

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

impl<Block: BlockT, StateBackend: backend::StateBackend<HashFor<Block>>> BuiltBlock<Block, StateBackend> {
	/// Convert into the inner values.
	pub fn into_inner(self) -> (Block, StorageChanges<StateBackend, Block>, Option<StorageProof>) {
		(self.block, self.storage_changes, self.proof)
	}
}

/// Block builder provider
pub trait BlockBuilderProvider<B, Block, RA>
	where
		Block: BlockT,
		B: backend::Backend<Block>,
		Self: Sized,
		RA: ProvideRuntimeApi<Block>,
{
	/// Create a new block, built on top of `parent`.
	///
	/// When proof recording is enabled, all accessed trie nodes are saved.
	/// These recorded trie nodes can be used by a third party to proof the
	/// output of this block builder without having access to the full storage.
	fn new_block_at<R: Into<RecordProof>>(
		&self,
		parent: &BlockId<Block>,
		inherent_digests: DigestFor<Block>,
		record_proof: R,
	) -> sp_blockchain::Result<BlockBuilder<Block, RA, B>>;

	/// Create a new block, built on the head of the chain.
	fn new_block(
		&self,
		inherent_digests: DigestFor<Block>,
	) -> sp_blockchain::Result<BlockBuilder<Block, RA, B>>;
}

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
		ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>
		+ ExtrinsicInfoRuntimeApi<Block>,
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
	/// This will ensure the extrinsic can be validly executed (by executing it).
	pub fn push(&mut self, xt: <Block as BlockT>::Extrinsic) -> Result<(), ApiErrorFor<A, Block>> {
		self.extrinsics.push(xt);
		Ok(())
	}

	/// Fetches previous block extrinsics, temporary applies them and then try
	/// to applies incomming transactions in order to prevalidate them
	///
	pub fn consume_valid_transactions(
		&mut self,
		transaction_provider: Box<
			dyn FnOnce(
				&BlockId<Block>,
				&<A as ProvideRuntimeApi<Block>>::Api,
			) -> Vec<Block::Extrinsic>,
		>,
		inherent_data: sp_inherents::InherentData,
	) -> Result<(), ApiErrorFor<A, Block>> {
		let is_next_block_epoch = sp_ignore_tx::extract_inherent_data(&inherent_data)
			.map_err(|_| String::from("cannot fetch information about ignore_tx flag"))?;

		if is_next_block_epoch {
			log::debug!(target: "block_builder", "the next block is new epoch - no transactions will be included");
			return Ok(());
		}

		let parent_hash = self.parent_hash;
		let block_id = &self.block_id;
		let previous_block_extrinsics = self
			.backend
			.blockchain()
			.body(BlockId::Hash(parent_hash))?
			.unwrap_or_default();

		let valid_extrinsics = self.api.execute_in_transaction(|api| {
			for tx in previous_block_extrinsics {
				// TODO return error
				match api.apply_extrinsic_with_context(
					block_id,
					ExecutionContext::BlockConstruction,
					tx.clone(),
				) {
					Ok(Ok(_)) => {}
					Ok(Err(validity)) => {
						return TransactionOutcome::Rollback(Err(format!(
							"cannot apply previous block extrinsics - {:?}",
							validity
						)))
					}
					Err(e) => {
						return TransactionOutcome::Rollback(Err(format!(
							"cannot apply previous block extrinsics - {}",
							e
						)))
					}
				}
			}
			TransactionOutcome::Rollback(Ok(transaction_provider(block_id, api)))
		});

		for xt in valid_extrinsics?.into_iter() {
			self.extrinsics.push(xt);
		}
		Ok(())
	}

	/// Consume the builder to build a valid `Block` containing all pushed extrinsics.
	///
	/// Returns the build `Block`, the changes to the storage and an optional `StorageProof`
	/// supplied by `self.api`, combined as [`BuiltBlock`].
	/// The storage proof will be `Some(_)` when proof recording was enabled.
	pub fn build(
		mut self,
		seed: SeedType,
	) -> Result<BuiltBlock<Block, backend::StateBackendFor<B, Block>>, ApiErrorFor<A, Block>> {
		let parent_hash = self.parent_hash;
		let block_id = &self.block_id;

		match self
			.backend
			.blockchain()
			.body(BlockId::Hash(parent_hash))
			.unwrap()
		{
			Some(previous_block_extrinsics) => {
				log::debug!(target: "block_builder", "transaction count {}", previous_block_extrinsics.len());
				let shuffled_extrinsics = if previous_block_extrinsics.len() <= 1 {
					previous_block_extrinsics
				}else{
					extrinsic_shuffler::shuffle::<Block, A>(
						&self.api,
						&self.block_id,
						previous_block_extrinsics,
						seed,
					)
				};

				for xt in shuffled_extrinsics.iter() {
					log::debug!(target: "block_builder", "executing extrinsic :{:?}", BlakeTwo256::hash(&xt.encode()));
					self.api.execute_in_transaction(|api| {
						match api.apply_extrinsic_with_context(
							block_id,
							ExecutionContext::BlockConstruction,
							xt.clone(),
						) {
							Ok(Ok(_)) => TransactionOutcome::Commit(()),
							Ok(Err(_tx_validity)) => TransactionOutcome::Rollback(()),
							Err(_e) => TransactionOutcome::Rollback(()),
						}
					})
				}
			}
			None => {
				info!("No extrinsics found for previous block");
			}
		};

		let mut header = self
			.api
			.finalize_block_with_context(&self.block_id, ExecutionContext::BlockConstruction)?;


		// store hash of all extrinsics include in given bloack
		let extrinsics_root = HashFor::<Block>::ordered_trie_root(
			self.extrinsics.iter().map(Encode::encode).collect(),
		);
		header.set_extrinsics_root(extrinsics_root);

		let proof = self.api.extract_proof();

		let state = self.backend.state_at(self.block_id)?;
		let changes_trie_state = backend::changes_tries_state_at_block(
			&self.block_id,
			self.backend.changes_trie_storage(),
		)?;

		let storage_changes = self.api.into_storage_changes(
			&state,
			changes_trie_state.as_ref(),
			parent_hash,
		)?;

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
	) -> Result<(SeedType, Vec<Block::Extrinsic>), ApiErrorFor<A, Block>> {
		let block_id = self.block_id.clone();
		let seed = pallet_random_seed::extract_inherent_data(&inherent_data)
			.map_err(|_| String::from("cannot read random seed from inherents data"))?;
		self.api
			.execute_in_transaction(move |api| {
				// `create_inherents` should not change any state, to ensure this we always rollback
				// the transaction.
				TransactionOutcome::Rollback(api.inherent_extrinsics_with_context(
					&block_id,
					ExecutionContext::BlockConstruction,
					inherent_data,
				))
			})
			.map(|inherents| (seed, inherents))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_blockchain::HeaderBackend;
	use sp_core::Blake2Hasher;
	use sp_state_machine::Backend;
	use substrate_test_runtime_client::{DefaultTestClientBuilderExt, TestClientBuilderExt};

	#[test]
	fn block_building_storage_proof_does_not_include_runtime_by_default() {
		let builder = substrate_test_runtime_client::TestClientBuilder::new();
		let backend = builder.backend();
		let client = builder.build();

		let block = BlockBuilder::new(
			&client,
			client.info().best_hash,
			client.info().best_number,
			RecordProof::Yes,
			Default::default(),
			&*backend,
		).unwrap().build(Default::default()).unwrap();

		let proof = block.proof.expect("Proof is build on request");

		let backend = sp_state_machine::create_proof_check_backend::<Blake2Hasher>(
			block.storage_changes.transaction_storage_root,
			proof,
		).unwrap();

		assert!(
			backend.storage(&sp_core::storage::well_known_keys::CODE)
				.unwrap_err()
				.contains("Database missing expected key"),
		);
	}
}
