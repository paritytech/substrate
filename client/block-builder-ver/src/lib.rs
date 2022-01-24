// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use codec::Encode;

use sp_api::{
	ApiExt, ApiRef, Core, ProvideRuntimeApi, StorageChanges, StorageProof, TransactionOutcome,
};
use sp_blockchain::{ApplyExtrinsicFailed, Backend, Error};
use sp_core::ExecutionContext;
use sp_runtime::{
	generic::BlockId,
	traits::{
		BlakeTwo256, Block as BlockT, DigestFor, Hash, HashFor, Header as HeaderT, NumberFor, One,
	},
	SaturatedConversion,
};

pub use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sp_blockchain::HeaderBackend;
use ver_api::VerApi;

use sc_client_api::backend;
use sp_core::ShufflingSeed;
use sp_ver::extract_inherent_data;

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
	inherents: Vec<Block::Extrinsic>,
	extrinsics: Vec<Block::Extrinsic>,
	api: ApiRef<'a, A::Api>,
	block_id: BlockId<Block>,
	parent_hash: Block::Hash,
	backend: &'a B,
	previous_block_extrinsics: Option<Vec<<Block as BlockT>::Extrinsic>>,
	/// The estimated size of the block header.
	estimated_header_size: usize,
}

impl<'a, Block, A, B> BlockBuilder<'a, Block, A, B>
where
	Block: BlockT,
	A: ProvideRuntimeApi<Block> + 'a,
	A::Api: BlockBuilderApi<Block>
		+ ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>
		+ VerApi<Block>,
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
	) -> Result<Self, Error> {
		let header = <<Block as BlockT>::Header as HeaderT>::new(
			parent_number + One::one(),
			Default::default(),
			Default::default(),
			parent_hash,
			inherent_digests,
		);

		let estimated_header_size = header.encoded_size();

		let mut api = api.runtime_api();

		if record_proof.yes() {
			api.record_proof();
		}

		let block_id = BlockId::Hash(parent_hash);

		api.initialize_block_with_context(&block_id, ExecutionContext::BlockConstruction, &header)?;

		Ok(Self {
			parent_hash,
			inherents: Vec::new(),
			extrinsics: Vec::new(),
			api,
			block_id,
			backend,
			previous_block_extrinsics: None,
			estimated_header_size,
		})
	}

	/// temporaily apply extrinsics and record them on the list
	pub fn record_valid_extrinsics_and_revert_changes<
		F: FnOnce(&'_ A::Api) -> Vec<Block::Extrinsic>,
	>(
		&mut self,
		call: F,
	) -> () {
		let valid_txs = self.api.execute_in_transaction(|api| {
			let txs = call(&api);
			TransactionOutcome::Rollback(txs)
		});
		log::debug!(target: "block_builder", "consume {} valid transactios", valid_txs.len());
		self.extrinsics.extend(valid_txs);
	}

	/// Push onto the block's list of extrinsics.
	///
	/// validate extrinsics but without commiting the change
	pub fn push(&mut self, xt: <Block as BlockT>::Extrinsic) -> Result<(), Error> {
		let block_id = &self.block_id;
		let inherents = &mut self.inherents;

		self.api.execute_in_transaction(|api| {
			match api.apply_extrinsic_with_context(
				block_id,
				ExecutionContext::BlockConstruction,
				xt.clone(),
			) {
				Ok(Ok(_)) => {
					inherents.push(xt);
					TransactionOutcome::Rollback(Ok(()))
				},
				Ok(Err(tx_validity)) => TransactionOutcome::Rollback(Err(
					ApplyExtrinsicFailed::Validity(tx_validity).into(),
				)),
				Err(e) => TransactionOutcome::Rollback(Err(Error::from(e))),
			}
		})
	}

	/// fetch previous block and apply it
	///
	/// consequence of delayed block execution
	pub fn apply_previous_block_extrinsics(&mut self, seed: ShufflingSeed) {
		let parent_hash = self.parent_hash;
		let block_id = &self.block_id;
		self.api.store_seed(&block_id, seed.seed).unwrap();

		let previous_block_header =
			self.backend.blockchain().header(BlockId::Hash(parent_hash)).unwrap().unwrap();

		let previous_block_extrinsics = self
			.backend
			.blockchain()
			.body(BlockId::Hash(parent_hash))
			.unwrap()
			.unwrap_or_default();

		let prev_block_extrinsics_count =
			previous_block_header.count().clone().saturated_into::<usize>();
		log::debug!(target: "block_builder", "previous block has {} transactions, {} comming from that block", previous_block_extrinsics.len(), prev_block_extrinsics_count);

		let previous_block_extrinsics = previous_block_extrinsics
			.iter()
			.take(prev_block_extrinsics_count)
			.cloned()
			.collect::<Vec<_>>();

		// filter out extrinsics only
		let extrinsics = previous_block_extrinsics
			.into_iter()
			.filter(|e| {
				self.api
					.execute_in_transaction(|api| match api.get_signer(&self.block_id, e.clone()) {
						Ok(result) => TransactionOutcome::Rollback(result),
						Err(_) => TransactionOutcome::Rollback(None),
					})
					.is_some()
			})
			.collect::<Vec<_>>();

		self.previous_block_extrinsics = Some(extrinsics.clone());
		let to_be_executed = self
			.inherents
			.clone()
			.into_iter()
			.chain(extrinsics.into_iter())
			.collect::<Vec<_>>();

		let shuffled_extrinsics = extrinsic_shuffler::shuffle::<Block, A>(
			&self.api,
			&self.block_id,
			to_be_executed,
			&seed.seed,
		);

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

	/// Consume the builder to build a valid `Block` containing all pushed extrinsics.
	///
	/// Returns the build `Block`, the changes to the storage and an optional `StorageProof`
	/// supplied by `self.api`, combined as [`BuiltBlock`].
	/// The storage proof will be `Some(_)` when proof recording was enabled.
	pub fn build_with_seed(
		mut self,
		seed: ShufflingSeed,
	) -> Result<BuiltBlock<Block, backend::StateBackendFor<B, Block>>, Error> {
		if let None = self.previous_block_extrinsics {
			self.apply_previous_block_extrinsics(seed.clone())
		}
		let mut header = self
			.api
			.finalize_block_with_context(&self.block_id, ExecutionContext::BlockConstruction)?;

		let proof = self.api.extract_proof();

		let state = self.backend.state_at(self.block_id)?;
		let changes_trie_state = backend::changes_tries_state_at_block(
			&self.block_id,
			self.backend.changes_trie_storage(),
		)?;
		let parent_hash = self.parent_hash;

		let storage_changes = self
			.api
			.into_storage_changes(&state, changes_trie_state.as_ref(), parent_hash)
			.map_err(|e| sp_blockchain::Error::StorageChanges(e))?;
		// store hash of all extrinsics include in given bloack
		//
		let curr_block_extrinsics_count = self.extrinsics.len() + self.inherents.len();
		let all_extrinsics: Vec<_> = self
			.inherents
			.iter()
			.chain(self.extrinsics.iter())
			.chain(self.previous_block_extrinsics.unwrap().iter())
			.cloned()
			.collect();

		let extrinsics_root = HashFor::<Block>::ordered_trie_root(
			all_extrinsics.iter().map(Encode::encode).collect(),
		);
		header.set_extrinsics_root(extrinsics_root);
		header.set_seed(seed);
		header.set_count((curr_block_extrinsics_count as u32).into());

		Ok(BuiltBlock {
			block: <Block as BlockT>::new(header, all_extrinsics),
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
	) -> Result<(ShufflingSeed, Vec<Block::Extrinsic>), Error> {
		let block_id = self.block_id;
		let seed = extract_inherent_data(&inherent_data).map_err(|_| {
			sp_blockchain::Error::Backend(String::from(
				"cannot read random seed from inherents data",
			))
		})?;

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
			.map(|inherents| {
				(ShufflingSeed { seed: seed.seed.into(), proof: seed.proof.into() }, inherents)
			})
			.map_err(|e| Error::Application(Box::new(e)))
	}

	/// Estimate the size of the block in the current state.
	///
	/// If `include_proof` is `true`, the estimated size of the storage proof will be added
	/// to the estimation.
	pub fn estimate_block_size(&self, include_proof: bool) -> usize {
		let size = self.estimated_header_size + self.extrinsics.encoded_size();

		if include_proof {
			size + self.api.proof_recorder().map(|pr| pr.estimate_encoded_size()).unwrap_or(0)
		} else {
			size
		}
	}
}

/// Verifies if trasaction can be executed
pub fn validate_transaction<'a, Block, Api>(
	at: &BlockId<Block>,
	api: &'_ Api::Api,
	xt: <Block as BlockT>::Extrinsic,
) -> Result<(), Error>
where
	Block: BlockT,
	Api: ProvideRuntimeApi<Block> + 'a,
	Api::Api: VerApi<Block>,
	Api::Api: BlockBuilderApi<Block>,
{
	match api.get_signer(at, xt.clone()).unwrap() {
		Some((who, nonce)) => log::debug!(target: "block_builder",
			"TX[{:?}] {:?} {} ", BlakeTwo256::hash_of(&xt), who, nonce),
		_ => {},
	};
	api.execute_in_transaction(|api| {
		match api.apply_extrinsic_with_context(at, ExecutionContext::BlockConstruction, xt.clone())
		{
			Ok(Ok(_)) => TransactionOutcome::Commit(Ok(())),
			Ok(Err(tx_validity)) => TransactionOutcome::Rollback(Err(
				ApplyExtrinsicFailed::Validity(tx_validity).into(),
			)),
			Err(e) => TransactionOutcome::Rollback(Err(Error::from(e))),
		}
	})
}

// #[cfg(test)]
// mod tests {
// 	use super::*;
// 	use sp_blockchain::HeaderBackend;
// 	use sp_core::Blake2Hasher;
// 	use sp_state_machine::Backend;
// 	use substrate_test_runtime_client::{DefaultTestClientBuilderExt, TestClientBuilderExt};
//
// 	#[test]
// 	fn block_building_storage_proof_does_not_include_runtime_by_default() {
// 		let builder = substrate_test_runtime_client::TestClientBuilder::new();
// 		let backend = builder.backend();
// 		let client = builder.build();
//
// 		let block = BlockBuilder::new(
// 			&client,
// 			client.info().best_hash,
// 			client.info().best_number,
// 			RecordProof::Yes,
// 			Default::default(),
// 			&*backend,
// 		)
// 		.unwrap()
// 		.build_with_seed(Default::default())
// 		.unwrap();
//
// 		let proof = block.proof.expect("Proof is build on request");
//
// 		let backend = sp_state_machine::create_proof_check_backend::<Blake2Hasher>(
// 			block.storage_changes.transaction_storage_root,
// 			proof,
// 		)
// 		.unwrap();
//
// 		assert!(backend
// 			.storage(&sp_core::storage::well_known_keys::CODE)
// 			.unwrap_err()
// 			.contains("Database missing expected key"),);
// 	}
// }
