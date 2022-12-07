// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use codec::{Decode, Encode};

use sp_api::{
	ApiExt, ApiRef, Core, ProvideRuntimeApi, StorageChanges, StorageProof, TransactionOutcome,
};
use sp_blockchain::{ApplyExtrinsicFailed, Error};
use sp_core::ExecutionContext;
use sp_runtime::{
	generic::BlockId,
	legacy,
	traits::{BlakeTwo256, Block as BlockT, Hash, HashFor, Header as HeaderT, NumberFor, One},
	Digest,
};

pub use sp_block_builder::BlockBuilder as BlockBuilderApi;
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

/// use proper api for applying extriniscs basedon version
pub fn apply_transaction_wrapper<'a, Block, Api>(
	api: &<Api as ProvideRuntimeApi<Block>>::Api,
	block_id: &BlockId<Block>,
	xt: Block::Extrinsic,
	context: ExecutionContext,
) -> Result<sp_runtime::ApplyExtrinsicResult, sp_api::ApiError>
where
	Block: BlockT,
	Api: ProvideRuntimeApi<Block> + 'a,
	Api::Api: BlockBuilderApi<Block>,
{
	let version = api
		.api_version::<dyn BlockBuilderApi<Block>>(&block_id)?
		.ok_or_else(|| Error::VersionInvalid("BlockBuilderApi".to_string()))?;

	if version < 6 {
		#[allow(deprecated)]
		api.apply_extrinsic_before_version_6_with_context(block_id, context, xt)
			.map(legacy::byte_sized_error::convert_to_latest)
	} else {
		api.apply_extrinsic_with_context(block_id, context, xt)
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
		inherent_digests: Digest,
		record_proof: R,
	) -> sp_blockchain::Result<BlockBuilder<Block, RA, B>>;

	/// Create a new block, built on the head of the chain.
	fn new_block(
		&self,
		inherent_digests: Digest,
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
		inherent_digests: Digest,
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
			estimated_header_size,
		})
	}

	/// temporaily apply extrinsics and record them on the list
	pub fn build_with_seed<
		F: FnOnce(
			&'_ BlockId<Block>,
			&'_ A::Api,
		) -> Vec<(Option<sp_runtime::AccountId32>, Block::Extrinsic)>,
	>(
		mut self,
		seed: ShufflingSeed,
		call: F,
	) -> Result<BuiltBlock<Block, backend::StateBackendFor<B, Block>>, Error> {
		let block_id = self.block_id;

		let mut valid_txs = if self.api.can_enqueue_txs(&block_id).unwrap() {
			self.api.execute_in_transaction(|api| {
				let next_header = api
					.finalize_block_with_context(&block_id, ExecutionContext::BlockConstruction)
					.unwrap();

				api.start_prevalidation(&block_id).unwrap();

				// create dummy header just to condider N+1 block extrinsics like new session
				let header = <<Block as BlockT>::Header as HeaderT>::new(
					*next_header.number() + One::one(),
					Default::default(),
					Default::default(),
					next_header.hash(),
					Default::default(),
				);

				if api.is_storage_migration_scheduled(&self.block_id).unwrap() {
					log::debug!(target:"block_builder", "storage migration scheduled - ignoring any txs");
					TransactionOutcome::Rollback(vec![])
				} else {
					api.initialize_block_with_context(
						&self.block_id,
						ExecutionContext::BlockConstruction,
						&header,
					)
					.unwrap();
					let txs = call(&self.block_id, &api);
					TransactionOutcome::Rollback(txs)
				}
			})
		} else {
			log::info!(target:"block_builder", "storage queue is full, no room for new txs");
			vec![]
		};

		// that should be improved at some point
		if valid_txs.len() > 100 {
			valid_txs.truncate(valid_txs.len() * 90 / 100);
		}

		let valid_txs_count = valid_txs.len();
		let store_txs_inherent = self
			.api
			.create_enqueue_txs_inherent(
				&self.block_id,
				valid_txs.into_iter().map(|(_, tx)| tx).collect(),
			)
			.unwrap();

		apply_transaction_wrapper::<Block, A>(
			&self.api,
			&self.block_id,
			store_txs_inherent.clone(),
			ExecutionContext::BlockConstruction,
		)
		.unwrap()
		.unwrap()
		.unwrap();

		// TODO get rid of collect
		let mut next_header = self
			.api
			.finalize_block_with_context(&self.block_id, ExecutionContext::BlockConstruction)?;

		let proof = self.api.extract_proof();

		let state = self.backend.state_at(self.block_id)?;
		let parent_hash = self.parent_hash;
		let storage_changes = self
			.api
			.into_storage_changes(&state, parent_hash)
			.map_err(sp_blockchain::Error::StorageChanges)?;

		log::debug!(target: "block_builder", "consume {} valid transactios", valid_txs_count);

		// store hash of all extrinsics include in given bloack
		//
		let all_extrinsics: Vec<_> = self
			.inherents
			.iter()
			.chain(self.extrinsics.iter())
			.chain(std::iter::once(&store_txs_inherent))
			.cloned()
			.collect();

		let extrinsics_root = HashFor::<Block>::ordered_trie_root(
			all_extrinsics.iter().map(Encode::encode).collect(),
			sp_runtime::StateVersion::V0,
		);
		next_header.set_extrinsics_root(extrinsics_root);
		next_header.set_seed(seed);
		next_header.set_count((self.extrinsics.len() as u32).into());

		Ok(BuiltBlock {
			block: <Block as BlockT>::new(next_header, all_extrinsics),
			storage_changes,
			proof,
		})
	}

	/// Push onto the block's list of extrinsics.
	///
	/// validate extrinsics but without commiting the change
	pub fn push(&mut self, xt: <Block as BlockT>::Extrinsic) -> Result<(), Error> {
		let block_id = &self.block_id;
		let inherents = &mut self.inherents;

		self.api.execute_in_transaction(|api| {
			match apply_transaction_wrapper::<Block, A>(
				api,
				block_id,
				xt.clone(),
				ExecutionContext::BlockConstruction,
			) {
				Ok(Ok(_)) => {
					inherents.push(xt);
					TransactionOutcome::Commit(Ok(()))
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
	pub fn apply_previous_block_extrinsics<F>(
		&mut self,
		seed: ShufflingSeed,
		block_size: &mut usize,
		max_block_size: usize,
		is_timer_expired: F,
	) where
		F: Fn() -> bool,
	{
		let block_id = &self.block_id;
		self.api.store_seed(&block_id, seed.seed).unwrap();
		let extrinsics = &mut self.extrinsics;

		let previous_block_txs = self.api.get_previous_block_txs(&block_id).unwrap();
		let previous_block_txs_count = previous_block_txs.len();
		log::debug!(target: "block_builder", "previous block enqueued {} txs", previous_block_txs_count);

		for tx_bytes in previous_block_txs {
			if (*block_size + tx_bytes.len() ) > max_block_size {
				break
			}

			if let Ok(xt) = <Block as BlockT>::Extrinsic::decode(&mut tx_bytes.as_slice()) {
				if self.api.execute_in_transaction(|api| { // execute tx to get execution status
					match apply_transaction_wrapper::<Block, A>(
						api,
						block_id,
						xt.clone(),
						ExecutionContext::BlockConstruction,
					) {

						_ if is_timer_expired() => {
							log::debug!(target: "block_builder", "timer expired no room for other txs from queue");
							TransactionOutcome::Rollback(false)
						},
						Ok(Err(validity_err)) if validity_err.exhausted_resources() => {
							log::debug!(target: "block_builder", "exhaust resources no room for other txs from queue");
							TransactionOutcome::Rollback(false)
						},
						Ok(Ok(_)) => {TransactionOutcome::Commit(true)}
						Ok(Err(validity_err)) => {
							log::warn!(target: "block_builder", "enqueued tx execution {} failed '${}'", BlakeTwo256::hash(&xt.encode()), validity_err);
							TransactionOutcome::Commit(true)
						},
						Err(_e) => {
							log::warn!(target: "block_builder", "enqueued tx execution {} failed - unknwown execution problem", BlakeTwo256::hash(&xt.encode()));
							TransactionOutcome::Commit(true)
						}
					}
				}){
					extrinsics.push(xt);
					*block_size += tx_bytes.len() + sp_core::H256::len_bytes();
				}else{
					break;
				}
			} else {
				log::warn!(target: "block_builder", "cannot decode tx");
			}
		}

		self.api.pop_txs(&block_id, extrinsics.len() as u64).unwrap();
		log::info!(target: "block_builder", "executed {}/{} previous block transactions", extrinsics.len(), previous_block_txs_count);
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
	pub fn estimate_block_size_without_extrinsics(&self, include_proof: bool) -> usize {
		let size = self.estimated_header_size +
			self.inherents.encoded_size() +
			self.api
				.create_enqueue_txs_inherent(&self.block_id, Default::default())
				.unwrap()
				.encoded_size();

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
	api.execute_in_transaction(|api| {
		match apply_transaction_wrapper::<Block, Api>(
			api,
			at,
			xt.clone(),
			ExecutionContext::BlockConstruction,
		) {
			Ok(Ok(_)) => TransactionOutcome::Commit(Ok(())),
			Ok(Err(tx_validity)) => TransactionOutcome::Rollback(Err(
				ApplyExtrinsicFailed::Validity(tx_validity).into(),
			)),
			Err(e) => TransactionOutcome::Rollback(Err(Error::from(e))),
		}
	})
}

#[cfg(test)]
mod tests {

	// #[test]
	// fn block_building_storage_proof_does_not_include_runtime_by_default() {
	// 	let builder = substrate_test_runtime_client::TestClientBuilder::new();
	// 	let backend = builder.backend();
	// 	let client = builder.build();
	//
	// 	let block = BlockBuilder::new(
	// 		&client,
	// 		client.info().best_hash,
	// 		client.info().best_number,
	// 		RecordProof::Yes,
	// 		Default::default(),
	// 		&*backend,
	// 	)
	// 	.unwrap()
	// 	.build_with_seed(Default::default())
	// 	.unwrap();
	//
	// 	let proof = block.proof.expect("Proof is build on request");
	//
	// 	let backend = sp_state_machine::create_proof_check_backend::<Blake2Hasher>(
	// 		block.storage_changes.transaction_storage_root,
	// 		proof,
	// 	)
	// 	.unwrap();
	//
	// 	assert!(backend
	// 		.storage(&sp_core::storage::well_known_keys::CODE)
	// 		.unwrap_err()
	// 		.contains("Database missing expected key"),);
	// }
}
