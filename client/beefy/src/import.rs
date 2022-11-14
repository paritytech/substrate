// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

use beefy_primitives::{crypto::Signature, BeefyApi, VersionedFinalityProof, BEEFY_ENGINE_ID};
use codec::Encode;
use log::error;
use std::{collections::HashMap, sync::Arc};

use sp_api::{ProvideRuntimeApi, TransactionFor};
use sp_blockchain::{well_known_cache_keys, HeaderBackend};
use sp_consensus::Error as ConsensusError;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT, NumberFor},
	EncodedJustification,
};

use sc_client_api::backend::Backend;
use sc_consensus::{BlockCheckParams, BlockImport, BlockImportParams, ImportResult};

use crate::{
	justification::decode_and_verify_commitment, notification::BeefySignedCommitmentSender,
};

/// A block-import handler for BEEFY.
///
/// This scans each imported block for BEEFY justifications and verifies them.
/// Wraps a `inner: BlockImport` and ultimately defers to it.
///
/// When using BEEFY, the block import worker should be using this block import object.
pub struct BeefyBlockImport<Block: BlockT, Backend, RuntimeApi, I> {
	backend: Arc<Backend>,
	runtime: Arc<RuntimeApi>,
	inner: I,
	justification_sender: BeefySignedCommitmentSender<Block>,
}

impl<Block: BlockT, BE, Runtime, I: Clone> Clone for BeefyBlockImport<Block, BE, Runtime, I> {
	fn clone(&self) -> Self {
		BeefyBlockImport {
			backend: self.backend.clone(),
			runtime: self.runtime.clone(),
			inner: self.inner.clone(),
			justification_sender: self.justification_sender.clone(),
		}
	}
}

impl<Block: BlockT, BE, Runtime, I> BeefyBlockImport<Block, BE, Runtime, I> {
	/// Create a new BeefyBlockImport.
	pub fn new(
		backend: Arc<BE>,
		runtime: Arc<Runtime>,
		inner: I,
		justification_sender: BeefySignedCommitmentSender<Block>,
	) -> BeefyBlockImport<Block, BE, Runtime, I> {
		BeefyBlockImport { backend, runtime, inner, justification_sender }
	}
}

impl<Block, BE, Runtime, I> BeefyBlockImport<Block, BE, Runtime, I>
where
	Block: BlockT,
	BE: Backend<Block>,
	Runtime: ProvideRuntimeApi<Block>,
	Runtime::Api: BeefyApi<Block> + Send + Sync,
{
	fn decode_and_verify(
		&self,
		encoded: &EncodedJustification,
		number: NumberFor<Block>,
		hash: <Block as BlockT>::Hash,
	) -> Result<VersionedFinalityProof<NumberFor<Block>, Signature>, ConsensusError> {
		let block_id = BlockId::hash(hash);
		let validator_set = self
			.runtime
			.runtime_api()
			.validator_set(&block_id)
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
			.ok_or_else(|| ConsensusError::ClientImport("Unknown validator set".to_string()))?;

		decode_and_verify_commitment::<Block>(&encoded[..], number, &validator_set)
	}

	/// Import BEEFY justification: Send it to worker for processing and also append it to backend.
	///
	/// This function assumes:
	/// - `justification` is verified and valid,
	/// - the block referred by `justification` has been imported _and_ finalized.
	fn import_beefy_justification_unchecked(
		&self,
		number: NumberFor<Block>,
		justification: VersionedFinalityProof<NumberFor<Block>, Signature>,
	) {
		// Append the justification to the block in the backend.
		if let Err(e) = self.backend.append_justification(
			BlockId::Number(number),
			(BEEFY_ENGINE_ID, justification.encode()),
		) {
			error!(target: "beefy", "🥩 Error {:?} on appending justification: {:?}", e, justification);
		}
		// Send the justification to the BEEFY voter for processing.
		match justification {
			// TODO #11838: Should not unpack, these channels should also use
			// `VersionedFinalityProof`.
			VersionedFinalityProof::V1(signed_commitment) => self
				.justification_sender
				.notify(|| Ok::<_, ()>(signed_commitment))
				.expect("forwards closure result; the closure always returns Ok; qed."),
		};
	}
}

#[async_trait::async_trait]
impl<Block, BE, Runtime, I> BlockImport<Block> for BeefyBlockImport<Block, BE, Runtime, I>
where
	Block: BlockT,
	BE: Backend<Block>,
	I: BlockImport<
			Block,
			Error = ConsensusError,
			Transaction = sp_api::TransactionFor<Runtime, Block>,
		> + Send
		+ Sync,
	Runtime: ProvideRuntimeApi<Block> + Send + Sync,
	Runtime::Api: BeefyApi<Block>,
{
	type Error = ConsensusError;
	type Transaction = TransactionFor<Runtime, Block>;

	async fn import_block(
		&mut self,
		mut block: BlockImportParams<Block, Self::Transaction>,
		new_cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let hash = block.post_hash();
		let number = *block.header.number();

		let beefy_proof = block
			.justifications
			.as_mut()
			.and_then(|just| {
				let decoded = just
					.get(BEEFY_ENGINE_ID)
					.map(|encoded| self.decode_and_verify(encoded, number, hash));
				// Remove BEEFY justification from the list before giving to `inner`;
				// we will append it to backend ourselves at the end if all goes well.
				just.remove(BEEFY_ENGINE_ID);
				decoded
			})
			.transpose()
			.unwrap_or(None);

		// Run inner block import.
		let inner_import_result = self.inner.import_block(block, new_cache).await?;

		match (beefy_proof, &inner_import_result) {
			(Some(proof), ImportResult::Imported(_)) => {
				let status = self.backend.blockchain().info();
				if number <= status.finalized_number &&
					Some(hash) ==
						self.backend
							.blockchain()
							.hash(number)
							.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
				{
					// The proof is valid and the block is imported and final, we can import.
					self.import_beefy_justification_unchecked(number, proof);
				} else {
					error!(
						target: "beefy",
						"🥩 Cannot import justification: {:?} for, not yet final, block number {:?}",
						proof,
						number,
					);
				}
			},
			_ => (),
		}

		Ok(inner_import_result)
	}

	async fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		self.inner.check_block(block).await
	}
}
