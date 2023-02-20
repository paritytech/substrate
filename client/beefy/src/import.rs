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

use beefy_primitives::{BeefyApi, BEEFY_ENGINE_ID};
use log::debug;
use std::{collections::HashMap, sync::Arc};

use sp_api::{ProvideRuntimeApi, TransactionFor};
use sp_blockchain::well_known_cache_keys;
use sp_consensus::Error as ConsensusError;
use sp_runtime::{
	traits::{Block as BlockT, Header as HeaderT, NumberFor},
	EncodedJustification,
};

use sc_client_api::backend::Backend;
use sc_consensus::{BlockCheckParams, BlockImport, BlockImportParams, ImportResult};

use crate::{
	communication::notification::BeefyVersionedFinalityProofSender,
	justification::{decode_and_verify_finality_proof, BeefyVersionedFinalityProof},
	metric_inc,
	metrics::BlockImportMetrics,
	LOG_TARGET,
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
	justification_sender: BeefyVersionedFinalityProofSender<Block>,
	metrics: Option<BlockImportMetrics>,
}

impl<Block: BlockT, BE, Runtime, I: Clone> Clone for BeefyBlockImport<Block, BE, Runtime, I> {
	fn clone(&self) -> Self {
		BeefyBlockImport {
			backend: self.backend.clone(),
			runtime: self.runtime.clone(),
			inner: self.inner.clone(),
			justification_sender: self.justification_sender.clone(),
			metrics: self.metrics.clone(),
		}
	}
}

impl<Block: BlockT, BE, Runtime, I> BeefyBlockImport<Block, BE, Runtime, I> {
	/// Create a new BeefyBlockImport.
	pub fn new(
		backend: Arc<BE>,
		runtime: Arc<Runtime>,
		inner: I,
		justification_sender: BeefyVersionedFinalityProofSender<Block>,
		metrics: Option<BlockImportMetrics>,
	) -> BeefyBlockImport<Block, BE, Runtime, I> {
		BeefyBlockImport { backend, runtime, inner, justification_sender, metrics }
	}
}

impl<Block, BE, Runtime, I> BeefyBlockImport<Block, BE, Runtime, I>
where
	Block: BlockT,
	BE: Backend<Block>,
	Runtime: ProvideRuntimeApi<Block>,
	Runtime::Api: BeefyApi<Block> + Send,
{
	fn decode_and_verify(
		&self,
		encoded: &EncodedJustification,
		number: NumberFor<Block>,
		hash: <Block as BlockT>::Hash,
	) -> Result<BeefyVersionedFinalityProof<Block>, ConsensusError> {
		use ConsensusError::ClientImport as ImportError;
		let beefy_genesis = self
			.runtime
			.runtime_api()
			.beefy_genesis(hash)
			.map_err(|e| ImportError(e.to_string()))?
			.ok_or_else(|| ImportError("Unknown BEEFY genesis".to_string()))?;
		if number < beefy_genesis {
			return Err(ImportError("BEEFY genesis is set for future block".to_string()))
		}
		let validator_set = self
			.runtime
			.runtime_api()
			.validator_set(hash)
			.map_err(|e| ImportError(e.to_string()))?
			.ok_or_else(|| ImportError("Unknown validator set".to_string()))?;

		decode_and_verify_finality_proof::<Block>(&encoded[..], number, &validator_set)
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

		let beefy_encoded = block.justifications.as_mut().and_then(|just| {
			let encoded = just.get(BEEFY_ENGINE_ID).cloned();
			// Remove BEEFY justification from the list before giving to `inner`; we send it to the
			// voter (beefy-gadget) and it will append it to the backend after block is finalized.
			just.remove(BEEFY_ENGINE_ID);
			encoded
		});

		// Run inner block import.
		let inner_import_result = self.inner.import_block(block, new_cache).await?;

		match (beefy_encoded, &inner_import_result) {
			(Some(encoded), ImportResult::Imported(_)) => {
				match self.decode_and_verify(&encoded, number, hash) {
					Ok(proof) => {
						// The proof is valid and the block is imported and final, we can import.
						debug!(
							target: LOG_TARGET,
							"🥩 import justif {:?} for block number {:?}.", proof, number
						);
						// Send the justification to the BEEFY voter for processing.
						self.justification_sender
							.notify(|| Ok::<_, ()>(proof))
							.expect("the closure always returns Ok; qed.");
						metric_inc!(self, beefy_good_justification_imports);
					},
					Err(err) => {
						debug!(
							target: LOG_TARGET,
							"🥩 error importing BEEFY justification for block {:?}: {:?}",
							number,
							err,
						);
						metric_inc!(self, beefy_bad_justification_imports);
					},
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
