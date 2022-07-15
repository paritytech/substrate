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

use std::{collections::HashMap, marker::PhantomData, sync::Arc};

use sp_api::{ProvideRuntimeApi, TransactionFor};
use sp_blockchain::well_known_cache_keys;
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
	Client as BeefyClient,
};
use beefy_primitives::{crypto::Signature, BeefyApi, VersionedFinalityProof, BEEFY_ENGINE_ID};

/// A block-import handler for BEEFY.
///
/// This scans each imported block for BEEFY justifications and verifies them.
/// Wraps a `inner: BlockImport` and ultimately defers to it.
///
/// When using BEEFY, the block import worker should be using this block import object.
pub struct BeefyBlockImport<Backend, Block: BlockT, Client, I> {
	client: Arc<Client>,
	inner: I,
	justification_sender: BeefySignedCommitmentSender<Block>,
	_phantom: PhantomData<Backend>,
}

impl<BE, Block: BlockT, Client, I: Clone> Clone for BeefyBlockImport<BE, Block, Client, I> {
	fn clone(&self) -> Self {
		BeefyBlockImport {
			client: self.client.clone(),
			inner: self.inner.clone(),
			justification_sender: self.justification_sender.clone(),
			_phantom: PhantomData,
		}
	}
}

impl<BE, Block: BlockT, Client, I> BeefyBlockImport<BE, Block, Client, I> {
	/// Create a new BeefyBlockImport.
	pub fn new(
		client: Arc<Client>,
		inner: I,
		justification_sender: BeefySignedCommitmentSender<Block>,
	) -> BeefyBlockImport<BE, Block, Client, I> {
		BeefyBlockImport { inner, client, justification_sender, _phantom: PhantomData }
	}
}

impl<BE, Block, Client, I> BeefyBlockImport<BE, Block, Client, I>
where
	BE: Backend<Block>,
	Block: BlockT,
	Client: BeefyClient<Block, BE> + ProvideRuntimeApi<Block>,
	Client::Api: BeefyApi<Block>,
{
	fn import_beefy_justification(
		&self,
		encoded: &EncodedJustification,
		number: NumberFor<Block>,
		hash: <Block as BlockT>::Hash,
	) -> Result<VersionedFinalityProof<NumberFor<Block>, Signature>, ConsensusError> {
		let block_id = BlockId::hash(hash);
		let validator_set = self
			.client
			.runtime_api()
			.validator_set(&block_id)
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
			.ok_or_else(|| ConsensusError::ClientImport("Unknown validator set".to_string()))?;

		decode_and_verify_commitment::<Block>(&encoded[..], number, &validator_set)
	}
}

#[async_trait::async_trait]
impl<BE, Block: BlockT, Client, I> BlockImport<Block> for BeefyBlockImport<BE, Block, Client, I>
where
	BE: Backend<Block>,
	I: BlockImport<
			Block,
			Error = ConsensusError,
			Transaction = sp_api::TransactionFor<Client, Block>,
		> + Send
		+ Sync,
	Client: BeefyClient<Block, BE> + ProvideRuntimeApi<Block>,
	Client::Api: BeefyApi<Block>,
{
	type Error = ConsensusError;
	type Transaction = TransactionFor<Client, Block>;

	async fn import_block(
		&mut self,
		mut block: BlockImportParams<Block, Self::Transaction>,
		new_cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let hash = block.post_hash();
		let number = *block.header.number();

		let beefy_proof = block
			.justifications
			.as_ref()
			.and_then(|just| just.get(BEEFY_ENGINE_ID))
			.map(|encoded| self.import_beefy_justification(encoded, number, hash))
			.and_then(|result| match result {
				Ok(proof) => Some(proof),
				Err(ConsensusError::InvalidJustification) => {
					// remove invalid justification from the list before giving to `inner`
					block.justifications.as_mut().and_then(|j| {
						j.remove(BEEFY_ENGINE_ID);
						None
					})
				},
				_ => None,
			});

		// Run inner block import.
		let inner_import_result = self.inner.import_block(block, new_cache).await?;

		match (beefy_proof, &inner_import_result) {
			// If both BEEFY proof valid and block import success, send proof to voter.
			(Some(proof), ImportResult::Imported(_)) => {
				match proof {
					// TODO #11838: Should not unpack, these channels should also use
					// `VersionedFinalityProof`.
					VersionedFinalityProof::V1(signed_commitment) => self
						.justification_sender
						.notify(|| Ok::<_, ()>(signed_commitment))
						.expect("forwards closure result; the closure always returns Ok; qed."),
				};
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
