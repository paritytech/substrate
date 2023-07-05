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

use crate::justification::BeefyVersionedFinalityProof;
use sc_client_api::Backend;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_consensus_beefy::{
	crypto::{AuthorityId, Signature},
	BeefyApi, Payload, PayloadProvider, VoteMessage,
};
use sp_runtime::{
	generic::BlockId,
	traits::{Block, NumberFor},
};
use std::{marker::PhantomData, sync::Arc};

pub(crate) trait BeefyFisherman<B: Block>: Send + Sync {
	/// Check `vote` for contained finalized block against expected payload.
	///
	/// Note: this fn expects `vote.commitment.block_number` to be finalized.
	fn check_vote(
		&self,
		vote: VoteMessage<NumberFor<B>, AuthorityId, Signature>,
	) -> Result<(), sp_blockchain::Error>;

	/// Check `proof` for contained finalized block against expected payload.
	///
	/// Note: this fn expects block referenced in `proof` to be finalized.
	fn check_proof(
		&self,
		proof: BeefyVersionedFinalityProof<B>,
	) -> Result<(), sp_blockchain::Error>;
}

/// Helper wrapper used to check gossiped votes for (historical) equivocations,
/// and report any such protocol infringements.
pub(crate) struct Fisherman<B: Block, BE, R, P> {
	pub backend: Arc<BE>,
	pub runtime: Arc<R>,
	pub payload_provider: P,
	pub _phantom: PhantomData<B>,
}

impl<B, BE, R, P> Fisherman<B, BE, R, P>
where
	B: Block,
	BE: Backend<B>,
	P: PayloadProvider<B>,
{
	fn expected_payload(&self, number: NumberFor<B>) -> Result<Payload, sp_blockchain::Error> {
		// This should be un-ambiguous since `number` is finalized.
		let hash = self.backend.blockchain().expect_block_hash_from_id(&BlockId::Number(number))?;
		let header = self.backend.blockchain().expect_header(hash)?;
		self.payload_provider
			.payload(&header)
			.ok_or_else(|| sp_blockchain::Error::Backend("BEEFY Payload not found".into()))
	}
}

impl<B, BE, R, P> BeefyFisherman<B> for Fisherman<B, BE, R, P>
where
	B: Block,
	BE: Backend<B>,
	P: PayloadProvider<B>,
	R: ProvideRuntimeApi<B> + Send + Sync,
	R::Api: BeefyApi<B>,
{
	/// Check `vote` for contained finalized block against expected payload.
	///
	/// Note: this fn expects `vote.commitment.block_number` to be finalized.
	fn check_vote(
		&self,
		vote: VoteMessage<NumberFor<B>, AuthorityId, Signature>,
	) -> Result<(), sp_blockchain::Error> {
		let number = vote.commitment.block_number;
		let expected = self.expected_payload(number)?;
		if vote.commitment.payload != expected {
			// TODO: report equivocation
		}
		Ok(())
	}

	/// Check `proof` for contained finalized block against expected payload.
	///
	/// Note: this fn expects block referenced in `proof` to be finalized.
	fn check_proof(
		&self,
		proof: BeefyVersionedFinalityProof<B>,
	) -> Result<(), sp_blockchain::Error> {
		let payload = proof.payload();
		let expected = self.expected_payload(*proof.number())?;
		if payload != &expected {
			// TODO: report equivocation
		}
		Ok(())
	}
}
