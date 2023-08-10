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

use crate::{
	error::Error, justification::BeefyVersionedFinalityProof, keystore::{BeefyKeystore, BeefySignatureHasher},
	LOG_TARGET,
};
use log::debug;
use sc_client_api::Backend;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_consensus_beefy::{
	check_fork_equivocation_proof,
	ecdsa_crypto::{AuthorityId, Signature},
	BeefyApi, ForkEquivocationProof, Payload, PayloadProvider, ValidatorSet, VoteMessage, Commitment, OpaqueKeyOwnershipProof, SignedCommitment,
};
use sp_runtime::{
	generic::BlockId,
	traits::{Block, Header, NumberFor},
};
use std::{marker::PhantomData, sync::Arc};

pub(crate) trait BeefyFisherman<B: Block>: Send + Sync {
	/// Check `vote` for contained block against expected payload.
	fn check_vote(
		&self,
		vote: VoteMessage<NumberFor<B>, AuthorityId, Signature>,
	) -> Result<(), Error>;

	/// Check `signed_commitment` for contained block against expected payload.
	fn check_signed_commitment(
		&self,
		signed_commitment: SignedCommitment<NumberFor<B>, Signature>,
	) -> Result<(), Error>;

	/// Check `proof` for contained block against expected payload.
	fn check_proof(&self, proof: BeefyVersionedFinalityProof<B>) -> Result<(), Error>;
}

/// Helper wrapper used to check gossiped votes for (historical) equivocations,
/// and report any such protocol infringements.
pub(crate) struct Fisherman<B: Block, BE, R, P> {
	pub backend: Arc<BE>,
	pub runtime: Arc<R>,
	pub key_store: Arc<BeefyKeystore>,
	pub payload_provider: P,
	pub _phantom: PhantomData<B>,
}

impl<B, BE, R, P> Fisherman<B, BE, R, P>
where
	B: Block,
	BE: Backend<B>,
	P: PayloadProvider<B>,
	R: ProvideRuntimeApi<B> + Send + Sync,
	R::Api: BeefyApi<B, AuthorityId>,
{
	fn expected_header_and_payload(&self, number: NumberFor<B>) -> Result<(B::Header, Payload), Error> {
		// This should be un-ambiguous since `number` is finalized.
		let hash = self
			.backend
			.blockchain()
			.expect_block_hash_from_id(&BlockId::Number(number))
			.map_err(|e| Error::Backend(e.to_string()))?;
		let header = self
			.backend
			.blockchain()
			.expect_header(hash)
			.map_err(|e| Error::Backend(e.to_string()))?;
		self.payload_provider
			.payload(&header)
			.map(|payload| (header, payload))
			.ok_or_else(|| Error::Backend("BEEFY Payload not found".into()))
	}

	fn active_validator_set_at(
		&self,
		header: &B::Header,
	) -> Result<ValidatorSet<AuthorityId>, Error> {
		self.runtime
			.runtime_api()
			.validator_set(header.hash())
			.map_err(Error::RuntimeApi)?
			.ok_or_else(|| Error::Backend("could not get BEEFY validator set".into()))
	}

	pub(crate) fn report_fork_equivocation(
		&self,
		proof: ForkEquivocationProof<NumberFor<B>, AuthorityId, Signature, B::Header>,
	) -> Result<(), Error> {
		let validator_set = self.active_validator_set_at(&proof.correct_header)?;
		let set_id = validator_set.id();

		let expected_header_hash = self
			.backend
			.blockchain()
			.expect_block_hash_from_id(&BlockId::Number(proof.commitment.block_number))
			.map_err(|e| Error::Backend(e.to_string()))?;

		if proof.commitment.validator_set_id != set_id ||
			!check_fork_equivocation_proof::<NumberFor<B>, AuthorityId, BeefySignatureHasher, B::Header>(&proof, &expected_header_hash)
		{
			debug!(target: LOG_TARGET, "🥩 Skip report for bad invalid fork proof {:?}", proof);
			return Ok(())
		}

		let hash = proof.correct_header.hash();
		let offender_ids = proof.signatories.iter().cloned().map(|(id, _sig)| id).collect::<Vec<_>>();
		let runtime_api = self.runtime.runtime_api();

		// generate key ownership proof at that block
		let key_owner_proofs = offender_ids.iter()
										   .filter_map(|id| {
											   match runtime_api.generate_key_ownership_proof(hash, set_id, id.clone()) {
												   Ok(Some(proof)) => Some(Ok(proof)),
												   Ok(None) => {
													   debug!(
														   target: LOG_TARGET,
														   "🥩 Invalid fork vote offender not part of the authority set."
													   );
													   None
												   },
												   Err(e) => Some(Err(Error::RuntimeApi(e))),
											   }
										   })
										   .collect::<Result<_, _>>()?;

		// submit invalid fork vote report at **best** block
		let best_block_hash = self.backend.blockchain().info().best_hash;
		runtime_api
			.submit_report_fork_equivocation_unsigned_extrinsic(best_block_hash, proof, key_owner_proofs)
			.map_err(Error::RuntimeApi)?;

		Ok(())
	}
}

impl<B, BE, R, P> BeefyFisherman<B> for Fisherman<B, BE, R, P>
where
	B: Block,
	BE: Backend<B>,
	P: PayloadProvider<B>,
	R: ProvideRuntimeApi<B> + Send + Sync,
	R::Api: BeefyApi<B, AuthorityId>,
{
	/// Check `vote` for contained block against expected payload.
	fn check_vote(
		&self,
		vote: VoteMessage<NumberFor<B>, AuthorityId, Signature>,
	) -> Result<(), Error> {
		let number = vote.commitment.block_number;
		let (correct_header, expected_payload) = self.expected_header_and_payload(number)?;
		if vote.commitment.payload != expected_payload {
			let proof = ForkEquivocationProof { commitment: vote.commitment, signatories: vec![(vote.id, vote.signature)], correct_header: correct_header.clone() };
			self.report_fork_equivocation(proof)?;
		}
		Ok(())
	}

	/// Check `signed_commitment` for contained block against expected payload.
	fn check_signed_commitment(
		&self,
		signed_commitment: SignedCommitment<NumberFor<B>, Signature>,
	) -> Result<(), Error> {
		let SignedCommitment {commitment, signatures} = signed_commitment;
		let number = commitment.block_number;
		let (correct_header, expected_payload) = self.expected_header_and_payload(number)?;
		if commitment.payload != expected_payload {
			let validator_set = self.active_validator_set_at(&correct_header)?;
			if signatures.len() != validator_set.validators().len() {
				// invalid proof
				return Ok(())
			}
			// report every signer of the bad justification
			let signatories = validator_set.validators().iter().cloned().zip(signatures.into_iter())
																		.filter_map(|(id, signature)| signature.map(|sig| (id, sig))).collect();

			let proof = ForkEquivocationProof { commitment, signatories, correct_header: correct_header.clone() };
			self.report_fork_equivocation(proof)?;
		}
		Ok(())
	}

	/// Check `proof` for contained block against expected payload.
	fn check_proof(&self, proof: BeefyVersionedFinalityProof<B>) -> Result<(), Error> {
		match proof {
			BeefyVersionedFinalityProof::<B>::V1(signed_commitment) => {
				self.check_signed_commitment(signed_commitment)
			}
		}
	}
}
