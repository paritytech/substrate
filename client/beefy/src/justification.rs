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

use crate::keystore::BeefyKeystore;
use beefy_primitives::{
	crypto::{AuthorityId, Signature},
	ValidatorSet, VersionedFinalityProof,
};
use codec::{Decode, Encode};
use sp_consensus::Error as ConsensusError;
use sp_runtime::traits::{Block as BlockT, NumberFor};

/// A commitment with matching BEEFY authorities' signatures.
pub type BeefySignedCommitment<Block> =
	beefy_primitives::SignedCommitment<NumberFor<Block>, beefy_primitives::crypto::Signature>;

/// Decode and verify a Beefy SignedCommitment.
pub(crate) fn decode_and_verify_commitment<Block: BlockT>(
	encoded: &[u8],
	target_number: NumberFor<Block>,
	validator_set: &ValidatorSet<AuthorityId>,
) -> Result<VersionedFinalityProof<NumberFor<Block>, Signature>, ConsensusError> {
	let proof = <VersionedFinalityProof<NumberFor<Block>, Signature>>::decode(&mut &*encoded)
		.map_err(|_| ConsensusError::InvalidJustification)?;
	verify_with_validator_set::<Block>(target_number, validator_set, &proof).map(|_| proof)
}

/// Verify the Beefy finality proof against the validator set at the block it was generated.
pub(crate) fn verify_with_validator_set<Block: BlockT>(
	target_number: NumberFor<Block>,
	validator_set: &ValidatorSet<AuthorityId>,
	proof: &VersionedFinalityProof<NumberFor<Block>, Signature>,
) -> Result<(), ConsensusError> {
	match proof {
		VersionedFinalityProof::V1(signed_commitment) => {
			if validator_set.len() != signed_commitment.signatures.len() ||
				signed_commitment.commitment.validator_set_id != validator_set.id() ||
				signed_commitment.commitment.block_number != target_number
			{
				return Err(ConsensusError::InvalidJustification)
			}

			// Arrangement of signatures in the commitment should be in the same order as validators
			// for that set
			let message = signed_commitment.commitment.encode();
			if validator_set
				.validators()
				.into_iter()
				.zip(signed_commitment.signatures.iter())
				.filter(|(.., sig)| sig.is_some())
				.all(|(id, signature)| {
					BeefyKeystore::verify(id, signature.as_ref().unwrap(), &message[..])
				}) {
				Ok(())
			} else {
				Err(ConsensusError::InvalidJustification)
			}
		},
	}
}
