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
fn verify_with_validator_set<Block: BlockT>(
	target_number: NumberFor<Block>,
	validator_set: &ValidatorSet<AuthorityId>,
	proof: &VersionedFinalityProof<NumberFor<Block>, Signature>,
) -> Result<(), ConsensusError> {
	match proof {
		VersionedFinalityProof::V1(signed_commitment) => {
			if signed_commitment.signatures.len() != validator_set.len() ||
				signed_commitment.commitment.validator_set_id != validator_set.id() ||
				signed_commitment.commitment.block_number != target_number
			{
				return Err(ConsensusError::InvalidJustification)
			}

			// Arrangement of signatures in the commitment should be in the same order
			// as validators for that set.
			let message = signed_commitment.commitment.encode();
			let valid_signatures = validator_set
				.validators()
				.into_iter()
				.zip(signed_commitment.signatures.iter())
				.filter(|(id, signature)| {
					signature
						.as_ref()
						.map(|sig| BeefyKeystore::verify(id, sig, &message[..]))
						.unwrap_or(false)
				})
				.count();
			if valid_signatures >= crate::round::threshold(validator_set.len()) {
				Ok(())
			} else {
				Err(ConsensusError::InvalidJustification)
			}
		},
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use beefy_primitives::{known_payload_ids, Commitment, Payload, SignedCommitment};
	use substrate_test_runtime_client::runtime::Block;

	use super::*;
	use crate::{keystore::tests::Keyring, tests::make_beefy_ids};

	pub(crate) fn new_signed_commitment(
		block_num: NumberFor<Block>,
		validator_set: &ValidatorSet<AuthorityId>,
		keys: &[Keyring],
	) -> BeefySignedCommitment<Block> {
		let commitment = Commitment {
			payload: Payload::new(known_payload_ids::MMR_ROOT_ID, vec![]),
			block_number: block_num,
			validator_set_id: validator_set.id(),
		};
		let message = commitment.encode();
		let signatures = keys.iter().map(|key| Some(key.sign(&message))).collect();
		SignedCommitment { commitment, signatures }
	}

	#[test]
	fn should_verify_with_validator_set() {
		let keys = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();

		// build valid justification
		let block_num = 42;
		let proof = new_signed_commitment(block_num, &validator_set, keys);

		let good_proof = proof.clone().into();
		// should verify successfully
		verify_with_validator_set::<Block>(block_num, &validator_set, &good_proof).unwrap();

		// wrong block number -> should fail verification
		let good_proof = proof.clone().into();
		match verify_with_validator_set::<Block>(block_num + 1, &validator_set, &good_proof) {
			Err(ConsensusError::InvalidJustification) => (),
			_ => assert!(false, "Expected Err(ConsensusError::InvalidJustification)"),
		};

		// wrong validator set id -> should fail verification
		let good_proof = proof.clone().into();
		let other = ValidatorSet::new(make_beefy_ids(keys), 1).unwrap();
		match verify_with_validator_set::<Block>(block_num, &other, &good_proof) {
			Err(ConsensusError::InvalidJustification) => (),
			_ => assert!(false, "Expected Err(ConsensusError::InvalidJustification)"),
		};

		// wrong signatures length -> should fail verification
		let mut bad_proof = proof.clone();
		// change length of signatures
		bad_proof.signatures.pop().flatten().unwrap();
		match verify_with_validator_set::<Block>(block_num + 1, &validator_set, &bad_proof.into()) {
			Err(ConsensusError::InvalidJustification) => (),
			_ => assert!(false, "Expected Err(ConsensusError::InvalidJustification)"),
		};

		// not enough signatures -> should fail verification
		let mut bad_proof = proof.clone();
		// remove a signature (but same length)
		*bad_proof.signatures.first_mut().unwrap() = None;
		match verify_with_validator_set::<Block>(block_num + 1, &validator_set, &bad_proof.into()) {
			Err(ConsensusError::InvalidJustification) => (),
			_ => assert!(false, "Expected Err(ConsensusError::InvalidJustification)"),
		};

		// not enough _correct_ signatures -> should fail verification
		let mut bad_proof = proof.clone();
		// change a signature to a different key
		*bad_proof.signatures.first_mut().unwrap() =
			Some(Keyring::Dave.sign(&proof.commitment.encode()));
		match verify_with_validator_set::<Block>(block_num + 1, &validator_set, &bad_proof.into()) {
			Err(ConsensusError::InvalidJustification) => (),
			_ => assert!(false, "Expected Err(ConsensusError::InvalidJustification)"),
		};
	}

	#[test]
	fn should_decode_and_verify_commitment() {
		let keys = &[Keyring::Alice, Keyring::Bob];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let block_num = 1;

		// build valid justification
		let proof = new_signed_commitment(block_num, &validator_set, keys);
		let versioned_proof: VersionedFinalityProof<NumberFor<Block>, Signature> = proof.into();
		let encoded = versioned_proof.encode();

		// should successfully decode and verify
		let verified =
			decode_and_verify_commitment::<Block>(&encoded, block_num, &validator_set).unwrap();
		assert_eq!(verified, versioned_proof);
	}
}
