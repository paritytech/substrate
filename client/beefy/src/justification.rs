use crate::keystore::BeefyKeystore;
use beefy_primitives::{
	crypto::{AuthorityId, Signature},
	ValidatorSet, VersionedFinalityProof,
};
use codec::{Decode, Encode};
use sp_consensus::Error as ConsensusError;
use sp_runtime::traits::{Block as BlockT, NumberFor};

/// Decodes a Beefy justification and verifies it
pub(crate) fn decode_and_verify_justification<Block: BlockT>(
	encoded: &[u8],
	validator_set: &ValidatorSet<AuthorityId>,
) -> Result<VersionedFinalityProof<NumberFor<Block>, Signature>, ConsensusError> {
	let finality_proof =
		<VersionedFinalityProof<NumberFor<Block>, Signature>>::decode(&mut &*encoded)
			.map_err(|_| ConsensusError::InvalidJustification)?;

	let res = verify_with_validator_set::<Block>(validator_set, finality_proof.clone())?;

	if res {
		return Ok(finality_proof)
	}

	Err(ConsensusError::InvalidJustification)
}

/// Verify the Beefy provided finality proof
/// against the validtor set at the block it was generated
pub(crate) fn verify_with_validator_set<Block: BlockT>(
	validator_set: &ValidatorSet<AuthorityId>,
	proof: VersionedFinalityProof<NumberFor<Block>, Signature>,
) -> Result<bool, ConsensusError> {
	let result = match proof {
		VersionedFinalityProof::V1(signed_commitment) => {
			if validator_set.len() != signed_commitment.signatures.len() ||
				signed_commitment.commitment.validator_set_id != validator_set.id()
			{
				return Err(ConsensusError::InvalidJustification)
			}

			// Arrangement of signatures in the commitment should be in the same order as validators
			// for that set
			let message = signed_commitment.commitment.encode();
			validator_set
				.validators()
				.into_iter()
				.zip(signed_commitment.signatures.into_iter())
				.filter(|(.., sig)| sig.is_some())
				.all(|(id, signature)| {
					BeefyKeystore::verify(id, signature.as_ref().unwrap(), &message[..])
				})
		},
	};

	Ok(result)
}
