// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Private implementation details of BABE digests.

#[cfg(feature = "std")]
use super::{BABE_ENGINE_ID, AuthoritySignature};
#[cfg(not(feature = "std"))]
use super::{VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH};
use super::{AuthorityId, AuthorityIndex, SlotNumber, BabeAuthorityWeight};
#[cfg(feature = "std")]
use sr_primitives::{DigestItem, generic::OpaqueDigestItemId};
#[cfg(feature = "std")]
use std::fmt::Debug;
use codec::{Decode, Encode};
#[cfg(feature = "std")]
use codec::{Codec, Input, Error};
#[cfg(feature = "std")]
use schnorrkel::{
	SignatureError, errors::MultiSignatureStage,
	vrf::{VRFProof, VRFOutput, VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH}
};
use rstd::vec::Vec;


/// A BABE pre-runtime digest. This contains all data required to validate a
/// block and for the BABE runtime module. Slots can be assigned to a primary
/// (VRF based) and to a secondary (slot number based).
#[cfg(feature = "std")]
#[derive(Clone, Debug)]
pub enum BabePreDigest {
	/// A primary VRF-based slot assignment.
	Primary {
		/// VRF output
		vrf_output: VRFOutput,
		/// VRF proof
		vrf_proof: VRFProof,
		/// Authority index
		authority_index: super::AuthorityIndex,
		/// Slot number
		slot_number: SlotNumber,
	},
	/// A secondary deterministic slot assignment.
	Secondary {
		/// Authority index
		authority_index: super::AuthorityIndex,
		/// Slot number
		slot_number: SlotNumber,
	},
}

#[cfg(feature = "std")]
impl BabePreDigest {
	/// Returns the slot number of the pre digest.
	pub fn authority_index(&self) -> AuthorityIndex {
		match self {
			BabePreDigest::Primary { authority_index, .. } => *authority_index,
			BabePreDigest::Secondary { authority_index, .. } => *authority_index,
		}
	}

	/// Returns the slot number of the pre digest.
	pub fn slot_number(&self) -> SlotNumber {
		match self {
			BabePreDigest::Primary { slot_number, .. } => *slot_number,
			BabePreDigest::Secondary { slot_number, .. } => *slot_number,
		}
	}

	/// Returns the weight _added_ by this digest, not the cumulative weight
	/// of the chain.
	pub fn added_weight(&self) -> crate::BabeBlockWeight {
		match self {
			BabePreDigest::Primary { .. } => 1,
			BabePreDigest::Secondary { .. } => 0,
		}
	}
}

/// The prefix used by BABE for its VRF keys.
pub const BABE_VRF_PREFIX: &'static [u8] = b"substrate-babe-vrf";

/// A raw version of `BabePreDigest`, usable on `no_std`.
#[derive(Copy, Clone, Encode, Decode)]
pub enum RawBabePreDigest {
	/// A primary VRF-based slot assignment.
	#[codec(index = "1")]
	Primary {
		/// Authority index
		authority_index: AuthorityIndex,
		/// Slot number
		slot_number: SlotNumber,
		/// VRF output
		vrf_output: [u8; VRF_OUTPUT_LENGTH],
		/// VRF proof
		vrf_proof: [u8; VRF_PROOF_LENGTH],
	},
	/// A secondary deterministic slot assignment.
	#[codec(index = "2")]
	Secondary {
		/// Authority index
		///
		/// This is not strictly-speaking necessary, since the secondary slots
		/// are assigned based on slot number and epoch randomness. But including
		/// it makes things easier for higher-level users of the chain data to
		/// be aware of the author of a secondary-slot block.
		authority_index: AuthorityIndex,
		/// Slot number
		slot_number: SlotNumber,
	},
}

impl RawBabePreDigest {
	/// Returns the slot number of the pre digest.
	pub fn slot_number(&self) -> SlotNumber {
		match self {
			RawBabePreDigest::Primary { slot_number, .. } => *slot_number,
			RawBabePreDigest::Secondary { slot_number, .. } => *slot_number,
		}
	}
}

#[cfg(feature = "std")]
impl Encode for BabePreDigest {
	fn encode(&self) -> Vec<u8> {
		let raw = match self {
			BabePreDigest::Primary {
				vrf_output,
				vrf_proof,
				authority_index,
				slot_number,
			} => {
				RawBabePreDigest::Primary {
					vrf_output: *vrf_output.as_bytes(),
					vrf_proof: vrf_proof.to_bytes(),
					authority_index: *authority_index,
					slot_number: *slot_number,
				}
			},
			BabePreDigest::Secondary {
				authority_index,
				slot_number,
			} => {
				RawBabePreDigest::Secondary {
					authority_index: *authority_index,
					slot_number: *slot_number,
				}
			},
		};

		codec::Encode::encode(&raw)
	}
}

#[cfg(feature = "std")]
impl codec::EncodeLike for BabePreDigest {}

#[cfg(feature = "std")]
impl Decode for BabePreDigest {
	fn decode<R: Input>(i: &mut R) -> Result<Self, Error> {
		let pre_digest = match Decode::decode(i)? {
			RawBabePreDigest::Primary { vrf_output, vrf_proof, authority_index, slot_number } => {
				// Verify (at compile time) that the sizes in babe_primitives are correct
				let _: [u8; super::VRF_OUTPUT_LENGTH] = vrf_output;
				let _: [u8; super::VRF_PROOF_LENGTH] = vrf_proof;

				BabePreDigest::Primary {
					vrf_proof: VRFProof::from_bytes(&vrf_proof).map_err(convert_error)?,
					vrf_output: VRFOutput::from_bytes(&vrf_output).map_err(convert_error)?,
					authority_index,
					slot_number,
				}
			},
			RawBabePreDigest::Secondary { authority_index, slot_number } => {
				BabePreDigest::Secondary { authority_index, slot_number }
			},
		};

		Ok(pre_digest)
	}
}

/// Information about the next epoch. This is broadcast in the first block
/// of the epoch.
#[derive(Decode, Encode, Default, PartialEq, Eq, Clone)]
#[cfg_attr(any(feature = "std", test), derive(Debug))]
pub struct NextEpochDescriptor {
	/// The authorities.
	pub authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,

	/// The value of randomness to use for the slot-assignment.
	pub randomness: [u8; VRF_OUTPUT_LENGTH],
}

/// A digest item which is usable with BABE consensus.
#[cfg(feature = "std")]
pub trait CompatibleDigestItem: Sized {
	/// Construct a digest item which contains a BABE pre-digest.
	fn babe_pre_digest(seal: BabePreDigest) -> Self;

	/// If this item is an BABE pre-digest, return it.
	fn as_babe_pre_digest(&self) -> Option<BabePreDigest>;

	/// Construct a digest item which contains a BABE seal.
	fn babe_seal(signature: AuthoritySignature) -> Self;

	/// If this item is a BABE signature, return the signature.
	fn as_babe_seal(&self) -> Option<AuthoritySignature>;

	/// If this item is a BABE epoch, return it.
	fn as_next_epoch_descriptor(&self) -> Option<NextEpochDescriptor>;
}

#[cfg(feature = "std")]
impl<Hash> CompatibleDigestItem for DigestItem<Hash> where
	Hash: Debug + Send + Sync + Eq + Clone + Codec + 'static
{
	fn babe_pre_digest(digest: BabePreDigest) -> Self {
		DigestItem::PreRuntime(BABE_ENGINE_ID, digest.encode())
	}

	fn as_babe_pre_digest(&self) -> Option<BabePreDigest> {
		self.try_to(OpaqueDigestItemId::PreRuntime(&BABE_ENGINE_ID))
	}

	fn babe_seal(signature: AuthoritySignature) -> Self {
		DigestItem::Seal(BABE_ENGINE_ID, signature.encode())
	}

	fn as_babe_seal(&self) -> Option<AuthoritySignature> {
		self.try_to(OpaqueDigestItemId::Seal(&BABE_ENGINE_ID))
	}

	fn as_next_epoch_descriptor(&self) -> Option<NextEpochDescriptor> {
		self.try_to(OpaqueDigestItemId::Consensus(&BABE_ENGINE_ID))
			.and_then(|x: super::ConsensusLog| match x {
				super::ConsensusLog::NextEpochData(n) => Some(n),
				_ => None,
			})
	}
}

#[cfg(feature = "std")]
fn convert_error(e: SignatureError) -> codec::Error {
	use SignatureError::*;
	use MultiSignatureStage::*;
	match e {
		EquationFalse => "Signature error: `EquationFalse`".into(),
		PointDecompressionError => "Signature error: `PointDecompressionError`".into(),
		ScalarFormatError => "Signature error: `ScalarFormatError`".into(),
		NotMarkedSchnorrkel => "Signature error: `NotMarkedSchnorrkel`".into(),
		BytesLengthError { .. } => "Signature error: `BytesLengthError`".into(),
		MuSigAbsent { musig_stage: Commitment } =>
			"Signature error: `MuSigAbsent` at stage `Commitment`".into(),
		MuSigAbsent { musig_stage: Reveal } =>
			"Signature error: `MuSigAbsent` at stage `Reveal`".into(),
		MuSigAbsent { musig_stage: Cosignature } =>
			"Signature error: `MuSigAbsent` at stage `Commitment`".into(),
		MuSigInconsistent { musig_stage: Commitment, duplicate: true } =>
			"Signature error: `MuSigInconsistent` at stage `Commitment` on duplicate".into(),
		MuSigInconsistent { musig_stage: Commitment, duplicate: false } =>
			"Signature error: `MuSigInconsistent` at stage `Commitment` on not duplicate".into(),
		MuSigInconsistent { musig_stage: Reveal, duplicate: true } =>
			"Signature error: `MuSigInconsistent` at stage `Reveal` on duplicate".into(),
		MuSigInconsistent { musig_stage: Reveal, duplicate: false } =>
			"Signature error: `MuSigInconsistent` at stage `Reveal` on not duplicate".into(),
		MuSigInconsistent { musig_stage: Cosignature, duplicate: true } =>
			"Signature error: `MuSigInconsistent` at stage `Cosignature` on duplicate".into(),
		MuSigInconsistent { musig_stage: Cosignature, duplicate: false } =>
			"Signature error: `MuSigInconsistent` at stage `Cosignature` on not duplicate".into(),
	}
}
