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
use super::AuthoritySignature;
#[cfg(feature = "std")]
use super::{BABE_ENGINE_ID, Epoch};
#[cfg(not(feature = "std"))]
use super::{VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH};
use super::{AuthorityIndex, BabeBlockWeight, SlotNumber};
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

/// A BABE pre-digest
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
		/// Chain weight (measured in number of Primary blocks)
		weight: BabeBlockWeight,
	},
	/// A secondary deterministic slot assignmnet.
	Secondary {
		/// Authority index
		authority_index: super::AuthorityIndex,
		/// Slot number
		slot_number: SlotNumber,
		/// Chain weight (measured in number of Primary blocks)
		weight: BabeBlockWeight,
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

	/// Returns the weight of the pre digest.
	pub fn weight(&self) -> BabeBlockWeight {
		match self {
			BabePreDigest::Primary { weight, .. } => *weight,
			BabePreDigest::Secondary { weight, .. } => *weight,
		}
	}
}

/// The prefix used by BABE for its VRF keys.
pub const BABE_VRF_PREFIX: &'static [u8] = b"substrate-babe-vrf";

/// A raw version of `BabePreDigest`, usable on `no_std`.
#[derive(Copy, Clone, Encode, Decode)]
pub enum RawBabePreDigest {
	/// A primary VRF-based slot assignment.
	Primary {
		/// Authority index
		authority_index: AuthorityIndex,
		/// Slot number
		slot_number: SlotNumber,
		/// Chain weight (measured in number of Primary blocks)
		weight: BabeBlockWeight,
		/// VRF output
		vrf_output: [u8; VRF_OUTPUT_LENGTH],
		/// VRF proof
		vrf_proof: [u8; VRF_PROOF_LENGTH],
	},
	/// A secondary deterministic slot assignmnet.
	Secondary {
		/// Authority index
		authority_index: AuthorityIndex,
		/// Slot number
		slot_number: SlotNumber,
		/// Chain weight (measured in number of Primary blocks)
		weight: BabeBlockWeight,
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
				weight,
			} => {
				RawBabePreDigest::Primary {
					vrf_output: *vrf_output.as_bytes(),
					vrf_proof: vrf_proof.to_bytes(),
					authority_index: *authority_index,
					slot_number: *slot_number,
					weight: *weight,
				}
			},
			BabePreDigest::Secondary {
				authority_index,
				slot_number,
				weight,
			} => {
				RawBabePreDigest::Secondary {
					authority_index: *authority_index,
					slot_number: *slot_number,
					weight: *weight,
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
			RawBabePreDigest::Primary { vrf_output, vrf_proof, authority_index, slot_number, weight } => {
				// Verify (at compile time) that the sizes in babe_primitives are correct
				let _: [u8; super::VRF_OUTPUT_LENGTH] = vrf_output;
				let _: [u8; super::VRF_PROOF_LENGTH] = vrf_proof;

				BabePreDigest::Primary {
					vrf_proof: VRFProof::from_bytes(&vrf_proof).map_err(convert_error)?,
					vrf_output: VRFOutput::from_bytes(&vrf_output).map_err(convert_error)?,
					authority_index,
					slot_number,
					weight,
				}
			},
			RawBabePreDigest::Secondary { authority_index, slot_number, weight } => {
				BabePreDigest::Secondary { authority_index, slot_number, weight }
			},
		};

		Ok(pre_digest)
	}
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
	fn as_babe_epoch(&self) -> Option<Epoch>;
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

	fn as_babe_epoch(&self) -> Option<Epoch> {
		self.try_to(OpaqueDigestItemId::Consensus(&BABE_ENGINE_ID))
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
