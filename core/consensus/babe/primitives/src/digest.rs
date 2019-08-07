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

use super::{BABE_ENGINE_ID, Epoch};
#[cfg(not(feature = "std"))]
use super::{VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH};
use super::SlotNumber;
use sr_primitives::{DigestItem, generic::OpaqueDigestItemId};
use sr_primitives::traits::{Header, DigestItemForHeader, Verify};
use codec::{Decode, Encode, Codec};
#[cfg(feature = "std")]
use codec::{Input, Error};
#[cfg(feature = "std")]
use schnorrkel::{
	SignatureError, errors::MultiSignatureStage,
	vrf::{VRFProof, VRFOutput, VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH}
};

/// A BABE pre-digest
#[cfg(feature = "std")]
#[derive(Clone, Debug)]
pub struct BabePreDigest {
	/// VRF output
	pub vrf_output: VRFOutput,
	/// VRF proof
	pub vrf_proof: VRFProof,
	/// Authority index
	pub authority_index: super::AuthorityIndex,
	/// Slot number
	pub slot_number: SlotNumber,
}

/// Get the slot.
pub fn get_slot<H: Header>(header: &H) -> Result<SlotNumber, &str>
	where DigestItemForHeader<H>: CompatibleDigestItem,
{
	find_pre_digest::<H, RawBabePreDigest>(header)
		.map(|raw_pre_digest| raw_pre_digest.slot_number)
}

/// Extract the BABE pre digest from the given header. Pre-runtime digests are
/// mandatory, the function will return `Err` if none is found.
pub fn find_pre_digest<H: Header, D: Codec>(header: &H) -> Result<D, &str>
	where DigestItemForHeader<H>: CompatibleDigestItem,
{
	let mut pre_digest: Option<_> = None;
	for log in header.digest().logs() {
		match (log.as_babe_pre_digest(), pre_digest.is_some()) {
			(Some(_), true) => Err("Multiple BABE pre-runtime digests, rejecting!")?,
			(None, _) => {},
			(s, false) => pre_digest = s,
		}
	}
	pre_digest.ok_or_else(|| "No BABE pre-runtime digest found")
}

/// The prefix used by BABE for its VRF keys.
pub const BABE_VRF_PREFIX: &'static [u8] = b"substrate-babe-vrf";

/// A raw version of `BabePreDigest`, usable on `no_std`.
#[derive(Copy, Clone, Encode, Decode)]
pub struct RawBabePreDigest {
	/// Slot number
	pub slot_number: SlotNumber,
	/// Authority index
	pub authority_index: super::AuthorityIndex,
	/// VRF output
	pub vrf_output: [u8; VRF_OUTPUT_LENGTH],
	/// VRF proof
	pub vrf_proof: [u8; VRF_PROOF_LENGTH],
}

#[cfg(feature = "std")]
impl Encode for BabePreDigest {
	fn encode(&self) -> Vec<u8> {
		let tmp =  RawBabePreDigest {
			vrf_output: *self.vrf_output.as_bytes(),
			vrf_proof: self.vrf_proof.to_bytes(),
			authority_index: self.authority_index,
			slot_number: self.slot_number,
		};
		codec::Encode::encode(&tmp)
	}
}

#[cfg(feature = "std")]
impl codec::EncodeLike for BabePreDigest {}

#[cfg(feature = "std")]
impl Decode for BabePreDigest {
	fn decode<R: Input>(i: &mut R) -> Result<Self, Error> {
		let RawBabePreDigest { vrf_output, vrf_proof, authority_index, slot_number } = Decode::decode(i)?;

		// Verify (at compile time) that the sizes in babe_primitives are correct
		let _: [u8; super::VRF_OUTPUT_LENGTH] = vrf_output;
		let _: [u8; super::VRF_PROOF_LENGTH] = vrf_proof;
		Ok(BabePreDigest {
			vrf_proof: VRFProof::from_bytes(&vrf_proof)
				.map_err(convert_error)?,
			vrf_output: VRFOutput::from_bytes(&vrf_output)
				.map_err(convert_error)?,
			authority_index,
			slot_number,
		})
	}
}

/// A digest item which is usable with BABE consensus.
// #[cfg(feature = "std")]
pub trait CompatibleDigestItem: Sized {
	/// Construct a digest item which contains a BABE pre-digest.
	fn babe_pre_digest<D: Codec>(seal: D) -> Self;

	/// If this item is an BABE pre-digest, return it.
	fn as_babe_pre_digest<D: Codec>(&self) -> Option<D>;

	/// Construct a digest item which contains a BABE seal.
	fn babe_seal<S: Codec + Verify>(signature: S) -> Self;

	/// If this item is a BABE signature, return the signature.
	fn as_babe_seal<S: Codec + Verify>(&self) -> Option<S>;

	/// If this item is a BABE epoch, return it.
	fn as_babe_epoch(&self) -> Option<Epoch>;
}

impl<Hash> CompatibleDigestItem for DigestItem<Hash> where
	Hash: Send + Sync + Eq + Clone + Codec + 'static
{
	fn babe_pre_digest<D: Codec>(digest: D) -> Self {
		DigestItem::PreRuntime(BABE_ENGINE_ID, digest.encode())
	}

	fn as_babe_pre_digest<D: Codec>(&self) -> Option<D> {
		self.try_to(OpaqueDigestItemId::PreRuntime(&BABE_ENGINE_ID))
	}

	fn babe_seal<S: Verify + Codec>(signature: S) -> Self {
		DigestItem::Seal(BABE_ENGINE_ID, signature.encode())
	}

	fn as_babe_seal<S: Verify + Codec>(&self) -> Option<S> {
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
