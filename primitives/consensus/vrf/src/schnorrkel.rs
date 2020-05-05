// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Schnorrkel-based VRF.

use codec::{Encode, Decode, EncodeLike};
use sp_std::{convert::TryFrom, prelude::*};
use sp_core::U512;
use sp_std::ops::{Deref, DerefMut};
use schnorrkel::errors::MultiSignatureStage;

pub use schnorrkel::{SignatureError, PublicKey, vrf::{VRF_PROOF_LENGTH, VRF_OUTPUT_LENGTH}};

/// The length of the Randomness.
pub const RANDOMNESS_LENGTH: usize = VRF_OUTPUT_LENGTH;

/// VRF output type available for `std` environment, suitable for schnorrkel operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VRFOutput(pub schnorrkel::vrf::VRFOutput);

impl Deref for VRFOutput {
	type Target = schnorrkel::vrf::VRFOutput;
	fn deref(&self) -> &Self::Target { &self.0 }
}

impl DerefMut for VRFOutput {
	fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl Encode for VRFOutput {
	fn encode(&self) -> Vec<u8> {
		self.0.as_bytes().encode()
	}
}

impl EncodeLike for VRFOutput { }

impl Decode for VRFOutput {
	fn decode<R: codec::Input>(i: &mut R) -> Result<Self, codec::Error> {
		let decoded = <[u8; VRF_OUTPUT_LENGTH]>::decode(i)?;
		Ok(Self(schnorrkel::vrf::VRFOutput::from_bytes(&decoded).map_err(convert_error)?))
	}
}

impl TryFrom<[u8; VRF_OUTPUT_LENGTH]> for VRFOutput {
	type Error = SignatureError;

	fn try_from(raw: [u8; VRF_OUTPUT_LENGTH]) -> Result<Self, Self::Error> {
		schnorrkel::vrf::VRFOutput::from_bytes(&raw).map(VRFOutput)
	}
}

/// VRF proof type available for `std` environment, suitable for schnorrkel operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VRFProof(pub schnorrkel::vrf::VRFProof);

impl PartialOrd for VRFProof {
	fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl Ord for VRFProof {
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		U512::from(self.0.to_bytes()).cmp(&U512::from(other.0.to_bytes()))
	}
}

impl Deref for VRFProof {
	type Target = schnorrkel::vrf::VRFProof;
	fn deref(&self) -> &Self::Target { &self.0 }
}

impl DerefMut for VRFProof {
	fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl Encode for VRFProof {
	fn encode(&self) -> Vec<u8> {
		self.0.to_bytes().encode()
	}
}

impl EncodeLike for VRFProof { }

impl Decode for VRFProof {
	fn decode<R: codec::Input>(i: &mut R) -> Result<Self, codec::Error> {
		let decoded = <[u8; VRF_PROOF_LENGTH]>::decode(i)?;
		Ok(Self(schnorrkel::vrf::VRFProof::from_bytes(&decoded).map_err(convert_error)?))
	}
}

impl TryFrom<[u8; VRF_PROOF_LENGTH]> for VRFProof {
	type Error = SignatureError;

	fn try_from(raw: [u8; VRF_PROOF_LENGTH]) -> Result<Self, Self::Error> {
		schnorrkel::vrf::VRFProof::from_bytes(&raw).map(VRFProof)
	}
}

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

/// Schnorrkel randomness value. Same size as `VRFOutput`.
pub type Randomness = [u8; RANDOMNESS_LENGTH];
