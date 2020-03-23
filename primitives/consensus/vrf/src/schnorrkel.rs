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

use codec::{Encode, Decode};
use sp_core::U512;
use sp_runtime::RuntimeDebug;
use sp_std::ops::{Deref, DerefMut};
#[cfg(feature = "std")]
use std::convert::TryFrom;
#[cfg(feature = "std")]
use codec::EncodeLike;
#[cfg(feature = "std")]
use schnorrkel::errors::MultiSignatureStage;

#[cfg(feature = "std")]
pub use schnorrkel::{SignatureError, vrf::{VRF_PROOF_LENGTH, VRF_OUTPUT_LENGTH}};

/// The length of the VRF proof.
#[cfg(not(feature = "std"))]
pub const VRF_PROOF_LENGTH: usize = 64;

/// The length of the VRF output.
#[cfg(not(feature = "std"))]
pub const VRF_OUTPUT_LENGTH: usize = 32;

/// The length of the Randomness.
pub const RANDOMNESS_LENGTH: usize = VRF_OUTPUT_LENGTH;

/// Raw VRF output.
#[derive(Clone, Copy, Eq, PartialEq, RuntimeDebug, Encode, Decode)]
pub struct RawVRFOutput(pub [u8; VRF_OUTPUT_LENGTH]);

impl Deref for RawVRFOutput {
	type Target = [u8; VRF_OUTPUT_LENGTH];
	fn deref(&self) -> &Self::Target { &self.0 }
}

impl DerefMut for RawVRFOutput {
	fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

/// VRF output type available for `std` environment, suitable for schnorrkel operations.
#[cfg(feature = "std")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VRFOutput(pub schnorrkel::vrf::VRFOutput);

#[cfg(feature = "std")]
impl Deref for VRFOutput {
	type Target = schnorrkel::vrf::VRFOutput;
	fn deref(&self) -> &Self::Target { &self.0 }
}

#[cfg(feature = "std")]
impl DerefMut for VRFOutput {
	fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

#[cfg(feature = "std")]
impl Encode for VRFOutput {
	fn encode(&self) -> Vec<u8> {
		self.0.as_bytes().encode()
	}
}

#[cfg(feature = "std")]
impl EncodeLike for VRFOutput { }

#[cfg(feature = "std")]
impl Decode for VRFOutput {
	fn decode<R: codec::Input>(i: &mut R) -> Result<Self, codec::Error> {
		let decoded = <[u8; VRF_OUTPUT_LENGTH]>::decode(i)?;
		Ok(Self(schnorrkel::vrf::VRFOutput::from_bytes(&decoded).map_err(convert_error)?))
	}
}

#[cfg(feature = "std")]
impl TryFrom<[u8; VRF_OUTPUT_LENGTH]> for VRFOutput {
	type Error = SignatureError;

	fn try_from(raw: [u8; VRF_OUTPUT_LENGTH]) -> Result<Self, Self::Error> {
		schnorrkel::vrf::VRFOutput::from_bytes(&raw).map(VRFOutput)
	}
}

#[cfg(feature = "std")]
impl TryFrom<RawVRFOutput> for VRFOutput {
	type Error = SignatureError;

	fn try_from(raw: RawVRFOutput) -> Result<VRFOutput, Self::Error> {
		schnorrkel::vrf::VRFOutput::from_bytes(&raw.0).map(VRFOutput)
	}
}

#[cfg(feature = "std")]
impl From<VRFOutput> for RawVRFOutput {
	fn from(output: VRFOutput) -> RawVRFOutput {
		RawVRFOutput(output.to_bytes())
	}
}

/// Raw VRF proof.
#[derive(Clone, Copy, Encode, Decode)]
pub struct RawVRFProof(pub [u8; VRF_PROOF_LENGTH]);

impl Deref for RawVRFProof {
	type Target = [u8; VRF_PROOF_LENGTH];
	fn deref(&self) -> &Self::Target { &self.0 }
}

impl DerefMut for RawVRFProof {
	fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

#[cfg(feature = "std")]
impl std::fmt::Debug for RawVRFProof {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{:?}", &self)
	}
}

impl core::cmp::PartialEq for RawVRFProof {
	fn eq(&self, other: &Self) -> bool {
		self == other
	}
}

impl core::cmp::Eq for RawVRFProof { }

/// VRF proof type available for `std` environment, suitable for schnorrkel operations.
#[cfg(feature = "std")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VRFProof(pub schnorrkel::vrf::VRFProof);

#[cfg(feature = "std")]
impl PartialOrd for VRFProof {
	fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
		Some(self.cmp(other))
	}
}

#[cfg(feature = "std")]
impl Ord for VRFProof {
	fn cmp(&self, other: &Self) -> core::cmp::Ordering {
		U512::from(self.0.to_bytes()).cmp(&U512::from(other.0.to_bytes()))
	}
}

#[cfg(feature = "std")]
impl Deref for VRFProof {
	type Target = schnorrkel::vrf::VRFProof;
	fn deref(&self) -> &Self::Target { &self.0 }
}

#[cfg(feature = "std")]
impl DerefMut for VRFProof {
	fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

#[cfg(feature = "std")]
impl Encode for VRFProof {
	fn encode(&self) -> Vec<u8> {
		self.0.to_bytes().encode()
	}
}

#[cfg(feature = "std")]
impl EncodeLike for VRFProof { }

#[cfg(feature = "std")]
impl Decode for VRFProof {
	fn decode<R: codec::Input>(i: &mut R) -> Result<Self, codec::Error> {
		let decoded = <[u8; VRF_PROOF_LENGTH]>::decode(i)?;
		Ok(Self(schnorrkel::vrf::VRFProof::from_bytes(&decoded).map_err(convert_error)?))
	}
}

#[cfg(feature = "std")]
impl TryFrom<[u8; VRF_PROOF_LENGTH]> for VRFProof {
	type Error = SignatureError;

	fn try_from(raw: [u8; VRF_PROOF_LENGTH]) -> Result<Self, Self::Error> {
		schnorrkel::vrf::VRFProof::from_bytes(&raw).map(VRFProof)
	}
}

#[cfg(feature = "std")]
impl TryFrom<RawVRFProof> for VRFProof {
	type Error = SignatureError;

	fn try_from(raw: RawVRFProof) -> Result<VRFProof, Self::Error> {
		schnorrkel::vrf::VRFProof::from_bytes(&raw.0).map(VRFProof)
	}
}

#[cfg(feature = "std")]
impl From<VRFProof> for RawVRFProof {
	fn from(output: VRFProof) -> RawVRFProof {
		RawVRFProof(output.to_bytes())
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

/// Schnorrkel randomness value. Same size as `VRFOutput`.
pub type Randomness = [u8; RANDOMNESS_LENGTH];
