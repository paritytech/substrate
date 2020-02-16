use core::convert::TryFrom;
use codec::{Encode, Decode, EncodeLike};
use schnorrkel::{SignatureError, errors::MultiSignatureStage};
use sp_std::ops::{Deref, DerefMut};
use sp_runtime::RuntimeDebug;

pub use schnorrkel::vrf::{VRF_PROOF_LENGTH, VRF_OUTPUT_LENGTH};

#[derive(Clone, Eq, PartialEq, RuntimeDebug, Encode, Decode)]
pub struct RawVRFOutput(pub [u8; VRF_OUTPUT_LENGTH]);

#[cfg(feature = "std")]
#[derive(Clone, Debug)]
pub struct VRFOutput(pub schnorrkel::vrf::VRFOutput);

#[cfg(not(feature = "std"))]
pub type VRFOutput = RawVRFOutput;

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

#[derive(Clone, Encode, Decode)]
pub struct RawVRFProof(pub [u8; VRF_PROOF_LENGTH]);

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

#[cfg(feature = "std")]
#[derive(Clone, Debug)]
pub struct VRFProof(pub schnorrkel::vrf::VRFProof);

#[cfg(not(feature = "std"))]
pub type VRFProof = RawVRFProof;

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

pub type Randomness = [u8; VRF_OUTPUT_LENGTH];
