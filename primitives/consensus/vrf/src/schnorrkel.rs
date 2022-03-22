// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Schnorrkel-based VRF.

use codec::{Decode, Encode, EncodeLike};
use schnorrkel::errors::MultiSignatureStage;
use sp_core::U512;
use sp_std::{
	convert::TryFrom,
	ops::{Deref, DerefMut},
	prelude::*,
};

pub use schnorrkel::{
	vrf::{VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH},
	PublicKey, SignatureError,
};

/// The length of the Randomness.
pub const RANDOMNESS_LENGTH: usize = VRF_OUTPUT_LENGTH;

/// VRF output type available for `std` environment, suitable for schnorrkel operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VRFOutput(pub schnorrkel::vrf::VRFOutput);

impl Deref for VRFOutput {
	type Target = schnorrkel::vrf::VRFOutput;
	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl DerefMut for VRFOutput {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl Encode for VRFOutput {
	fn encode(&self) -> Vec<u8> {
		self.0.as_bytes().encode()
	}
}

impl EncodeLike for VRFOutput {}

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
	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl DerefMut for VRFProof {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl Encode for VRFProof {
	fn encode(&self) -> Vec<u8> {
		self.0.to_bytes().encode()
	}
}

impl EncodeLike for VRFProof {}

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
	use MultiSignatureStage::*;
	use SignatureError::*;
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
