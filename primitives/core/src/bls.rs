// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

//! Substrate BLS signature verification

#[cfg(feature = "full_crypto")]
use ark_std::io::Cursor;

#[cfg(feature = "full_crypto")]
use ark_bls12_381::{
	g1::Parameters as G1Parameters, g2::Parameters as G2Parameters, Bls12_381, G1Affine, G2Affine,
};
#[cfg(feature = "full_crypto")]
use ark_ec::{
	hashing::{curve_maps::wb::WBMap, map_to_curve_hasher::MapToCurveBasedHasher, HashToCurve},
	pairing::Pairing,
	short_weierstrass::{Projective, SWCurveConfig},
};
#[cfg(feature = "full_crypto")]
use ark_ff::field_hashers::DefaultFieldHasher;
#[cfg(feature = "full_crypto")]
use ark_serialize::{CanonicalDeserialize, Compress, Validate};
#[cfg(feature = "full_crypto")]
use ark_std::fmt;
#[cfg(feature = "full_crypto")]
use sha2::Sha256;

/// As per README in: https://github.com/ethereum/bls12-381-tests
const DOMAIN: &[u8] = b"BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";

/// Verify a BLS `signature` on `message` against a `public_key`.
/// Returns an error if either signature of PK couldn't be deserialized.
/// Otherwise returns an Ok(result), which is true only if `signature` is valid.
/// Note that subgroup checks are NOT performed during deserialization.
pub fn bls_verify(
	signature: &[u8],
	message: &[u8],
	public_key: &[u8],
) -> Result<bool, SerializationError> {
	let g1 = G1Parameters::GENERATOR;

	let r: G2Affine = g2_from_vec(signature)?;

	let pk: G1Affine = g1_from_vec(public_key)?;
	// hash the message to G2
	let g2_mapper = MapToCurveBasedHasher::<
		Projective<G2Parameters>,
		DefaultFieldHasher<Sha256, 128>,
		WBMap<G2Parameters>,
	>::new(DOMAIN)
	.unwrap();
	let q = g2_mapper.hash(message).unwrap();

	// check the pairing
	let c1 = Bls12_381::pairing(pk, q);
	let c2 = Bls12_381::pairing(g1, r);
	Ok(c1 == c2)
}

/// This is an error that could occur during serialization.
#[derive(Debug)]
pub enum SerializationError {
	/// The supplied signature couldn't be deserialized.
	InvalidSignature,
	/// The supplied public key couldn't be deserialized.
	InvalidPK,
}

impl fmt::Display for SerializationError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
		match self {
			SerializationError::InvalidSignature =>
				write!(f, "The signature failed to deserialize into a G2Affine point!"),
			SerializationError::InvalidPK =>
				write!(f, "The public key failed to deserialize into a G1Affine point!"),
		}
	}
}

impl ark_std::error::Error for SerializationError {}

#[cfg(feature = "full_crypto")]
fn g2_from_vec(vec: &[u8]) -> Result<G2Affine, SerializationError> {
	let serialized: [u8; 96] = vec.try_into().unwrap();
	let mut cursor = Cursor::new(&serialized[..]);
	G2Affine::deserialize_with_mode(&mut cursor, Compress::Yes, Validate::Yes)
		.map_err(|_| SerializationError::InvalidSignature)
}

#[cfg(feature = "full_crypto")]
fn g1_from_vec(vec: &[u8]) -> Result<G1Affine, SerializationError> {
	let serialized: [u8; 48] = vec.try_into().unwrap();
	let mut cursor = Cursor::new(&serialized[..]);
	G1Affine::deserialize_with_mode(&mut cursor, Compress::Yes, Validate::Yes)
		.map_err(|_| SerializationError::InvalidPK)
}

#[cfg(test)]
mod tests {
	use super::*;
	use hex_literal::hex;

	#[test]
	fn test_eth_signature() {
		// example from verify_valid_case_195246ee3bd3b6ec.json from https://github.com/ethereum/bls12-381-tests/releases/tag/v0.1.1
		let pk_bytes: [u8; 48] = hex!("b53d21a4cfd562c469cc81514d4ce5a6b577d8403d32a394dc265dd190b47fa9f829fdd7963afdf972e5e77854051f6f");
		let message: [u8; 32] =
			hex!("abababababababababababababababababababababababababababababababab");
		let signature: [u8; 96] = hex!("ae82747ddeefe4fd64cf9cedb9b04ae3e8a43420cd255e3c7cd06a8d88b7c7f8638543719981c5d16fa3527c468c25f0026704a6951bde891360c7e8d12ddee0559004ccdbe6046b55bae1b257ee97f7cdb955773d7cf29adf3ccbb9975e4eb9");

		let result = bls_verify(&signature, &message, &pk_bytes).unwrap();

		assert!(result);
	}
}
