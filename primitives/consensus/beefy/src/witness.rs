// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Primitives for light, 2-phase interactive verification protocol.
//!
//! Instead of submitting full list of signatures, it's possible to submit first a witness
//! form of [SignedCommitment].
//! This can later be verified by the client requesting only some (out of all) signatures for
//! verification. This allows lowering the data and computation cost of verifying the
//! signed commitment.

use sp_std::prelude::*;

use crate::commitment::{Commitment, SignedCommitment};

/// A light form of [SignedCommitment].
///
/// This is a light ("witness") form of the signed commitment. Instead of containing full list of
/// signatures, which might be heavy and expensive to verify, it only contains a bit vector of
/// validators which signed the original [SignedCommitment] and a merkle root of all signatures.
///
/// This can be used by light clients for 2-phase interactive verification (for instance for
/// Ethereum Mainnet), in a commit-reveal like scheme, where first we submit only the signed
/// commitment witness and later on, the client picks only some signatures to verify at random.
#[derive(Debug, PartialEq, Eq, codec::Encode, codec::Decode)]
pub struct SignedCommitmentWitness<TBlockNumber, TSignatureAccumulator> {
	/// The full content of the commitment.
	pub commitment: Commitment<TBlockNumber>,

	/// The bit vector of validators who signed the commitment.
	pub signed_by: Vec<bool>, // TODO [ToDr] Consider replacing with bitvec crate

	/// Either a merkle root of signatures in the original signed commitment or a single aggregated
	/// BLS signature aggregating all original signatures.
	pub signature_accumulator: TSignatureAccumulator,
}

impl<TBlockNumber, TSignatureAccumulator>
	SignedCommitmentWitness<TBlockNumber, TSignatureAccumulator>
{
	/// Convert [SignedCommitment] into [SignedCommitmentWitness].
	///
	/// This takes a [SignedCommitment], which contains full signatures
	/// and converts it into a witness form, which does not contain full signatures,
	/// only a bit vector indicating which validators have signed the original [SignedCommitment]
	/// and a merkle root of all signatures.
	///
	/// Returns the full list of signatures along with the witness.
	pub fn from_signed<TSignatureAggregator, TSignature>(
		signed: SignedCommitment<TBlockNumber, TSignature>,
		aggregator: TSignatureAggregator,
	) -> (Self, Vec<Option<TSignature>>)
	where
		TSignatureAggregator: FnOnce(&[Option<TSignature>]) -> TSignatureAccumulator,
	{
		let SignedCommitment { commitment, signatures } = signed;
		let signed_by = signatures.iter().map(|s| s.is_some()).collect();
		let signature_accumulator = aggregator(&signatures);

		(Self { commitment, signed_by, signature_accumulator }, signatures)
	}
}

#[cfg(test)]
mod tests {
	use sp_core::{keccak_256, Pair};

	use super::*;
	use codec::Decode;

	use crate::{ecdsa_crypto::Signature as EcdsaSignature, known_payloads, Payload};

	#[cfg(feature = "bls-experimental")]
	use crate::bls_crypto::Signature as BlsSignature;

	#[cfg(feature = "bls-experimental")]
	use w3f_bls::{
		single_pop_aggregator::SignatureAggregatorAssumingPoP, Message, SerializableToBytes,
		Signed, TinyBLS377,
	};

	type TestCommitment = Commitment<u128>;

	// Types for ecdsa signed commitment.
	type TestEcdsaSignedCommitment = SignedCommitment<u128, EcdsaSignature>;
	type TestEcdsaSignedCommitmentWitness =
		SignedCommitmentWitness<u128, Vec<Option<EcdsaSignature>>>;

	#[cfg(feature = "bls-experimental")]
	#[derive(Clone, Debug, PartialEq, codec::Encode, codec::Decode)]
	struct EcdsaBlsSignaturePair(EcdsaSignature, BlsSignature);

	// types for commitment containing  bls signature along side ecdsa signature
	#[cfg(feature = "bls-experimental")]
	type TestBlsSignedCommitment = SignedCommitment<u128, EcdsaBlsSignaturePair>;
	#[cfg(feature = "bls-experimental")]
	type TestBlsSignedCommitmentWitness = SignedCommitmentWitness<u128, Vec<u8>>;

	// The mock signatures are equivalent to the ones produced by the BEEFY keystore
	fn mock_ecdsa_signatures() -> (EcdsaSignature, EcdsaSignature) {
		let alice = sp_core::ecdsa::Pair::from_string("//Alice", None).unwrap();

		let msg = keccak_256(b"This is the first message");
		let sig1 = alice.sign_prehashed(&msg);

		let msg = keccak_256(b"This is the second message");
		let sig2 = alice.sign_prehashed(&msg);

		(sig1.into(), sig2.into())
	}

	// Generates mock aggregatable bls signature for generating test commitment
	// BLS signatures
	#[cfg(feature = "bls-experimental")]
	fn mock_bls_signatures() -> (BlsSignature, BlsSignature) {
		let alice = sp_core::bls::Pair::from_string("//Alice", None).unwrap();

		let msg = b"This is the first message";
		let sig1 = alice.sign(msg);

		let msg = b"This is the second message";
		let sig2 = alice.sign(msg);

		(sig1.into(), sig2.into())
	}

	fn ecdsa_signed_commitment() -> TestEcdsaSignedCommitment {
		let payload = Payload::from_single_entry(
			known_payloads::MMR_ROOT_ID,
			"Hello World!".as_bytes().to_vec(),
		);
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		let sigs = mock_ecdsa_signatures();

		SignedCommitment { commitment, signatures: vec![None, None, Some(sigs.0), Some(sigs.1)] }
	}

	#[cfg(feature = "bls-experimental")]
	fn ecdsa_and_bls_signed_commitment() -> TestBlsSignedCommitment {
		let payload = Payload::from_single_entry(
			known_payloads::MMR_ROOT_ID,
			"Hello World!".as_bytes().to_vec(),
		);
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		let ecdsa_sigs = mock_ecdsa_signatures();
		let bls_sigs = mock_bls_signatures();

		SignedCommitment {
			commitment,
			signatures: vec![
				None,
				None,
				Some(EcdsaBlsSignaturePair(ecdsa_sigs.0, bls_sigs.0)),
				Some(EcdsaBlsSignaturePair(ecdsa_sigs.1, bls_sigs.1)),
			],
		}
	}

	#[test]
	fn should_convert_signed_commitment_to_witness() {
		// given
		let signed = ecdsa_signed_commitment();

		// when
		let (witness, signatures) =
			TestEcdsaSignedCommitmentWitness::from_signed(signed, |sigs| sigs.to_vec());

		// then
		assert_eq!(witness.signature_accumulator, signatures);
	}

	#[test]
	#[cfg(feature = "bls-experimental")]
	fn should_convert_dually_signed_commitment_to_witness() {
		// given
		let signed = ecdsa_and_bls_signed_commitment();

		// when
		let (witness, _signatures) =
			// from signed take a function as the aggregator 
			TestBlsSignedCommitmentWitness::from_signed::<_, _>(signed, |sigs| {
				// we are going to aggregate the signatures here
				let mut aggregatedsigs: SignatureAggregatorAssumingPoP<TinyBLS377> =
					SignatureAggregatorAssumingPoP::new(Message::new(b"", b"mock payload"));

				for sig in sigs {
					match sig {
						Some(sig) => {
							let serialized_sig : Vec<u8> = (*sig.1).to_vec();
							aggregatedsigs.add_signature(
								&w3f_bls::Signature::<TinyBLS377>::from_bytes(
									serialized_sig.as_slice()
								).unwrap()
							);
						},
						None => (),
					}
				}
				(&aggregatedsigs).signature().to_bytes()
			});

		// We can't use BlsSignature::try_from because it expected 112Bytes (CP (64) + BLS 48)
		// single signature while we are having a BLS aggregated signature corresponding to no CP.
		w3f_bls::Signature::<TinyBLS377>::from_bytes(witness.signature_accumulator.as_slice())
			.unwrap();
	}

	#[test]
	fn should_encode_and_decode_witness() {
		// Given
		let signed = ecdsa_signed_commitment();
		let (witness, _) = TestEcdsaSignedCommitmentWitness::from_signed::<_, _>(
			signed,
			|sigs: &[std::option::Option<EcdsaSignature>]| sigs.to_vec(),
		);

		// When
		let encoded = codec::Encode::encode(&witness);
		let decoded = TestEcdsaSignedCommitmentWitness::decode(&mut &*encoded);

		// Then
		assert_eq!(decoded, Ok(witness));
		assert_eq!(
			encoded,
			array_bytes::hex2bytes_unchecked(
				"\
				046d683048656c6c6f20576f726c642105000000000000000000000000000000000000000000000010\
				0000010110000001558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c\
				746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01012d6e1f8105c337a8\
				6cdd9aaacdc496577f3db8c55ef9e6fd48f2c5c05a2274707491635d8ba3df64f324575b7b2a34487b\
				ca2324b6a0046395a71681be3d0c2a00\
			"
			)
		);
	}
}
