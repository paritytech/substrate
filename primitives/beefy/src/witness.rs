// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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
pub struct SignedCommitmentWitness<TBlockNumber, TMerkleRoot> {
	/// The full content of the commitment.
	pub commitment: Commitment<TBlockNumber>,

	/// The bit vector of validators who signed the commitment.
	pub signed_by: Vec<bool>, // TODO [ToDr] Consider replacing with bitvec crate

	/// A merkle root of signatures in the original signed commitment.
	pub signatures_merkle_root: TMerkleRoot,
}

impl<TBlockNumber, TMerkleRoot> SignedCommitmentWitness<TBlockNumber, TMerkleRoot> {
	/// Convert [SignedCommitment] into [SignedCommitmentWitness].
	///
	/// This takes a [SignedCommitment], which contains full signatures
	/// and converts it into a witness form, which does not contain full signatures,
	/// only a bit vector indicating which validators have signed the original [SignedCommitment]
	/// and a merkle root of all signatures.
	///
	/// Returns the full list of signatures along with the witness.
	pub fn from_signed<TMerkelize, TSignature>(
		signed: SignedCommitment<TBlockNumber, TSignature>,
		merkelize: TMerkelize,
	) -> (Self, Vec<Option<TSignature>>)
	where
		TMerkelize: FnOnce(&[Option<TSignature>]) -> TMerkleRoot,
	{
		let SignedCommitment { commitment, signatures } = signed;
		let signed_by = signatures.iter().map(|s| s.is_some()).collect();
		let signatures_merkle_root = merkelize(&signatures);

		(Self { commitment, signed_by, signatures_merkle_root }, signatures)
	}
}

#[cfg(test)]
mod tests {

	use sp_core::{keccak_256, Pair};
	use sp_keystore::{testing::KeyStore, SyncCryptoStore, SyncCryptoStorePtr};

	use super::*;
	use codec::Decode;

	use crate::{crypto, known_payload_ids, Payload, KEY_TYPE};

	type TestCommitment = Commitment<u128>;
	type TestSignedCommitment = SignedCommitment<u128, crypto::Signature>;
	type TestSignedCommitmentWitness =
		SignedCommitmentWitness<u128, Vec<Option<crypto::Signature>>>;

	// The mock signatures are equivalent to the ones produced by the BEEFY keystore
	fn mock_signatures() -> (crypto::Signature, crypto::Signature) {
		let store: SyncCryptoStorePtr = KeyStore::new().into();

		let alice = sp_core::ecdsa::Pair::from_string("//Alice", None).unwrap();
		let _ =
			SyncCryptoStore::insert_unknown(&*store, KEY_TYPE, "//Alice", alice.public().as_ref())
				.unwrap();

		let msg = keccak_256(b"This is the first message");
		let sig1 = SyncCryptoStore::ecdsa_sign_prehashed(&*store, KEY_TYPE, &alice.public(), &msg)
			.unwrap()
			.unwrap();

		let msg = keccak_256(b"This is the second message");
		let sig2 = SyncCryptoStore::ecdsa_sign_prehashed(&*store, KEY_TYPE, &alice.public(), &msg)
			.unwrap()
			.unwrap();

		(sig1.into(), sig2.into())
	}

	fn signed_commitment() -> TestSignedCommitment {
		let payload =
			Payload::new(known_payload_ids::MMR_ROOT_ID, "Hello World!".as_bytes().to_vec());
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		let sigs = mock_signatures();

		SignedCommitment { commitment, signatures: vec![None, None, Some(sigs.0), Some(sigs.1)] }
	}

	#[test]
	fn should_convert_signed_commitment_to_witness() {
		// given
		let signed = signed_commitment();

		// when
		let (witness, signatures) =
			TestSignedCommitmentWitness::from_signed(signed, |sigs| sigs.to_vec());

		// then
		assert_eq!(witness.signatures_merkle_root, signatures);
	}

	#[test]
	fn should_encode_and_decode_witness() {
		// given
		let signed = signed_commitment();
		let (witness, _) = TestSignedCommitmentWitness::from_signed(signed, |sigs| sigs.to_vec());

		// when
		let encoded = codec::Encode::encode(&witness);
		let decoded = TestSignedCommitmentWitness::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(witness));
		assert_eq!(
			encoded,
			hex_literal::hex!(
				"046d683048656c6c6f20576f726c642105000000000000000000000000000000000000000000000010
				0000010110000001558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c
				746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01012d6e1f8105c337a86
				cdd9aaacdc496577f3db8c55ef9e6fd48f2c5c05a2274707491635d8ba3df64f324575b7b2a34487bc
				a2324b6a0046395a71681be3d0c2a00"
			)
		);
	}
}
