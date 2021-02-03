// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

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
pub struct SignedCommitmentWitness<TBlockNumber, TPayload, TMerkleRoot> {
	/// The full content of the commitment.
	pub commitment: Commitment<TBlockNumber, TPayload>,

	/// The bit vector of validators who signed the commitment.
	pub signed_by: Vec<bool>, // TODO [ToDr] Consider replacing with bitvec crate

	/// A merkle root of signatures in the original signed commitment.
	pub signatures_merkle_root: TMerkleRoot,
}

impl<TBlockNumber, TPayload, TMerkleRoot> SignedCommitmentWitness<TBlockNumber, TPayload, TMerkleRoot> {
	/// Convert [SignedCommitment] into [SignedCommitmentWitness].
	///
	/// This takes a [SignedCommitment], which contains full signatures
	/// and converts it into a witness form, which does not contain full signatures,
	/// only a bit vector indicating which validators have signed the original [SignedCommitment]
	/// and a merkle root of all signatures.
	///
	/// Returns the full list of signatures along with the witness.
	pub fn from_signed<TSignature, TMerkelize>(
		signed: SignedCommitment<TBlockNumber, TPayload, TSignature>,
		merkelize: TMerkelize,
	) -> (Self, Vec<Option<TSignature>>)
	where
		TMerkelize: FnOnce(&[Option<TSignature>]) -> TMerkleRoot,
	{
		let SignedCommitment { commitment, signatures } = signed;
		let signed_by = signatures.iter().map(|s| s.is_some()).collect();
		let signatures_merkle_root = merkelize(&signatures);

		(
			Self {
				commitment,
				signed_by,
				signatures_merkle_root,
			},
			signatures,
		)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::Decode;

	type TestCommitment = Commitment<u128, String>;
	type TestSignedCommitment = SignedCommitment<u128, String, Vec<u8>>;
	type TestSignedCommitmentWitness = SignedCommitmentWitness<u128, String, Vec<Option<Vec<u8>>>>;

	fn signed_commitment() -> TestSignedCommitment {
		let commitment: TestCommitment = Commitment {
			payload: "Hello World!".into(),
			block_number: 5,
			validator_set_id: 0,
		};

		SignedCommitment {
			commitment,
			signatures: vec![None, None, Some(vec![1, 2, 3, 4]), Some(vec![5, 6, 7, 8])],
		}
	}

	#[test]
	fn should_convert_signed_commitment_to_witness() {
		// given
		let signed = signed_commitment();

		// when
		let (witness, signatures) = TestSignedCommitmentWitness::from_signed(signed, |sigs| sigs.to_vec());

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
				"3048656c6c6f20576f726c64210500000000000000000000000000000000000000000000001000000101100000011001020304011005060708"
			)
		);
	}
}
