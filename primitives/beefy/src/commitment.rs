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

use sp_std::{cmp, prelude::*};

use crate::{crypto::Signature, ValidatorSetId};

/// A commitment signed by GRANDPA validators as part of BEEFY protocol.
///
/// The commitment contains a [payload] extracted from the finalized block at height [block_number].
/// GRANDPA validators collect signatures on commitments and a stream of such signed commitments
/// (see [SignedCommitment]) forms the BEEFY protocol.
#[derive(Clone, Debug, PartialEq, Eq, codec::Encode, codec::Decode)]
pub struct Commitment<TBlockNumber, TPayload> {
	/// The payload being signed.
	///
	/// This should be some form of cumulative representation of the chain (think MMR root hash).
	/// The payload should also contain some details that allow the light client to verify next
	/// validator set. The protocol does not enforce any particular format of this data,
	/// nor how often it should be present in commitments, however the light client has to be
	/// provided with full validator set whenever it performs the transition (i.e. importing first
	/// block with [validator_set_id] incremented).
	pub payload: TPayload,

	/// Finalized block number this commitment is for.
	///
	/// GRANDPA validators agree on a block they create a commitment for and start collecting
	/// signatures. This process is called a round.
	/// There might be multiple rounds in progress (depending on the block choice rule), however
	/// since the payload is supposed to be cumulative, it is not required to import all
	/// commitments.
	/// BEEFY light client is expected to import at least one commitment per epoch,
	/// but is free to import as many as it requires.
	pub block_number: TBlockNumber,

	/// BEEFY validator set supposed to sign this commitment.
	///
	/// Validator set is changing once per epoch. The Light Client must be provided by details
	/// about the validator set whenever it's importing first commitment with a new
	/// `validator_set_id`. Validator set data MUST be verifiable, for instance using [payload]
	/// information.
	pub validator_set_id: ValidatorSetId,
}

impl<TBlockNumber, TPayload> cmp::PartialOrd for Commitment<TBlockNumber, TPayload>
where
	TBlockNumber: cmp::Ord,
	TPayload: cmp::Eq,
{
	fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl<TBlockNumber, TPayload> cmp::Ord for Commitment<TBlockNumber, TPayload>
where
	TBlockNumber: cmp::Ord,
	TPayload: cmp::Eq,
{
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		self.validator_set_id
			.cmp(&other.validator_set_id)
			.then_with(|| self.block_number.cmp(&other.block_number))
	}
}

/// A commitment with matching GRANDPA validators' signatures.
#[derive(Clone, Debug, PartialEq, Eq, codec::Encode, codec::Decode)]
pub struct SignedCommitment<TBlockNumber, TPayload> {
	/// The commitment signatures are collected for.
	pub commitment: Commitment<TBlockNumber, TPayload>,
	/// GRANDPA validators' signatures for the commitment.
	///
	/// The length of this `Vec` must match number of validators in the current set (see
	/// [Commitment::validator_set_id]).
	pub signatures: Vec<Option<Signature>>,
}

impl<TBlockNumber, TPayload> SignedCommitment<TBlockNumber, TPayload> {
	/// Return the number of collected signatures.
	pub fn no_of_signatures(&self) -> usize {
		self.signatures.iter().filter(|x| x.is_some()).count()
	}
}

/// A [SignedCommitment] with a version number. This variant will be appended
/// to the block justifications for the block for which the signed commitment
/// has been generated.
#[derive(Clone, Debug, PartialEq, codec::Encode, codec::Decode)]
pub enum VersionedCommitment<N, P> {
	#[codec(index = 1)]
	/// Current active version
	V1(SignedCommitment<N, P>),
}

#[cfg(test)]
mod tests {

	use sp_core::{keccak_256, Pair};
	use sp_keystore::{testing::KeyStore, SyncCryptoStore, SyncCryptoStorePtr};

	use super::*;
	use codec::Decode;

	use crate::{crypto, KEY_TYPE};

	type TestCommitment = Commitment<u128, String>;
	type TestSignedCommitment = SignedCommitment<u128, String>;
	type TestVersionedCommitment = VersionedCommitment<u128, String>;

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

	#[test]
	fn commitment_encode_decode() {
		// given
		let commitment: TestCommitment =
			Commitment { payload: "Hello World!".into(), block_number: 5, validator_set_id: 0 };

		// when
		let encoded = codec::Encode::encode(&commitment);
		let decoded = TestCommitment::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(commitment));
		assert_eq!(
			encoded,
			hex_literal::hex!(
				"3048656c6c6f20576f726c6421050000000000000000000000000000000000000000000000"
			)
		);
	}

	#[test]
	fn signed_commitment_encode_decode() {
		// given
		let commitment: TestCommitment =
			Commitment { payload: "Hello World!".into(), block_number: 5, validator_set_id: 0 };

		let sigs = mock_signatures();

		let signed = SignedCommitment {
			commitment,
			signatures: vec![None, None, Some(sigs.0), Some(sigs.1)],
		};

		// when
		let encoded = codec::Encode::encode(&signed);
		let decoded = TestSignedCommitment::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(signed));
		assert_eq!(
			encoded,
			hex_literal::hex!(
				"3048656c6c6f20576f726c64210500000000000000000000000000000000000000000000001000
			0001558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d
			10dd3cd68ce3dc0c33c86e99bcb7816f9ba01012d6e1f8105c337a86cdd9aaacdc496577f3db8c55ef9e6fd48f2c5c05a
			2274707491635d8ba3df64f324575b7b2a34487bca2324b6a0046395a71681be3d0c2a00"
			)
		);
	}

	#[test]
	fn signed_commitment_count_signatures() {
		// given
		let commitment: TestCommitment =
			Commitment { payload: "Hello World!".into(), block_number: 5, validator_set_id: 0 };

		let sigs = mock_signatures();

		let mut signed = SignedCommitment {
			commitment,
			signatures: vec![None, None, Some(sigs.0), Some(sigs.1)],
		};
		assert_eq!(signed.no_of_signatures(), 2);

		// when
		signed.signatures[2] = None;

		// then
		assert_eq!(signed.no_of_signatures(), 1);
	}

	#[test]
	fn commitment_ordering() {
		fn commitment(
			block_number: u128,
			validator_set_id: crate::ValidatorSetId,
		) -> TestCommitment {
			Commitment { payload: "Hello World!".into(), block_number, validator_set_id }
		}

		// given
		let a = commitment(1, 0);
		let b = commitment(2, 1);
		let c = commitment(10, 0);
		let d = commitment(10, 1);

		// then
		assert!(a < b);
		assert!(a < c);
		assert!(c < b);
		assert!(c < d);
		assert!(b < d);
	}

	#[test]
	fn versioned_commitment_encode_decode() {
		let commitment: TestCommitment =
			Commitment { payload: "Hello World!".into(), block_number: 5, validator_set_id: 0 };

		let sigs = mock_signatures();

		let signed = SignedCommitment {
			commitment,
			signatures: vec![None, None, Some(sigs.0), Some(sigs.1)],
		};

		let versioned = TestVersionedCommitment::V1(signed.clone());

		let encoded = codec::Encode::encode(&versioned);

		assert_eq!(1, encoded[0]);
		assert_eq!(encoded[1..], codec::Encode::encode(&signed));

		let decoded = TestVersionedCommitment::decode(&mut &*encoded);

		assert_eq!(decoded, Ok(versioned));
	}
}
