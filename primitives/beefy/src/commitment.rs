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

use sp_std::{cmp, prelude::*};

use crate::ValidatorSetId;

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
	/// Validator set is changing once per epoch. The Light Client must be provided by details about
	/// the validator set whenever it's importing first commitment with a new `validator_set_id`.
	/// Validator set data MUST be verifiable, for instance using [payload] information.
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
pub struct SignedCommitment<TBlockNumber, TPayload, TSignature> {
	/// The commitment signatures are collected for.
	pub commitment: Commitment<TBlockNumber, TPayload>,
	/// GRANDPA validators' signatures for the commitment.
	///
	/// The length of this `Vec` must match number of validators in the current set (see
	/// [Commitment::validator_set_id]).
	pub signatures: Vec<Option<TSignature>>,
}

impl<TBlockNumber, TPayload, TSignature> SignedCommitment<TBlockNumber, TPayload, TSignature> {
	/// Return the number of collected signatures.
	pub fn no_of_signatures(&self) -> usize {
		self.signatures.iter().filter(|x| x.is_some()).count()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::Decode;

	type TestCommitment = Commitment<u128, String>;
	type TestSignedCommitment = SignedCommitment<u128, String, Vec<u8>>;

	#[test]
	fn commitment_encode_decode() {
		// given
		let commitment: TestCommitment = Commitment {
			payload: "Hello World!".into(),
			block_number: 5,
			validator_set_id: 0,
		};

		// when
		let encoded = codec::Encode::encode(&commitment);
		let decoded = TestCommitment::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(commitment));
		assert_eq!(
			encoded,
			hex_literal::hex!("3048656c6c6f20576f726c6421050000000000000000000000000000000000000000000000")
		);
	}

	#[test]
	fn signed_commitment_encode_decode() {
		// given
		let commitment: TestCommitment = Commitment {
			payload: "Hello World!".into(),
			block_number: 5,
			validator_set_id: 0,
		};
		let signed = SignedCommitment {
			commitment,
			signatures: vec![None, None, Some(vec![1, 2, 3, 4]), Some(vec![5, 6, 7, 8])],
		};

		// when
		let encoded = codec::Encode::encode(&signed);
		let decoded = TestSignedCommitment::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(signed));
		assert_eq!(
			encoded,
			hex_literal::hex!(
				"3048656c6c6f20576f726c6421050000000000000000000000000000000000000000000000100000011001020304011005060708"
			)
		);
	}

	#[test]
	fn signed_commitment_count_signatures() {
		// given
		let commitment: TestCommitment = Commitment {
			payload: "Hello World!".into(),
			block_number: 5,
			validator_set_id: 0,
		};
		let mut signed = SignedCommitment {
			commitment,
			signatures: vec![None, None, Some(vec![1, 2, 3, 4]), Some(vec![5, 6, 7, 8])],
		};
		assert_eq!(signed.no_of_signatures(), 2);

		// when
		signed.signatures[2] = None;

		// then
		assert_eq!(signed.no_of_signatures(), 1);
	}

	#[test]
	fn commitment_ordering() {
		fn commitment(block_number: u128, validator_set_id: crate::ValidatorSetId) -> TestCommitment {
			Commitment {
				payload: "Hello World!".into(),
				block_number,
				validator_set_id,
			}
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
}
