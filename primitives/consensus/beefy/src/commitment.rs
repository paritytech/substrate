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

use codec::{Decode, Encode, Error, Input};
use scale_info::TypeInfo;
use sp_std::{cmp, prelude::*};

use crate::{Payload, ValidatorSetId};

/// A commitment signed by GRANDPA validators as part of BEEFY protocol.
///
/// The commitment contains a [payload](Commitment::payload) extracted from the finalized block at
/// height [block_number](Commitment::block_number).
/// GRANDPA validators collect signatures on commitments and a stream of such signed commitments
/// (see [SignedCommitment]) forms the BEEFY protocol.
#[derive(Clone, Debug, PartialEq, Eq, Encode, Decode, TypeInfo)]
pub struct Commitment<TBlockNumber> {
	///  A collection of payloads to be signed, see [`Payload`] for details.
	///
	/// One of the payloads should be some form of cumulative representation of the chain (think
	/// MMR root hash). Additionally one of the payloads should also contain some details that
	/// allow the light client to verify next validator set. The protocol does not enforce any
	/// particular format of this data, nor how often it should be present in commitments, however
	/// the light client has to be provided with full validator set whenever it performs the
	/// transition (i.e. importing first block with
	/// [validator_set_id](Commitment::validator_set_id) incremented).
	pub payload: Payload,

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
	/// `validator_set_id`. Validator set data MUST be verifiable, for instance using
	/// [payload](Commitment::payload) information.
	pub validator_set_id: ValidatorSetId,
}

impl<TBlockNumber> cmp::PartialOrd for Commitment<TBlockNumber>
where
	TBlockNumber: cmp::Ord,
{
	fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
		Some(self.cmp(other))
	}
}

impl<TBlockNumber> cmp::Ord for Commitment<TBlockNumber>
where
	TBlockNumber: cmp::Ord,
{
	fn cmp(&self, other: &Self) -> cmp::Ordering {
		self.validator_set_id
			.cmp(&other.validator_set_id)
			.then_with(|| self.block_number.cmp(&other.block_number))
			.then_with(|| self.payload.cmp(&other.payload))
	}
}

/// A commitment with matching GRANDPA validators' signatures.
///
/// Note that SCALE-encoding of the structure is optimized for size efficiency over the wire,
/// please take a look at custom [`Encode`] and [`Decode`] implementations and
/// `CompactSignedCommitment` struct.
#[derive(Clone, Debug, PartialEq, Eq, TypeInfo)]
pub struct SignedCommitment<TBlockNumber, TSignature> {
	/// The commitment signatures are collected for.
	pub commitment: Commitment<TBlockNumber>,
	/// GRANDPA validators' signatures for the commitment.
	///
	/// The length of this `Vec` must match number of validators in the current set (see
	/// [Commitment::validator_set_id]).
	pub signatures: Vec<Option<TSignature>>,
}

impl<TBlockNumber, TSignature> SignedCommitment<TBlockNumber, TSignature> {
	/// Return the number of collected signatures.
	pub fn no_of_signatures(&self) -> usize {
		self.signatures.iter().filter(|x| x.is_some()).count()
	}
}

/// Type to be used to denote placement of signatures
type BitField = Vec<u8>;
/// Compress 8 bit values into a single u8 Byte
const CONTAINER_BIT_SIZE: usize = 8;

/// Compressed representation of [`SignedCommitment`], used for encoding efficiency.
#[derive(Clone, Debug, PartialEq, Eq, Encode, Decode)]
struct CompactSignedCommitment<TBlockNumber, TSignature> {
	/// The commitment, unchanged compared to regular [`SignedCommitment`].
	commitment: Commitment<TBlockNumber>,
	/// A bitfield representing presence of a signature coming from a validator at some index.
	///
	/// The bit at index `0` is set to `1` in case we have a signature coming from a validator at
	/// index `0` in in the original validator set. In case the [`SignedCommitment`] does not
	/// contain that signature the `bit` will be set to `0`. Bits are packed into `Vec<u8>`
	signatures_from: BitField,
	/// Number of validators in the Validator Set and hence number of significant bits in the
	/// [`signatures_from`] collection.
	///
	/// Note this might be smaller than the size of `signatures_compact` in case some signatures
	/// are missing.
	validator_set_len: u32,
	/// A `Vec` containing all `Signature`s present in the original [`SignedCommitment`].
	///
	/// Note that in order to associate a `Signature` from this `Vec` with a validator, one needs
	/// to look at the `signatures_from` bitfield, since some validators might have not produced a
	/// signature.
	signatures_compact: Vec<TSignature>,
}

impl<'a, TBlockNumber: Clone, TSignature> CompactSignedCommitment<TBlockNumber, &'a TSignature> {
	/// Packs a `SignedCommitment` into the compressed `CompactSignedCommitment` format for
	/// efficient network transport.
	fn pack(signed_commitment: &'a SignedCommitment<TBlockNumber, TSignature>) -> Self {
		let SignedCommitment { commitment, signatures } = signed_commitment;
		let validator_set_len = signatures.len() as u32;

		let signatures_compact: Vec<&'a TSignature> =
			signatures.iter().filter_map(|x| x.as_ref()).collect();
		let bits = {
			let mut bits: Vec<u8> =
				signatures.iter().map(|x| if x.is_some() { 1 } else { 0 }).collect();
			// Resize with excess bits for placement purposes
			let excess_bits_len =
				CONTAINER_BIT_SIZE - (validator_set_len as usize % CONTAINER_BIT_SIZE);
			bits.resize(bits.len() + excess_bits_len, 0);
			bits
		};

		let mut signatures_from: BitField = vec![];
		let chunks = bits.chunks(CONTAINER_BIT_SIZE);
		for chunk in chunks {
			let mut iter = chunk.iter().copied();
			let mut v = iter.next().unwrap() as u8;

			for bit in iter {
				v <<= 1;
				v |= bit as u8;
			}

			signatures_from.push(v);
		}

		Self {
			commitment: commitment.clone(),
			signatures_from,
			validator_set_len,
			signatures_compact,
		}
	}

	/// Unpacks a `CompactSignedCommitment` into the uncompressed `SignedCommitment` form.
	fn unpack(
		temporary_signatures: CompactSignedCommitment<TBlockNumber, TSignature>,
	) -> SignedCommitment<TBlockNumber, TSignature> {
		let CompactSignedCommitment {
			commitment,
			signatures_from,
			validator_set_len,
			signatures_compact,
		} = temporary_signatures;
		let mut bits: Vec<u8> = vec![];

		for block in signatures_from {
			for bit in 0..CONTAINER_BIT_SIZE {
				bits.push((block >> (CONTAINER_BIT_SIZE - bit - 1)) & 1);
			}
		}

		bits.truncate(validator_set_len as usize);

		let mut next_signature = signatures_compact.into_iter();
		let signatures: Vec<Option<TSignature>> = bits
			.iter()
			.map(|&x| if x == 1 { next_signature.next() } else { None })
			.collect();

		SignedCommitment { commitment, signatures }
	}
}

impl<TBlockNumber, TSignature> Encode for SignedCommitment<TBlockNumber, TSignature>
where
	TBlockNumber: Encode + Clone,
	TSignature: Encode,
{
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		let temp = CompactSignedCommitment::pack(self);
		temp.using_encoded(f)
	}
}

impl<TBlockNumber, TSignature> Decode for SignedCommitment<TBlockNumber, TSignature>
where
	TBlockNumber: Decode + Clone,
	TSignature: Decode,
{
	fn decode<I: Input>(input: &mut I) -> Result<Self, Error> {
		let temp = CompactSignedCommitment::decode(input)?;
		Ok(CompactSignedCommitment::unpack(temp))
	}
}

/// A [SignedCommitment] with a version number.
///
/// This variant will be appended to the block justifications for the block
/// for which the signed commitment has been generated.
///
/// Note that this enum is subject to change in the future with introduction
/// of additional cryptographic primitives to BEEFY.
#[derive(Clone, Debug, PartialEq, codec::Encode, codec::Decode)]
pub enum VersionedFinalityProof<N, S> {
	#[codec(index = 1)]
	/// Current active version
	V1(SignedCommitment<N, S>),
}

impl<N, S> From<SignedCommitment<N, S>> for VersionedFinalityProof<N, S> {
	fn from(commitment: SignedCommitment<N, S>) -> Self {
		VersionedFinalityProof::V1(commitment)
	}
}

#[cfg(test)]
mod tests {

	use super::*;
	use crate::{ecdsa_crypto::Signature as EcdsaSignature, known_payloads};
	use codec::Decode;
	use sp_core::{keccak_256, Pair};

	#[cfg(feature = "bls-experimental")]
	use crate::bls_crypto::Signature as BlsSignature;

	type TestCommitment = Commitment<u128>;

	const LARGE_RAW_COMMITMENT: &[u8] = include_bytes!("../test-res/large-raw-commitment");

	// Types for bls-less commitment
	type TestEcdsaSignedCommitment = SignedCommitment<u128, EcdsaSignature>;
	type TestVersionedFinalityProof = VersionedFinalityProof<u128, EcdsaSignature>;

	// Types for commitment supporting aggregatable bls signature
	#[cfg(feature = "bls-experimental")]
	#[derive(Clone, Debug, PartialEq, codec::Encode, codec::Decode)]
	struct BlsAggregatableSignature(BlsSignature);

	#[cfg(feature = "bls-experimental")]
	#[derive(Clone, Debug, PartialEq, codec::Encode, codec::Decode)]
	struct EcdsaBlsSignaturePair(EcdsaSignature, BlsSignature);

	#[cfg(feature = "bls-experimental")]
	type TestBlsSignedCommitment = SignedCommitment<u128, EcdsaBlsSignaturePair>;

	// Generates mock aggregatable ecdsa signature for generating test commitment
	// BLS signatures
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

	#[test]
	fn commitment_encode_decode() {
		// given
		let payload =
			Payload::from_single_entry(known_payloads::MMR_ROOT_ID, "Hello World!".encode());
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		// when
		let encoded = codec::Encode::encode(&commitment);
		let decoded = TestCommitment::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(commitment));
		assert_eq!(
			encoded,
			array_bytes::hex2bytes_unchecked(
				"046d68343048656c6c6f20576f726c6421050000000000000000000000000000000000000000000000"
			)
		);
	}

	#[test]
	fn signed_commitment_encode_decode_ecdsa() {
		// given
		let payload =
			Payload::from_single_entry(known_payloads::MMR_ROOT_ID, "Hello World!".encode());
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		let ecdsa_sigs = mock_ecdsa_signatures();

		let ecdsa_signed = SignedCommitment {
			commitment: commitment.clone(),
			signatures: vec![None, None, Some(ecdsa_sigs.0.clone()), Some(ecdsa_sigs.1.clone())],
		};

		// when
		let encoded = codec::Encode::encode(&ecdsa_signed);
		let decoded = TestEcdsaSignedCommitment::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(ecdsa_signed));
		assert_eq!(
			encoded,
			array_bytes::hex2bytes_unchecked(
				"\
				046d68343048656c6c6f20576f726c64210500000000000000000000000000000000000000000000000\
				4300400000008558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746c\
				c321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba012d6e1f8105c337a86cdd9aa\
				acdc496577f3db8c55ef9e6fd48f2c5c05a2274707491635d8ba3df64f324575b7b2a34487bca2324b6\
				a0046395a71681be3d0c2a00\
			"
			)
		);
	}

	#[test]
	#[cfg(feature = "bls-experimental")]
	fn signed_commitment_encode_decode_ecdsa_n_bls() {
		// given
		let payload =
			Payload::from_single_entry(known_payloads::MMR_ROOT_ID, "Hello World!".encode());
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		let ecdsa_sigs = mock_ecdsa_signatures();

		//including bls signature
		let bls_signed_msgs = mock_bls_signatures();

		let ecdsa_and_bls_signed = SignedCommitment {
			commitment,
			signatures: vec![
				None,
				None,
				Some(EcdsaBlsSignaturePair(ecdsa_sigs.0, bls_signed_msgs.0)),
				Some(EcdsaBlsSignaturePair(ecdsa_sigs.1, bls_signed_msgs.1)),
			],
		};

		//when
		let encoded = codec::Encode::encode(&ecdsa_and_bls_signed);
		let decoded = TestBlsSignedCommitment::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(ecdsa_and_bls_signed));
		assert_eq!(
			encoded,
			array_bytes::hex2bytes_unchecked(
				"046d68343048656c6c6f20576f726c642105000000000000000000000000000000000000000000000004300400000008558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01667603fc041cf9d7147d22bf54b15e5778893d6986b71a929747befd3b4d233fbe668bc480e8865116b94db46ca25a01e03c71955f2582604e415da68f2c3c406b9d5f4ad416230ec5453f05ac16a50d8d0923dfb0413cc956ae3fa6334465bd1f2cacec8e9cd606438390fe2a29dc052d6e1f8105c337a86cdd9aaacdc496577f3db8c55ef9e6fd48f2c5c05a2274707491635d8ba3df64f324575b7b2a34487bca2324b6a0046395a71681be3d0c2a00df61d3b2be0963eb6caa243cc505d327aec73e1bb7ffe9a14b1354b0c406792ac6d6f47c06987c15dec9993f43eefa001d866fe0850d986702c414840f0d9ec0fdc04832ef91ae37c8d49e2f573ca50cb37f152801d489a19395cb04e5fc8f2ab6954b58a3bcc40ef9b6409d2ff7ef07"
			)
		);
	}

	#[test]
	fn signed_commitment_count_signatures() {
		// given
		let payload =
			Payload::from_single_entry(known_payloads::MMR_ROOT_ID, "Hello World!".encode());
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		let sigs = mock_ecdsa_signatures();

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
			let payload =
				Payload::from_single_entry(known_payloads::MMR_ROOT_ID, "Hello World!".encode());
			Commitment { payload, block_number, validator_set_id }
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
		let payload =
			Payload::from_single_entry(known_payloads::MMR_ROOT_ID, "Hello World!".encode());
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		let sigs = mock_ecdsa_signatures();

		let signed = SignedCommitment {
			commitment,
			signatures: vec![None, None, Some(sigs.0), Some(sigs.1)],
		};

		let versioned = TestVersionedFinalityProof::V1(signed.clone());

		let encoded = codec::Encode::encode(&versioned);

		assert_eq!(1, encoded[0]);
		assert_eq!(encoded[1..], codec::Encode::encode(&signed));

		let decoded = TestVersionedFinalityProof::decode(&mut &*encoded);

		assert_eq!(decoded, Ok(versioned));
	}

	#[test]
	fn large_signed_commitment_encode_decode() {
		// given
		let payload =
			Payload::from_single_entry(known_payloads::MMR_ROOT_ID, "Hello World!".encode());
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		let sigs = mock_ecdsa_signatures();

		let signatures: Vec<Option<_>> = (0..1024)
			.into_iter()
			.map(|x| if x < 340 { None } else { Some(sigs.0.clone()) })
			.collect();
		let signed = SignedCommitment { commitment, signatures };

		// when
		let encoded = codec::Encode::encode(&signed);
		let decoded = TestEcdsaSignedCommitment::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(signed));
		assert_eq!(encoded, LARGE_RAW_COMMITMENT);
	}
}
