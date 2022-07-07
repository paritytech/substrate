// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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
use sp_std::{cmp, prelude::*};

use crate::ValidatorSetId;

/// Id of different payloads in the [`Commitment`] data
pub type BeefyPayloadId = [u8; 2];

/// Registry of all known [`BeefyPayloadId`].
pub mod known_payload_ids {
	use crate::BeefyPayloadId;

	/// A [`Payload`](super::Payload) identifier for Merkle Mountain Range root hash.
	///
	/// Encoded value should contain a [`crate::MmrRootHash`] type (i.e. 32-bytes hash).
	pub const MMR_ROOT_ID: BeefyPayloadId = *b"mh";
}

/// A BEEFY payload type allowing for future extensibility of adding additional kinds of payloads.
///
/// The idea is to store a vector of SCALE-encoded values with an extra identifier.
/// Identifiers MUST be sorted by the [`BeefyPayloadId`] to allow efficient lookup of expected
/// value. Duplicated identifiers are disallowed. It's okay for different implementations to only
/// support a subset of possible values.
#[derive(Decode, Encode, Debug, PartialEq, Eq, Clone, Ord, PartialOrd, Hash)]
pub struct Payload(Vec<(BeefyPayloadId, Vec<u8>)>);

impl Payload {
	/// Construct a new payload given an initial vallue
	pub fn new(id: BeefyPayloadId, value: Vec<u8>) -> Self {
		Self(vec![(id, value)])
	}

	/// Returns a raw payload under given `id`.
	///
	/// If the [`BeefyPayloadId`] is not found in the payload `None` is returned.
	pub fn get_raw(&self, id: &BeefyPayloadId) -> Option<&Vec<u8>> {
		let index = self.0.binary_search_by(|probe| probe.0.cmp(id)).ok()?;
		Some(&self.0[index].1)
	}

	/// Returns a decoded payload value under given `id`.
	///
	/// In case the value is not there or it cannot be decoded does not match `None` is returned.
	pub fn get_decoded<T: Decode>(&self, id: &BeefyPayloadId) -> Option<T> {
		self.get_raw(id).and_then(|raw| T::decode(&mut &raw[..]).ok())
	}

	/// Push a `Vec<u8>` with a given id into the payload vec.
	/// This method will internally sort the payload vec after every push.
	///
	/// Returns self to allow for daisy chaining.
	pub fn push_raw(mut self, id: BeefyPayloadId, value: Vec<u8>) -> Self {
		self.0.push((id, value));
		self.0.sort_by_key(|(id, _)| *id);
		self
	}
}

/// A commitment signed by GRANDPA validators as part of BEEFY protocol.
///
/// The commitment contains a [payload](Commitment::payload) extracted from the finalized block at
/// height [block_number](Commitment::block_number).
/// GRANDPA validators collect signatures on commitments and a stream of such signed commitments
/// (see [SignedCommitment]) forms the BEEFY protocol.
#[derive(Clone, Debug, PartialEq, Eq, Encode, Decode)]
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
	}
}

/// A commitment with matching GRANDPA validators' signatures.
///
/// Note that SCALE-encoding of the structure is optimized for size efficiency over the wire,
/// please take a look at custom [`Encode`] and [`Decode`] implementations and
/// `CompactSignedCommitment` struct.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignedCommitment<TBlockNumber, TSignature, TAggregatableSignature> {
	/// The commitment signatures are collected for.
	pub commitment: Commitment<TBlockNumber>,
	/// GRANDPA validators' signatures for the commitment.
	///
	/// The length of this `Vec` must match number of validators in the current set (see
	/// [Commitment::validator_set_id]).
	pub signatures: Vec<Option<TSignature>>,

	//@drskalman: This was the original suggestion, now the suggestion is to
	//SignedCommitment<BlockNumber, (ecdsa::Signature, (bls::Signature,
	//ecsda::Signature))>). It still doesn't leave a place for aggregation, but maybe
	//aggregation happens somewhere else. This also waste space on otherwise
	//aggregatable BLSSignature.

	//@AlistairStewart also said it does not make sense to gossip list bls singnature without
	//aggergating them.
	pub aggregatable_signature: TAggregatableSignature,
}

impl<TBlockNumber, TSignature, TAggregatableSignature>
	SignedCommitment<TBlockNumber, TSignature, TAggregatableSignature>
{
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
struct CompactSignedCommitment<TBlockNumber, TSignature, TAggregatableSignature> {
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

	/// A form of signature which can aggregate many signatures in one object rather than a vector.
	aggregatable_signature: TAggregatableSignature,
}

impl<'a, TBlockNumber: Clone, TSignature, TAggregatableSignature>
	CompactSignedCommitment<TBlockNumber, &'a TSignature, &'a TAggregatableSignature>
{
	/// Packs a `SignedCommitment` into the compressed `CompactSignedCommitment` format for
	/// efficient network transport.
	fn pack(
		signed_commitment: &'a SignedCommitment<TBlockNumber, TSignature, TAggregatableSignature>,
	) -> Self {
		let SignedCommitment { commitment, signatures, aggregatable_signature } = signed_commitment;
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
			aggregatable_signature,
		}
	}

	/// Unpacks a `CompactSignedCommitment` into the uncompressed `SignedCommitment` form.
	fn unpack(
		temporary_signatures: CompactSignedCommitment<
			TBlockNumber,
			TSignature,
			TAggregatableSignature,
		>,
	) -> SignedCommitment<TBlockNumber, TSignature, TAggregatableSignature> {
		let CompactSignedCommitment {
			commitment,
			signatures_from,
			validator_set_len,
			signatures_compact,
			aggregatable_signature,
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

		SignedCommitment { commitment, signatures, aggregatable_signature }
	}
}

impl<TBlockNumber, TSignature, TAggregatableSignature> Encode
	for SignedCommitment<TBlockNumber, TSignature, TAggregatableSignature>
where
	TBlockNumber: Encode + Clone,
	TSignature: Encode,
	TAggregatableSignature: Encode,
{
	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		let temp = CompactSignedCommitment::pack(self);
		temp.using_encoded(f)
	}
}

impl<TBlockNumber, TSignature, TAggregatableSignature> Decode
	for SignedCommitment<TBlockNumber, TSignature, TAggregatableSignature>
where
	TBlockNumber: Decode + Clone,
	TSignature: Decode,
	TAggregatableSignature: Decode,
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
pub enum VersionedFinalityProof<N, S, AS> {
	#[codec(index = 1)]
	/// Current active version
	V1(SignedCommitment<N, S, AS>),
}

#[cfg(test)]
mod tests {

	use hex::ToHex;
use sp_core::{keccak_256, Pair};
	use sp_keystore::{testing::KeyStore, SyncCryptoStore, SyncCryptoStorePtr};

	use super::*;
	use codec::Decode;

	use crate::{crypto, KEY_TYPE, bls_crypto::{Signature as BLSSignature}};
	use bls_like::{Keypair, SignedMessage as BLSSignedMessage, Signed, pop::SignatureAggregatorAssumingPoP, BLS377, SerializableToBytes};	

	type TestCommitment = Commitment<u128>;

        ///types for bls-less commitment
	#[derive(Clone, Debug, PartialEq, codec::Encode, codec::Decode)]
	struct TestNOPAggregatableSignature;

	type TestSignedCommitment =
		SignedCommitment<u128, crypto::Signature, TestNOPAggregatableSignature>;
	type TestVersionedFinalityProof =
	VersionedFinalityProof<u128, crypto::Signature, TestNOPAggregatableSignature>;

	///types for commitment supporting aggregatable bls signature
	#[derive(Clone, Debug, PartialEq, codec::Encode, codec::Decode)]
	struct BLSAggregatableSignature(BLSSignature);
	type TestBLSSignedCommitment =
		SignedCommitment<u128, crypto::Signature, BLSAggregatableSignature>;
	type TestVersionedBLSFinalityProof =
	VersionedFinalityProof<u128, crypto::Signature, BLSAggregatableSignature>;
	
	// The mock signatures are equivalent to the ones produced by the BEEFY keystore
	fn mock_ecdsa_signatures() -> (crypto::Signature, crypto::Signature) {
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

	///generates mock aggregatable bls signature for generating test commitment
	///note that with the current scheme we need Signer's BLS public key in order to aggregate
	///BLS signatures
	fn mock_bls_signatures() ->  (BLSSignedMessage<BLS377>, BLSSignedMessage<BLS377>) {
		let store: SyncCryptoStorePtr = KeyStore::new().into();

		let mut alice = sp_core::bls::Pair::from_string("//Alice", None).unwrap();
		let _ =
			SyncCryptoStore::insert_unknown(&*store, KEY_TYPE, "//Alice", alice.public().as_ref())
				.unwrap();

		let msg = b"This is the first message";
		let sig1 = alice.signed_message(msg);

		let msg = b"This is the second message";
		let sig2 = alice.signed_message(msg);

		(sig1.into(), sig2.into())
	}

	#[test]
	fn commitment_encode_decode() {
		// given
		let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, "Hello World!".encode());
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		// when
		let encoded = codec::Encode::encode(&commitment);
		let decoded = TestCommitment::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(commitment));
		assert_eq!(
			encoded,
			hex_literal::hex!(
				"046d68343048656c6c6f20576f726c6421050000000000000000000000000000000000000000000000"
			)
		);
	}

	#[test]
	fn signed_commitment_encode_decode() {
		// given
		let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, "Hello World!".encode());
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		let ecdsa_sigs = mock_ecdsa_signatures();

		let ecdsa_signed = SignedCommitment {
			commitment: commitment.clone(),
			signatures: vec![None, None, Some(ecdsa_sigs.0.clone()), Some(ecdsa_sigs.1.clone())],
			aggregatable_signature: TestNOPAggregatableSignature,
		};

		// when
		let encoded = codec::Encode::encode(&ecdsa_signed);
		let decoded = TestSignedCommitment::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(ecdsa_signed));
		assert_eq!(
			encoded,
			hex_literal::hex!(
				"046d68343048656c6c6f20576f726c6421050000000000000000000000000000000000000000000000
				04300400000008558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746
				cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba012d6e1f8105c337a86cdd9a
				aacdc496577f3db8c55ef9e6fd48f2c5c05a2274707491635d8ba3df64f324575b7b2a34487bca2324b
				6a0046395a71681be3d0c2a00"
			)
		);

		//including bls signature
		let bls_signed_msgs = mock_bls_signatures();

		//we are going to aggregate the signatures here, in real life, this happens when
		//validators receives other validators signatures before they are going to gossip
		//it.
		let mut aggregatedsigs =  SignatureAggregatorAssumingPoP::new();

		aggregatedsigs.aggregate(&bls_signed_msgs.0);
		aggregatedsigs.aggregate(&bls_signed_msgs.1);

		let aggregated_signature = (&aggregatedsigs).signature(); //<SignatureAggregatorAssumingPoP<BLS377>) as Signed>::signature(&aggregatedsigs.signature());

		let ecdsa_and_bls_signed = SignedCommitment {
			commitment,
			signatures: vec![None, None, Some(ecdsa_sigs.0), Some(ecdsa_sigs.1)], aggregatable_signature: BLSAggregatableSignature(BLSSignature::from(sp_core::bls::Signature(aggregated_signature.to_bytes()))),
		};

		//when
		let encoded = codec::Encode::encode(&ecdsa_and_bls_signed);
		let decoded = TestBLSSignedCommitment::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(ecdsa_and_bls_signed));
		assert_eq!(
			encoded,
			hex_literal::hex!(
				"046d68343048656c6c6f20576f726c6421050000000000000000000000000000000000000000000000
                                 04300400000008558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c74
                                 6cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba012d6e1f8105c337a86cdd
                                 9aaacdc496577f3db8c55ef9e6fd48f2c5c05a2274707491635d8ba3df64f324575b7b2a34487bca23
                                 24b6a0046395a71681be3d0c2a00c6f6312da571e1278f0e2420dd3419277883d7b9a2e5d1f6c0eba0
                                 4d0014f1644ba83ec7a24476e8ea7c4d05d1193d001c7f0bb4b946934de462bb2c3c9ddfcccde6be37
                                 486b1178ff35013222f529a2d22e043395034290b27ef07c92147401"
			)
		);


		}

	#[test]
	fn signed_commitment_count_signatures() {
		// given
		let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, "Hello World!".encode());
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		let sigs = mock_ecdsa_signatures();

		let mut signed = SignedCommitment {
			commitment,
			signatures: vec![None, None, Some(sigs.0), Some(sigs.1)],
			aggregatable_signature: TestNOPAggregatableSignature,
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
			let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, "Hello World!".encode());
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
		let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, "Hello World!".encode());
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		let sigs = mock_ecdsa_signatures();

		let signed = SignedCommitment {
			commitment,
			signatures: vec![None, None, Some(sigs.0), Some(sigs.1)],
			aggregatable_signature: TestNOPAggregatableSignature,
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
		let payload = Payload::new(known_payload_ids::MMR_ROOT_ID, "Hello World!".encode());
		let commitment: TestCommitment =
			Commitment { payload, block_number: 5, validator_set_id: 0 };

		let sigs = mock_ecdsa_signatures();

		let signatures: Vec<Option<_>> = (0..1024)
			.into_iter()
			.map(|x| if x < 340 { None } else { Some(sigs.0.clone()) })
			.collect();
		let aggregatable_signature = TestNOPAggregatableSignature;
		let signed = SignedCommitment { commitment, signatures, aggregatable_signature };

		// when
		let encoded = codec::Encode::encode(&signed);
		let decoded = TestSignedCommitment::decode(&mut &*encoded);

		// then
		assert_eq!(decoded, Ok(signed));
		assert_eq!(
			encoded,
			hex_literal::hex!(
				"046d68343048656c6c6f20576f726c6421050000000000000000000000000000000000000000000000
				05020000000000000000000000000000000000000000000000000000000000000000000000000000000
				000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
				fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
				fffffffffff0000040000b10a558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed
				4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad812
				79df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d1
				0dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2
				ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01
				558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e9
				9a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72
				d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bc
				b7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc3
				21f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9855
				80e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0
				c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da
				8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279d
				f0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd
				3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac8
				0a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558
				455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a8
				30e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d94
				8d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb78
				16f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f
				2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e
				4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33
				c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da848
				0c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df07
				95cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd
				68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a0
				9abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455
				ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e
				314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1
				107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f
				9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f231
				9a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb
				75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86
				e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c7
				46cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795c
				c985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68c
				e3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09ab
				ed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8
				1279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314
				d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107
				b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba
				01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5
				e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d
				72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99
				bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746c
				c321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98
				5580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3d
				c0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4
				da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8127
				9df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10
				dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2a
				c80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015
				58455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99
				a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d
				948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb
				7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc32
				1f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98558
				0e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c
				33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8
				480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df
				0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3
				cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80
				a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015584
				55ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a83
				0e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948
				d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb781
				6f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2
				319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4
				fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c
				86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480
				c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df079
				5cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd6
				8ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09
				abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455a
				d81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e3
				14d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d11
				07b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9
				ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319
				a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb7
				5d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e
				99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c74
				6cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc
				985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce
				3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abe
				d4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81
				279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d
				10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b
				2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0
				1558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e
				99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d7
				2d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99b
				cb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc
				321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985
				580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc
				0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4d
				a8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279
				df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10d
				d3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac
				80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155
				8455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a
				830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d9
				48d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7
				816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321
				f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580
				e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c3
				3c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da84
				80c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0
				795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3c
				d68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a
				09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155845
				5ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830
				e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d
				1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816
				f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f23
				19a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4f
				b75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c8
				6e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c
				746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795
				cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68
				ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09a
				bed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad
				81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e31
				4d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d110
				7b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9b
				a01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a
				5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75
				d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e9
				9bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746
				cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9
				85580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3
				dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed
				4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad812
				79df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d1
				0dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2
				ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01
				558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e9
				9a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72
				d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bc
				b7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc3
				21f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9855
				80e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0
				c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da
				8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279d
				f0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd
				3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac8
				0a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558
				455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a8
				30e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d94
				8d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb78
				16f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f
				2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e
				4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33
				c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da848
				0c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df07
				95cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd
				68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a0
				9abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455
				ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e
				314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1
				107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f
				9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f231
				9a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb
				75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86
				e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c7
				46cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795c
				c985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68c
				e3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09ab
				ed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8
				1279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314
				d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107
				b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba
				01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5
				e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d
				72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99
				bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746c
				c321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98
				5580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3d
				c0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4
				da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8127
				9df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10
				dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2a
				c80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015
				58455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99
				a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d
				948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb
				7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc32
				1f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98558
				0e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c
				33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8
				480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df
				0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3
				cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80
				a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015584
				55ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a83
				0e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948
				d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb781
				6f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2
				319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4
				fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c
				86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480
				c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df079
				5cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd6
				8ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09
				abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455a
				d81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e3
				14d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d11
				07b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9
				ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319
				a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb7
				5d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e
				99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c74
				6cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc
				985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce
				3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abe
				d4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81
				279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d
				10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b
				2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0
				1558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e
				99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d7
				2d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99b
				cb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc
				321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985
				580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc
				0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4d
				a8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279
				df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10d
				d3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac
				80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155
				8455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a
				830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d9
				48d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7
				816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321
				f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580
				e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c3
				3c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da84
				80c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0
				795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3c
				d68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a
				09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155845
				5ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830
				e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d
				1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816
				f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f23
				19a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4f
				b75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c8
				6e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c
				746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795
				cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68
				ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09a
				bed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad
				81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e31
				4d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d110
				7b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9b
				a01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a
				5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75
				d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e9
				9bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746
				cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9
				85580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3
				dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed
				4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad812
				79df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d1
				0dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2
				ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01
				558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e9
				9a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72
				d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bc
				b7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc3
				21f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9855
				80e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0
				c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da
				8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279d
				f0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd
				3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac8
				0a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558
				455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a8
				30e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d94
				8d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb78
				16f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f
				2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e
				4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33
				c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da848
				0c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df07
				95cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd
				68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a0
				9abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455
				ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e
				314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1
				107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f
				9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f231
				9a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb
				75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86
				e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c7
				46cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795c
				c985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68c
				e3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09ab
				ed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8
				1279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314
				d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107
				b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba
				01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5
				e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d
				72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99
				bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746c
				c321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98
				5580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3d
				c0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4
				da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8127
				9df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10
				dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2a
				c80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015
				58455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99
				a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d
				948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb
				7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc32
				1f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98558
				0e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c
				33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8
				480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df
				0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3
				cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80
				a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015584
				55ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a83
				0e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948
				d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb781
				6f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2
				319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4
				fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c
				86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480
				c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df079
				5cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd6
				8ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09
				abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455a
				d81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e3
				14d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d11
				07b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9
				ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319
				a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb7
				5d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e
				99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c74
				6cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc
				985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce
				3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abe
				d4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81
				279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d
				10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b
				2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0
				1558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e
				99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d7
				2d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99b
				cb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc
				321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985
				580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc
				0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4d
				a8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279
				df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10d
				d3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac
				80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155
				8455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a
				830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d9
				48d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7
				816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321
				f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580
				e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c3
				3c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da84
				80c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0
				795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3c
				d68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a
				09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155845
				5ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830
				e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d
				1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816
				f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f23
				19a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4f
				b75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c8
				6e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c
				746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795
				cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68
				ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09a
				bed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad
				81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e31
				4d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d110
				7b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9b
				a01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a
				5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75
				d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e9
				9bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746
				cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9
				85580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3
				dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed
				4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad812
				79df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d1
				0dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2
				ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01
				558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e9
				9a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72
				d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bc
				b7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc3
				21f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9855
				80e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0
				c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da
				8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279d
				f0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd
				3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac8
				0a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558
				455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a8
				30e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d94
				8d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb78
				16f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f
				2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e
				4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33
				c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da848
				0c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df07
				95cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd
				68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a0
				9abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455
				ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e
				314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1
				107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f
				9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f231
				9a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb
				75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86
				e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c7
				46cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795c
				c985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68c
				e3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09ab
				ed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8
				1279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314
				d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107
				b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba
				01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5
				e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d
				72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99
				bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746c
				c321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98
				5580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3d
				c0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4
				da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8127
				9df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10
				dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2a
				c80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015
				58455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99
				a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d
				948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb
				7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc32
				1f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98558
				0e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c
				33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8
				480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df
				0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3
				cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80
				a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015584
				55ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a83
				0e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948
				d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb781
				6f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2
				319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4
				fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c
				86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480
				c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df079
				5cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd6
				8ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09
				abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455a
				d81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e3
				14d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d11
				07b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9
				ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319
				a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb7
				5d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e
				99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c74
				6cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc
				985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce
				3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abe
				d4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81
				279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d
				10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b
				2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0
				1558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e
				99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d7
				2d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99b
				cb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc
				321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985
				580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc
				0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4d
				a8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279
				df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10d
				d3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac
				80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155
				8455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a
				830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d9
				48d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7
				816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321
				f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580
				e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c3
				3c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da84
				80c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0
				795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3c
				d68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a
				09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155845
				5ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830
				e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d
				1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816
				f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f23
				19a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4f
				b75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c8
				6e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c
				746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795
				cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68
				ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09a
				bed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad
				81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e31
				4d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d110
				7b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9b
				a01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a
				5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75
				d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e9
				9bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746
				cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9
				85580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3
				dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed
				4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad812
				79df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d1
				0dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2
				ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01
				558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e9
				9a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72
				d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bc
				b7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc3
				21f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9855
				80e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0
				c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da
				8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279d
				f0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd
				3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac8
				0a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558
				455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a8
				30e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d94
				8d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb78
				16f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f
				2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e
				4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33
				c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da848
				0c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df07
				95cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd
				68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a0
				9abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455
				ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e
				314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1
				107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f
				9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f231
				9a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb
				75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86
				e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c7
				46cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795c
				c985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68c
				e3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09ab
				ed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8
				1279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314
				d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107
				b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba
				01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5
				e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d
				72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99
				bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746c
				c321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98
				5580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3d
				c0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4
				da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8127
				9df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10
				dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2a
				c80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015
				58455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99
				a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d
				948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb
				7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc32
				1f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98558
				0e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c
				33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8
				480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df
				0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3
				cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80
				a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015584
				55ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a83
				0e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948
				d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb781
				6f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2
				319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4
				fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c
				86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480
				c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df079
				5cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd6
				8ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09
				abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455a
				d81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e3
				14d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d11
				07b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9
				ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319
				a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb7
				5d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e
				99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c74
				6cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc
				985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce
				3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abe
				d4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81
				279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d
				10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b
				2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0
				1558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e
				99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d7
				2d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99b
				cb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc
				321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985
				580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc
				0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4d
				a8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279
				df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10d
				d3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac
				80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155
				8455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a
				830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d9
				48d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7
				816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321
				f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580
				e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c3
				3c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da84
				80c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0
				795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3c
				d68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a
				09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155845
				5ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830
				e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d
				1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816
				f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f23
				19a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4f
				b75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c8
				6e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c
				746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795
				cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68
				ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09a
				bed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad
				81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e31
				4d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d110
				7b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9b
				a01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a
				5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75
				d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e9
				9bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746
				cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9
				85580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3
				dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed
				4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad812
				79df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d1
				0dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2
				ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01
				558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e9
				9a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72
				d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bc
				b7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc3
				21f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9855
				80e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0
				c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da
				8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279d
				f0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd
				3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac8
				0a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558
				455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a8
				30e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d94
				8d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb78
				16f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f
				2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e
				4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33
				c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da848
				0c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df07
				95cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd
				68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a0
				9abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455
				ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e
				314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1
				107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f
				9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f231
				9a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb
				75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86
				e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c7
				46cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795c
				c985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68c
				e3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09ab
				ed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8
				1279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314
				d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107
				b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba
				01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5
				e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d
				72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99
				bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746c
				c321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98
				5580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3d
				c0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4
				da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8127
				9df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10
				dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2a
				c80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015
				58455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99
				a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d
				948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb
				7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc32
				1f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98558
				0e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c
				33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8
				480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df
				0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3
				cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80
				a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015584
				55ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a83
				0e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948
				d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb781
				6f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2
				319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4
				fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c
				86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480
				c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df079
				5cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd6
				8ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09
				abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455a
				d81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e3
				14d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d11
				07b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9
				ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319
				a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb7
				5d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e
				99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c74
				6cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc
				985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce
				3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abe
				d4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81
				279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d
				10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b
				2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0
				1558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e
				99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d7
				2d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99b
				cb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc
				321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985
				580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc
				0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4d
				a8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279
				df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10d
				d3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac
				80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155
				8455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a
				830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d9
				48d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7
				816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321
				f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580
				e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c3
				3c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da84
				80c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0
				795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3c
				d68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a
				09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155845
				5ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830
				e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d
				1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816
				f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f23
				19a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4f
				b75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c8
				6e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c
				746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795
				cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68
				ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09a
				bed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad
				81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e31
				4d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d110
				7b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9b
				a01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a
				5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75
				d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e9
				9bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746
				cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9
				85580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3
				dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed
				4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad812
				79df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d1
				0dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2
				ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01
				558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e9
				9a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72
				d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bc
				b7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc3
				21f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9855
				80e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0
				c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da
				8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279d
				f0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd
				3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac8
				0a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558
				455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a8
				30e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d94
				8d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb78
				16f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f
				2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e
				4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33
				c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da848
				0c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df07
				95cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd
				68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a0
				9abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455
				ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e
				314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1
				107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f
				9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f231
				9a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb
				75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86
				e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c7
				46cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795c
				c985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68c
				e3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09ab
				ed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8
				1279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314
				d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107
				b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba
				01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5
				e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d
				72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99
				bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746c
				c321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98
				5580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3d
				c0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4
				da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8127
				9df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10
				dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2a
				c80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015
				58455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99
				a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d
				948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb
				7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc32
				1f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98558
				0e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c
				33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8
				480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df
				0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3
				cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80
				a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015584
				55ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a83
				0e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948
				d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb781
				6f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2
				319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4
				fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c
				86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480
				c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df079
				5cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd6
				8ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09
				abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455a
				d81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e3
				14d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d11
				07b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9
				ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319
				a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb7
				5d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e
				99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c74
				6cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc
				985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce
				3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abe
				d4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81
				279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d
				10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b
				2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0
				1558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e
				99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d7
				2d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99b
				cb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc
				321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985
				580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc
				0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4d
				a8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279
				df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10d
				d3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac
				80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155
				8455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a
				830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d9
				48d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7
				816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321
				f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580
				e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c3
				3c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da84
				80c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0
				795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3c
				d68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a
				09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155845
				5ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830
				e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d
				1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816
				f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f23
				19a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4f
				b75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c8
				6e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c
				746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795
				cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68
				ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09a
				bed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad
				81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e31
				4d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d110
				7b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9b
				a01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a
				5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75
				d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e9
				9bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746
				cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9
				85580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3
				dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed
				4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad812
				79df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d1
				0dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2
				ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01
				558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e9
				9a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72
				d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bc
				b7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc3
				21f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9855
				80e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0
				c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da
				8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279d
				f0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd
				3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac8
				0a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558
				455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a8
				30e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d94
				8d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb78
				16f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f
				2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e
				4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33
				c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da848
				0c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df07
				95cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd
				68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a0
				9abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455
				ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e
				314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1
				107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f
				9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f231
				9a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb
				75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86
				e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c7
				46cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795c
				c985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68c
				e3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09ab
				ed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8
				1279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314
				d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107
				b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba
				01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5
				e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d
				72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99
				bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746c
				c321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98
				5580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3d
				c0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4
				da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad8127
				9df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10
				dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2a
				c80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015
				58455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99
				a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d
				948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb
				7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc32
				1f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc98558
				0e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c
				33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8
				480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df
				0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3
				cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80
				a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba015584
				55ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a83
				0e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948
				d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb781
				6f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2
				319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4
				fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c
				86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480
				c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df079
				5cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd6
				8ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09
				abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455a
				d81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e3
				14d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d11
				07b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9
				ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319
				a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb7
				5d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e
				99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c74
				6cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc
				985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce
				3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abe
				d4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81
				279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d
				10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b
				2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0
				1558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e
				99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d7
				2d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99b
				cb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc
				321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985
				580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc
				0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4d
				a8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279
				df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10d
				d3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac
				80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155
				8455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a
				830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d9
				48d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7
				816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321
				f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580
				e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c3
				3c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da84
				80c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0
				795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3c
				d68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a
				09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba0155845
				5ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830
				e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d
				1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816
				f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f23
				19a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4f
				b75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c8
				6e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c
				746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795
				cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68
				ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09a
				bed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad
				81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e31
				4d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d110
				7b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9b
				a01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a
				5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75
				d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e9
				9bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746
				cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9
				85580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3
				dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed
				4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad812
				79df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d1
				0dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2
				ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01
				558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e9
				9a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72
				d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bc
				b7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc3
				21f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc9855
				80e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0
				c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da
				8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279d
				f0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd
				3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac8
				0a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558
				455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a8
				30e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d94
				8d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb78
				16f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f
				2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e
				4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33
				c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da848
				0c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df07
				95cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd
				68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a0
				9abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455
				ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f2319a5e99a830e
				314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01558455ad81279df0795cc985580e4fb75d72d948d1
				107b2ac80a09abed4da8480c746cc321f2319a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f
				9ba01558455ad81279df0795cc985580e4fb75d72d948d1107b2ac80a09abed4da8480c746cc321f231
				9a5e99a830e314d10dd3cd68ce3dc0c33c86e99bcb7816f9ba01"
			)
		);
	}
}
