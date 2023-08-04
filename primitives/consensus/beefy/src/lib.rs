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

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! Primitives for BEEFY protocol.
//!
//! The crate contains shared data types used by BEEFY protocol and documentation (in a form of
//! code) for building a BEEFY light client.
//!
//! BEEFY is a gadget that runs alongside another finality gadget (for instance GRANDPA).
//! For simplicity (and the initially intended use case) the documentation says GRANDPA in places
//! where a more abstract "Finality Gadget" term could be used, but there is no reason why BEEFY
//! wouldn't run with some other finality scheme.
//! BEEFY validator set is supposed to be tracking the Finality Gadget validator set, but note that
//! it will use a different set of keys. For Polkadot use case we plan to use `secp256k1` for BEEFY,
//! while GRANDPA uses `ed25519`.

mod commitment;
pub mod mmr;
mod payload;
#[cfg(feature = "std")]
mod test_utils;
pub mod witness;

pub use commitment::{Commitment, SignedCommitment, VersionedFinalityProof};
pub use payload::{known_payloads, BeefyPayloadId, Payload, PayloadProvider};
#[cfg(feature = "std")]
pub use test_utils::*;

use codec::{Codec, Decode, Encode};
use scale_info::TypeInfo;
use sp_application_crypto::RuntimeAppPublic;
use sp_core::H256;
use sp_runtime::traits::{Hash, Keccak256, NumberFor};
use sp_std::prelude::*;

/// Key type for BEEFY module.
pub const KEY_TYPE: sp_core::crypto::KeyTypeId = sp_application_crypto::key_types::BEEFY;

/// Trait representing BEEFY authority id, including custom signature verification.
///
/// Accepts custom hashing fn for the message and custom convertor fn for the signer.
pub trait BeefyAuthorityId<MsgHash: Hash>: RuntimeAppPublic {
	/// Verify a signature.
	///
	/// Return `true` if signature over `msg` is valid for this id.
	fn verify(&self, signature: &<Self as RuntimeAppPublic>::Signature, msg: &[u8]) -> bool;
}

/// BEEFY cryptographic types for ECDSA crypto
///
/// This module basically introduces four crypto types:
/// - `ecdsa_crypto::Pair`
/// - `ecdsa_crypto::Public`
/// - `ecdsa_crypto::Signature`
/// - `ecdsa_crypto::AuthorityId`
///
/// Your code should use the above types as concrete types for all crypto related
/// functionality.
pub mod ecdsa_crypto {
	use super::{BeefyAuthorityId, Hash, RuntimeAppPublic, KEY_TYPE as BEEFY_KEY_TYPE};
	use sp_application_crypto::{app_crypto, ecdsa};
	use sp_core::crypto::Wraps;
	app_crypto!(ecdsa, BEEFY_KEY_TYPE);

	/// Identity of a BEEFY authority using ECDSA as its crypto.
	pub type AuthorityId = Public;

	/// Signature for a BEEFY authority using ECDSA as its crypto.
	pub type AuthoritySignature = Signature;

	impl<MsgHash: Hash> BeefyAuthorityId<MsgHash> for AuthorityId
	where
		<MsgHash as Hash>::Output: Into<[u8; 32]>,
	{
		fn verify(&self, signature: &<Self as RuntimeAppPublic>::Signature, msg: &[u8]) -> bool {
			let msg_hash = <MsgHash as Hash>::hash(msg).into();
			match sp_io::crypto::secp256k1_ecdsa_recover_compressed(
				signature.as_inner_ref().as_ref(),
				&msg_hash,
			) {
				Ok(raw_pubkey) => raw_pubkey.as_ref() == AsRef::<[u8]>::as_ref(self),
				_ => false,
			}
		}
	}
}

/// BEEFY cryptographic types for BLS crypto
///
/// This module basically introduces four crypto types:
/// - `bls_crypto::Pair`
/// - `bls_crypto::Public`
/// - `bls_crypto::Signature`
/// - `bls_crypto::AuthorityId`
///
/// Your code should use the above types as concrete types for all crypto related
/// functionality.

#[cfg(feature = "bls-experimental")]
pub mod bls_crypto {
	use super::{BeefyAuthorityId, Hash, RuntimeAppPublic, KEY_TYPE as BEEFY_KEY_TYPE};
	use sp_application_crypto::{app_crypto, bls377};
	use sp_core::{bls377::Pair as BlsPair, crypto::Wraps, Pair as _};
	app_crypto!(bls377, BEEFY_KEY_TYPE);

	/// Identity of a BEEFY authority using BLS as its crypto.
	pub type AuthorityId = Public;

	/// Signature for a BEEFY authority using BLS as its crypto.
	pub type AuthoritySignature = Signature;

	impl<MsgHash: Hash> BeefyAuthorityId<MsgHash> for AuthorityId
	where
		<MsgHash as Hash>::Output: Into<[u8; 32]>,
	{
		fn verify(&self, signature: &<Self as RuntimeAppPublic>::Signature, msg: &[u8]) -> bool {
			// `w3f-bls` library uses IETF hashing standard and as such does not exposes
			// a choice of hash to field function.
			// We are directly calling into the library to avoid introducing new host call.
			// and because BeefyAuthorityId::verify is being called in the runtime so we don't have

			BlsPair::verify(signature.as_inner_ref(), msg, self.as_inner_ref())
		}
	}
}
/// The `ConsensusEngineId` of BEEFY.
pub const BEEFY_ENGINE_ID: sp_runtime::ConsensusEngineId = *b"BEEF";

/// Authority set id starts with zero at BEEFY pallet genesis.
pub const GENESIS_AUTHORITY_SET_ID: u64 = 0;

/// A typedef for validator set id.
pub type ValidatorSetId = u64;

/// A set of BEEFY authorities, a.k.a. validators.
#[derive(Decode, Encode, Debug, PartialEq, Clone, TypeInfo)]
pub struct ValidatorSet<AuthorityId> {
	/// Public keys of the validator set elements
	validators: Vec<AuthorityId>,
	/// Identifier of the validator set
	id: ValidatorSetId,
}

impl<AuthorityId> ValidatorSet<AuthorityId> {
	/// Return a validator set with the given validators and set id.
	pub fn new<I>(validators: I, id: ValidatorSetId) -> Option<Self>
	where
		I: IntoIterator<Item = AuthorityId>,
	{
		let validators: Vec<AuthorityId> = validators.into_iter().collect();
		if validators.is_empty() {
			// No validators; the set would be empty.
			None
		} else {
			Some(Self { validators, id })
		}
	}

	/// Return a reference to the vec of validators.
	pub fn validators(&self) -> &[AuthorityId] {
		&self.validators
	}

	/// Return the validator set id.
	pub fn id(&self) -> ValidatorSetId {
		self.id
	}

	/// Return the number of validators in the set.
	pub fn len(&self) -> usize {
		self.validators.len()
	}
}

/// The index of an authority.
pub type AuthorityIndex = u32;

/// The Hashing used within MMR.
pub type MmrHashing = Keccak256;
/// The type used to represent an MMR root hash.
pub type MmrRootHash = H256;

/// A consensus log item for BEEFY.
#[derive(Decode, Encode, TypeInfo)]
pub enum ConsensusLog<AuthorityId: Codec> {
	/// The authorities have changed.
	#[codec(index = 1)]
	AuthoritiesChange(ValidatorSet<AuthorityId>),
	/// Disable the authority with given index.
	#[codec(index = 2)]
	OnDisabled(AuthorityIndex),
	/// MMR root hash.
	#[codec(index = 3)]
	MmrRoot(MmrRootHash),
}

/// BEEFY vote message.
///
/// A vote message is a direct vote created by a BEEFY node on every voting round
/// and is gossiped to its peers.
#[derive(Clone, Debug, Decode, Encode, PartialEq, TypeInfo)]
pub struct VoteMessage<Number, Id, Signature> {
	/// Commit to information extracted from a finalized block
	pub commitment: Commitment<Number>,
	/// Node authority id
	pub id: Id,
	/// Node signature
	pub signature: Signature,
}

/// Proof of voter misbehavior on a given set id. Misbehavior/equivocation in
/// BEEFY happens when a voter votes on the same round/block for different payloads.
/// Proving is achieved by collecting the signed commitments of conflicting votes.
#[derive(Clone, Debug, Decode, Encode, PartialEq, TypeInfo)]
pub struct EquivocationProof<Number, Id, Signature> {
	/// The first vote in the equivocation.
	pub first: VoteMessage<Number, Id, Signature>,
	/// The second vote in the equivocation.
	pub second: VoteMessage<Number, Id, Signature>,
}

impl<Number, Id, Signature> EquivocationProof<Number, Id, Signature> {
	/// Returns the authority id of the equivocator.
	pub fn offender_id(&self) -> &Id {
		&self.first.id
	}
	/// Returns the round number at which the equivocation occurred.
	pub fn round_number(&self) -> &Number {
		&self.first.commitment.block_number
	}
	/// Returns the set id at which the equivocation occurred.
	pub fn set_id(&self) -> ValidatorSetId {
		self.first.commitment.validator_set_id
	}
}

/// Check a commitment signature by encoding the commitment and
/// verifying the provided signature using the expected authority id.
pub fn check_commitment_signature<Number, Id, MsgHash>(
	commitment: &Commitment<Number>,
	authority_id: &Id,
	signature: &<Id as RuntimeAppPublic>::Signature,
) -> bool
where
	Id: BeefyAuthorityId<MsgHash>,
	Number: Clone + Encode + PartialEq,
	MsgHash: Hash,
{
	let encoded_commitment = commitment.encode();
	BeefyAuthorityId::<MsgHash>::verify(authority_id, signature, &encoded_commitment)
}

/// Verifies the equivocation proof by making sure that both votes target
/// different blocks and that its signatures are valid.
pub fn check_equivocation_proof<Number, Id, MsgHash>(
	report: &EquivocationProof<Number, Id, <Id as RuntimeAppPublic>::Signature>,
) -> bool
where
	Id: BeefyAuthorityId<MsgHash> + PartialEq,
	Number: Clone + Encode + PartialEq,
	MsgHash: Hash,
{
	let first = &report.first;
	let second = &report.second;

	// if votes
	//   come from different authorities,
	//   are for different rounds,
	//   have different validator set ids,
	//   or both votes have the same commitment,
	//     --> the equivocation is invalid.
	if first.id != second.id ||
		first.commitment.block_number != second.commitment.block_number ||
		first.commitment.validator_set_id != second.commitment.validator_set_id ||
		first.commitment.payload == second.commitment.payload
	{
		return false
	}

	// check signatures on both votes are valid
	let valid_first = check_commitment_signature(&first.commitment, &first.id, &first.signature);
	let valid_second =
		check_commitment_signature(&second.commitment, &second.id, &second.signature);

	return valid_first && valid_second
}

/// New BEEFY validator set notification hook.
pub trait OnNewValidatorSet<AuthorityId> {
	/// Function called by the pallet when BEEFY validator set changes.
	fn on_new_validator_set(
		validator_set: &ValidatorSet<AuthorityId>,
		next_validator_set: &ValidatorSet<AuthorityId>,
	);
}

/// No-op implementation of [OnNewValidatorSet].
impl<AuthorityId> OnNewValidatorSet<AuthorityId> for () {
	fn on_new_validator_set(_: &ValidatorSet<AuthorityId>, _: &ValidatorSet<AuthorityId>) {}
}

/// An opaque type used to represent the key ownership proof at the runtime API
/// boundary. The inner value is an encoded representation of the actual key
/// ownership proof which will be parameterized when defining the runtime. At
/// the runtime API boundary this type is unknown and as such we keep this
/// opaque representation, implementors of the runtime API will have to make
/// sure that all usages of `OpaqueKeyOwnershipProof` refer to the same type.
#[derive(Decode, Encode, PartialEq, TypeInfo)]
pub struct OpaqueKeyOwnershipProof(Vec<u8>);
impl OpaqueKeyOwnershipProof {
	/// Create a new `OpaqueKeyOwnershipProof` using the given encoded
	/// representation.
	pub fn new(inner: Vec<u8>) -> OpaqueKeyOwnershipProof {
		OpaqueKeyOwnershipProof(inner)
	}

	/// Try to decode this `OpaqueKeyOwnershipProof` into the given concrete key
	/// ownership proof type.
	pub fn decode<T: Decode>(self) -> Option<T> {
		codec::Decode::decode(&mut &self.0[..]).ok()
	}
}

sp_api::decl_runtime_apis! {
	/// API necessary for BEEFY voters.
	#[api_version(3)]
	pub trait BeefyApi<AuthorityId> where
		AuthorityId : Codec + RuntimeAppPublic,
	{
		/// Return the block number where BEEFY consensus is enabled/started
		fn beefy_genesis() -> Option<NumberFor<Block>>;

		/// Return the current active BEEFY validator set
		fn validator_set() -> Option<ValidatorSet<AuthorityId>>;

		/// Submits an unsigned extrinsic to report an equivocation. The caller
		/// must provide the equivocation proof and a key ownership proof
		/// (should be obtained using `generate_key_ownership_proof`). The
		/// extrinsic will be unsigned and should only be accepted for local
		/// authorship (not to be broadcast to the network). This method returns
		/// `None` when creation of the extrinsic fails, e.g. if equivocation
		/// reporting is disabled for the given runtime (i.e. this method is
		/// hardcoded to return `None`). Only useful in an offchain context.
		fn submit_report_equivocation_unsigned_extrinsic(
			equivocation_proof:
				EquivocationProof<NumberFor<Block>, AuthorityId, <AuthorityId as RuntimeAppPublic>::Signature>,
			key_owner_proof: OpaqueKeyOwnershipProof,
		) -> Option<()>;

		/// Generates a proof of key ownership for the given authority in the
		/// given set. An example usage of this module is coupled with the
		/// session historical module to prove that a given authority key is
		/// tied to a given staking identity during a specific session. Proofs
		/// of key ownership are necessary for submitting equivocation reports.
		/// NOTE: even though the API takes a `set_id` as parameter the current
		/// implementations ignores this parameter and instead relies on this
		/// method being called at the correct block height, i.e. any point at
		/// which the given set id is live on-chain. Future implementations will
		/// instead use indexed data through an offchain worker, not requiring
		/// older states to be available.
		fn generate_key_ownership_proof(
			set_id: ValidatorSetId,
			authority_id: AuthorityId,
		) -> Option<OpaqueKeyOwnershipProof>;
	}

}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_application_crypto::ecdsa::{self, Public};
	use sp_core::{blake2_256, crypto::Wraps, keccak_256, Pair};
	use sp_runtime::traits::{BlakeTwo256, Keccak256};

	#[test]
	fn validator_set() {
		// Empty set not allowed.
		assert_eq!(ValidatorSet::<Public>::new(vec![], 0), None);

		let alice = ecdsa::Pair::from_string("//Alice", None).unwrap();
		let set_id = 0;
		let validators = ValidatorSet::<Public>::new(vec![alice.public()], set_id).unwrap();

		assert_eq!(validators.id(), set_id);
		assert_eq!(validators.validators(), &vec![alice.public()]);
	}

	#[test]
	fn ecdsa_beefy_verify_works() {
		let msg = &b"test-message"[..];
		let (pair, _) = ecdsa_crypto::Pair::generate();

		let keccak_256_signature: ecdsa_crypto::Signature =
			pair.as_inner_ref().sign_prehashed(&keccak_256(msg)).into();

		let blake2_256_signature: ecdsa_crypto::Signature =
			pair.as_inner_ref().sign_prehashed(&blake2_256(msg)).into();

		// Verification works if same hashing function is used when signing and verifying.
		assert!(BeefyAuthorityId::<Keccak256>::verify(&pair.public(), &keccak_256_signature, msg));
		assert!(BeefyAuthorityId::<BlakeTwo256>::verify(
			&pair.public(),
			&blake2_256_signature,
			msg
		));
		// Verification fails if distinct hashing functions are used when signing and verifying.
		assert!(!BeefyAuthorityId::<Keccak256>::verify(&pair.public(), &blake2_256_signature, msg));
		assert!(!BeefyAuthorityId::<BlakeTwo256>::verify(
			&pair.public(),
			&keccak_256_signature,
			msg
		));

		// Other public key doesn't work
		let (other_pair, _) = ecdsa_crypto::Pair::generate();
		assert!(!BeefyAuthorityId::<Keccak256>::verify(
			&other_pair.public(),
			&keccak_256_signature,
			msg,
		));
		assert!(!BeefyAuthorityId::<BlakeTwo256>::verify(
			&other_pair.public(),
			&blake2_256_signature,
			msg,
		));
	}

	#[test]
	#[cfg(feature = "bls-experimental")]
	fn bls_beefy_verify_works() {
		let msg = &b"test-message"[..];
		let (pair, _) = bls_crypto::Pair::generate();

		let signature: bls_crypto::Signature = pair.as_inner_ref().sign(&msg).into();

		// Verification works if same hashing function is used when signing and verifying.
		assert!(BeefyAuthorityId::<Keccak256>::verify(&pair.public(), &signature, msg));

		// Other public key doesn't work
		let (other_pair, _) = bls_crypto::Pair::generate();
		assert!(!BeefyAuthorityId::<Keccak256>::verify(&other_pair.public(), &signature, msg,));
	}
}
