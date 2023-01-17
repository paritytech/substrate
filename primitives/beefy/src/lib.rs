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
pub mod witness;

pub use commitment::{Commitment, SignedCommitment, VersionedFinalityProof};
pub use payload::{known_payloads, BeefyPayloadId, Payload, PayloadProvider};

use codec::{Codec, Decode, Encode};
use scale_info::TypeInfo;
use sp_application_crypto::RuntimeAppPublic;
use sp_core::H256;
use sp_runtime::traits::Hash;
use sp_std::prelude::*;

/// Key type for BEEFY module.
pub const KEY_TYPE: sp_application_crypto::KeyTypeId = sp_application_crypto::KeyTypeId(*b"beef");

/// Trait representing BEEFY authority id, including custom signature verification.
///
/// Accepts custom hashing fn for the message and custom convertor fn for the signer.
pub trait BeefyAuthorityId<MsgHash: Hash>: RuntimeAppPublic {
	/// Verify a signature.
	///
	/// Return `true` if signature over `msg` is valid for this id.
	fn verify(&self, signature: &<Self as RuntimeAppPublic>::Signature, msg: &[u8]) -> bool;
}

/// BEEFY cryptographic types
///
/// This module basically introduces three crypto types:
/// - `crypto::Pair`
/// - `crypto::Public`
/// - `crypto::Signature`
///
/// Your code should use the above types as concrete types for all crypto related
/// functionality.
///
/// The current underlying crypto scheme used is ECDSA. This can be changed,
/// without affecting code restricted against the above listed crypto types.
pub mod crypto {
	use super::{BeefyAuthorityId, Hash, RuntimeAppPublic};
	use sp_application_crypto::{app_crypto, ecdsa};
	use sp_core::crypto::Wraps;
	app_crypto!(ecdsa, crate::KEY_TYPE);

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
#[derive(Debug, Decode, Encode, TypeInfo)]
pub struct VoteMessage<Number, Id, Signature> {
	/// Commit to information extracted from a finalized block
	pub commitment: Commitment<Number>,
	/// Node authority id
	pub id: Id,
	/// Node signature
	pub signature: Signature,
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

sp_api::decl_runtime_apis! {
	/// API necessary for BEEFY voters.
	pub trait BeefyApi
	{
		/// Return the current active BEEFY validator set
		fn validator_set() -> Option<ValidatorSet<crypto::AuthorityId>>;
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
	fn beefy_verify_works() {
		let msg = &b"test-message"[..];
		let (pair, _) = crypto::Pair::generate();

		let keccak_256_signature: crypto::Signature =
			pair.as_inner_ref().sign_prehashed(&keccak_256(msg)).into();

		let blake2_256_signature: crypto::Signature =
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
		let (other_pair, _) = crypto::Pair::generate();
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
}
