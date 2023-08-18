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

//! A crate which contains statement-store primitives.

use codec::{Decode, Encode};
use scale_info::TypeInfo;
use sp_application_crypto::RuntimeAppPublic;
#[cfg(feature = "std")]
use sp_core::Pair;
use sp_runtime_interface::pass_by::PassByCodec;
use sp_std::vec::Vec;

/// Statement topic.
pub type Topic = [u8; 32];
/// Decryption key identifier.
pub type DecryptionKey = [u8; 32];
/// Statement hash.
pub type Hash = [u8; 32];
/// Block hash.
pub type BlockHash = [u8; 32];
/// Account id
pub type AccountId = [u8; 32];
/// Statement channel.
pub type Channel = [u8; 32];

/// Total number of topic fields allowed.
pub const MAX_TOPICS: usize = 4;

#[cfg(feature = "std")]
pub use store_api::{
	Error, NetworkPriority, Result, StatementSource, StatementStore, SubmitResult,
};

#[cfg(feature = "std")]
mod ecies;
pub mod runtime_api;
#[cfg(feature = "std")]
mod store_api;

mod sr25519 {
	mod app_sr25519 {
		use sp_application_crypto::{app_crypto, key_types::STATEMENT, sr25519};
		app_crypto!(sr25519, STATEMENT);
	}
	pub type Public = app_sr25519::Public;
}

/// Statement-store specific ed25519 crypto primitives.
pub mod ed25519 {
	mod app_ed25519 {
		use sp_application_crypto::{app_crypto, ed25519, key_types::STATEMENT};
		app_crypto!(ed25519, STATEMENT);
	}
	/// Statement-store specific ed25519 public key.
	pub type Public = app_ed25519::Public;
	/// Statement-store specific ed25519 key pair.
	#[cfg(feature = "std")]
	pub type Pair = app_ed25519::Pair;
}

mod ecdsa {
	mod app_ecdsa {
		use sp_application_crypto::{app_crypto, ecdsa, key_types::STATEMENT};
		app_crypto!(ecdsa, STATEMENT);
	}
	pub type Public = app_ecdsa::Public;
}

/// Returns blake2-256 hash for the encoded statement.
#[cfg(feature = "std")]
pub fn hash_encoded(data: &[u8]) -> [u8; 32] {
	sp_core::hashing::blake2_256(data)
}

/// Statement proof.
#[derive(Encode, Decode, TypeInfo, sp_core::RuntimeDebug, Clone, PartialEq, Eq)]
pub enum Proof {
	/// Sr25519 Signature.
	Sr25519 {
		/// Signature.
		signature: [u8; 64],
		/// Public key.
		signer: [u8; 32],
	},
	/// Ed25519 Signature.
	Ed25519 {
		/// Signature.
		signature: [u8; 64],
		/// Public key.
		signer: [u8; 32],
	},
	/// Secp256k1 Signature.
	Secp256k1Ecdsa {
		/// Signature.
		signature: [u8; 65],
		/// Public key.
		signer: [u8; 33],
	},
	/// On-chain event proof.
	OnChain {
		/// Account identifier associated with the event.
		who: AccountId,
		/// Hash of block that contains the event.
		block_hash: BlockHash,
		/// Index of the event in the event list.
		event_index: u64,
	},
}

impl Proof {
	/// Return account id for the proof creator.
	pub fn account_id(&self) -> AccountId {
		match self {
			Proof::Sr25519 { signer, .. } => *signer,
			Proof::Ed25519 { signer, .. } => *signer,
			Proof::Secp256k1Ecdsa { signer, .. } =>
				<sp_runtime::traits::BlakeTwo256 as sp_core::Hasher>::hash(signer).into(),
			Proof::OnChain { who, .. } => *who,
		}
	}
}

/// Statement attributes. Each statement is a list of 0 or more fields. Fields may only appear once
/// and in the order declared here.
#[derive(Encode, Decode, TypeInfo, sp_core::RuntimeDebug, Clone, PartialEq, Eq)]
#[repr(u8)]
pub enum Field {
	/// Statement proof.
	AuthenticityProof(Proof) = 0,
	/// An identifier for the key that `Data` field may be decrypted with.
	DecryptionKey(DecryptionKey) = 1,
	/// Priority when competing with other messages from the same sender.
	Priority(u32) = 2,
	/// Account channel to use. Only one message per `(account, channel)` pair is allowed.
	Channel(Channel) = 3,
	/// First statement topic.
	Topic1(Topic) = 4,
	/// Second statement topic.
	Topic2(Topic) = 5,
	/// Third statement topic.
	Topic3(Topic) = 6,
	/// Fourth statement topic.
	Topic4(Topic) = 7,
	/// Additional data.
	Data(Vec<u8>) = 8,
}

impl Field {
	fn discriminant(&self) -> u8 {
		// This is safe for repr(u8)
		// see https://doc.rust-lang.org/reference/items/enumerations.html#pointer-casting
		unsafe { *(self as *const Self as *const u8) }
	}
}

/// Statement structure.
#[derive(TypeInfo, sp_core::RuntimeDebug, PassByCodec, Clone, PartialEq, Eq, Default)]
pub struct Statement {
	proof: Option<Proof>,
	decryption_key: Option<DecryptionKey>,
	channel: Option<Channel>,
	priority: Option<u32>,
	num_topics: u8,
	topics: [Topic; MAX_TOPICS],
	data: Option<Vec<u8>>,
}

impl Decode for Statement {
	fn decode<I: codec::Input>(input: &mut I) -> core::result::Result<Self, codec::Error> {
		// Encoding matches that of Vec<Field>. Basically this just means accepting that there
		// will be a prefix of vector length.
		let num_fields: codec::Compact<u32> = Decode::decode(input)?;
		let mut tag = 0;
		let mut statement = Statement::new();
		for i in 0..num_fields.into() {
			let field: Field = Decode::decode(input)?;
			if i > 0 && field.discriminant() <= tag {
				return Err("Invalid field order or duplicate fields".into())
			}
			tag = field.discriminant();
			match field {
				Field::AuthenticityProof(p) => statement.set_proof(p),
				Field::DecryptionKey(key) => statement.set_decryption_key(key),
				Field::Priority(p) => statement.set_priority(p),
				Field::Channel(c) => statement.set_channel(c),
				Field::Topic1(t) => statement.set_topic(0, t),
				Field::Topic2(t) => statement.set_topic(1, t),
				Field::Topic3(t) => statement.set_topic(2, t),
				Field::Topic4(t) => statement.set_topic(3, t),
				Field::Data(data) => statement.set_plain_data(data),
			}
		}
		Ok(statement)
	}
}

impl Encode for Statement {
	fn encode(&self) -> Vec<u8> {
		self.encoded(false)
	}
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// Result returned by `Statement::verify_signature`
pub enum SignatureVerificationResult {
	/// Signature is valid and matches this account id.
	Valid(AccountId),
	/// Signature has failed verification.
	Invalid,
	/// No signature in the proof or no proof.
	NoSignature,
}

impl Statement {
	/// Create a new empty statement with no proof.
	pub fn new() -> Statement {
		Default::default()
	}

	/// Create a new statement with a proof.
	pub fn new_with_proof(proof: Proof) -> Statement {
		let mut statement = Self::new();
		statement.set_proof(proof);
		statement
	}

	/// Sign with a key that matches given public key in the keystore.
	///
	/// Returns `true` if signing worked (private key present etc).
	///
	/// NOTE: This can only be called from the runtime.
	pub fn sign_sr25519_public(&mut self, key: &sr25519::Public) -> bool {
		let to_sign = self.signature_material();
		if let Some(signature) = key.sign(&to_sign) {
			let proof = Proof::Sr25519 {
				signature: signature.into_inner().into(),
				signer: key.clone().into_inner().into(),
			};
			self.set_proof(proof);
			true
		} else {
			false
		}
	}

	/// Sign with a given private key and add the signature proof field.
	#[cfg(feature = "std")]
	pub fn sign_sr25519_private(&mut self, key: &sp_core::sr25519::Pair) {
		let to_sign = self.signature_material();
		let proof =
			Proof::Sr25519 { signature: key.sign(&to_sign).into(), signer: key.public().into() };
		self.set_proof(proof);
	}

	/// Sign with a key that matches given public key in the keystore.
	///
	/// Returns `true` if signing worked (private key present etc).
	///
	/// NOTE: This can only be called from the runtime.
	pub fn sign_ed25519_public(&mut self, key: &ed25519::Public) -> bool {
		let to_sign = self.signature_material();
		if let Some(signature) = key.sign(&to_sign) {
			let proof = Proof::Ed25519 {
				signature: signature.into_inner().into(),
				signer: key.clone().into_inner().into(),
			};
			self.set_proof(proof);
			true
		} else {
			false
		}
	}

	/// Sign with a given private key and add the signature proof field.
	#[cfg(feature = "std")]
	pub fn sign_ed25519_private(&mut self, key: &sp_core::ed25519::Pair) {
		let to_sign = self.signature_material();
		let proof =
			Proof::Ed25519 { signature: key.sign(&to_sign).into(), signer: key.public().into() };
		self.set_proof(proof);
	}

	/// Sign with a key that matches given public key in the keystore.
	///
	/// Returns `true` if signing worked (private key present etc).
	///
	/// NOTE: This can only be called from the runtime.
	///
	/// Returns `true` if signing worked (private key present etc).
	///
	/// NOTE: This can only be called from the runtime.
	pub fn sign_ecdsa_public(&mut self, key: &ecdsa::Public) -> bool {
		let to_sign = self.signature_material();
		if let Some(signature) = key.sign(&to_sign) {
			let proof = Proof::Secp256k1Ecdsa {
				signature: signature.into_inner().into(),
				signer: key.clone().into_inner().0,
			};
			self.set_proof(proof);
			true
		} else {
			false
		}
	}

	/// Sign with a given private key and add the signature proof field.
	#[cfg(feature = "std")]
	pub fn sign_ecdsa_private(&mut self, key: &sp_core::ecdsa::Pair) {
		let to_sign = self.signature_material();
		let proof =
			Proof::Secp256k1Ecdsa { signature: key.sign(&to_sign).into(), signer: key.public().0 };
		self.set_proof(proof);
	}

	/// Check proof signature, if any.
	pub fn verify_signature(&self) -> SignatureVerificationResult {
		use sp_runtime::traits::Verify;

		match self.proof() {
			Some(Proof::OnChain { .. }) | None => SignatureVerificationResult::NoSignature,
			Some(Proof::Sr25519 { signature, signer }) => {
				let to_sign = self.signature_material();
				let signature = sp_core::sr25519::Signature(*signature);
				let public = sp_core::sr25519::Public(*signer);
				if signature.verify(to_sign.as_slice(), &public) {
					SignatureVerificationResult::Valid(*signer)
				} else {
					SignatureVerificationResult::Invalid
				}
			},
			Some(Proof::Ed25519 { signature, signer }) => {
				let to_sign = self.signature_material();
				let signature = sp_core::ed25519::Signature(*signature);
				let public = sp_core::ed25519::Public(*signer);
				if signature.verify(to_sign.as_slice(), &public) {
					SignatureVerificationResult::Valid(*signer)
				} else {
					SignatureVerificationResult::Invalid
				}
			},
			Some(Proof::Secp256k1Ecdsa { signature, signer }) => {
				let to_sign = self.signature_material();
				let signature = sp_core::ecdsa::Signature(*signature);
				let public = sp_core::ecdsa::Public(*signer);
				if signature.verify(to_sign.as_slice(), &public) {
					let sender_hash =
						<sp_runtime::traits::BlakeTwo256 as sp_core::Hasher>::hash(signer);
					SignatureVerificationResult::Valid(sender_hash.into())
				} else {
					SignatureVerificationResult::Invalid
				}
			},
		}
	}

	/// Calculate statement hash.
	#[cfg(feature = "std")]
	pub fn hash(&self) -> [u8; 32] {
		self.using_encoded(hash_encoded)
	}

	/// Returns a topic by topic index.
	pub fn topic(&self, index: usize) -> Option<Topic> {
		if index < self.num_topics as usize {
			Some(self.topics[index])
		} else {
			None
		}
	}

	/// Returns decryption key if any.
	pub fn decryption_key(&self) -> Option<DecryptionKey> {
		self.decryption_key
	}

	/// Convert to internal data.
	pub fn into_data(self) -> Option<Vec<u8>> {
		self.data
	}

	/// Get a reference to the statement proof, if any.
	pub fn proof(&self) -> Option<&Proof> {
		self.proof.as_ref()
	}

	/// Get proof account id, if any
	pub fn account_id(&self) -> Option<AccountId> {
		self.proof.as_ref().map(Proof::account_id)
	}

	/// Get plain data.
	pub fn data(&self) -> Option<&Vec<u8>> {
		self.data.as_ref()
	}

	/// Get plain data len.
	pub fn data_len(&self) -> usize {
		self.data().map_or(0, Vec::len)
	}

	/// Get channel, if any.
	pub fn channel(&self) -> Option<Channel> {
		self.channel
	}

	/// Get priority, if any.
	pub fn priority(&self) -> Option<u32> {
		self.priority
	}

	/// Return encoded fields that can be signed to construct or verify a proof
	fn signature_material(&self) -> Vec<u8> {
		self.encoded(true)
	}

	/// Remove the proof of this statement.
	pub fn remove_proof(&mut self) {
		self.proof = None;
	}

	/// Set statement proof. Any existing proof is overwritten.
	pub fn set_proof(&mut self, proof: Proof) {
		self.proof = Some(proof)
	}

	/// Set statement priority.
	pub fn set_priority(&mut self, priority: u32) {
		self.priority = Some(priority)
	}

	/// Set statement channel.
	pub fn set_channel(&mut self, channel: Channel) {
		self.channel = Some(channel)
	}

	/// Set topic by index. Does noting if index is over `MAX_TOPICS`.
	pub fn set_topic(&mut self, index: usize, topic: Topic) {
		if index < MAX_TOPICS {
			self.topics[index] = topic;
			self.num_topics = self.num_topics.max(index as u8 + 1);
		}
	}

	/// Set decryption key.
	pub fn set_decryption_key(&mut self, key: DecryptionKey) {
		self.decryption_key = Some(key);
	}

	/// Set unencrypted statement data.
	pub fn set_plain_data(&mut self, data: Vec<u8>) {
		self.data = Some(data)
	}

	fn encoded(&self, for_signing: bool) -> Vec<u8> {
		// Encoding matches that of Vec<Field>. Basically this just means accepting that there
		// will be a prefix of vector length.
		let num_fields = if !for_signing && self.proof.is_some() { 1 } else { 0 } +
			if self.decryption_key.is_some() { 1 } else { 0 } +
			if self.priority.is_some() { 1 } else { 0 } +
			if self.channel.is_some() { 1 } else { 0 } +
			if self.data.is_some() { 1 } else { 0 } +
			self.num_topics as u32;

		let mut output = Vec::new();
		// When encoding signature payload, the length prefix is omitted.
		// This is so that the signature for encoded statement can potentially be derived without
		// needing to re-encode the statement.
		if !for_signing {
			let compact_len = codec::Compact::<u32>(num_fields);
			compact_len.encode_to(&mut output);

			if let Some(proof) = &self.proof {
				0u8.encode_to(&mut output);
				proof.encode_to(&mut output);
			}
		}
		if let Some(decryption_key) = &self.decryption_key {
			1u8.encode_to(&mut output);
			decryption_key.encode_to(&mut output);
		}
		if let Some(priority) = &self.priority {
			2u8.encode_to(&mut output);
			priority.encode_to(&mut output);
		}
		if let Some(channel) = &self.channel {
			3u8.encode_to(&mut output);
			channel.encode_to(&mut output);
		}
		for t in 0..self.num_topics {
			(4u8 + t).encode_to(&mut output);
			self.topics[t as usize].encode_to(&mut output);
		}
		if let Some(data) = &self.data {
			8u8.encode_to(&mut output);
			data.encode_to(&mut output);
		}
		output
	}

	/// Encrypt give data with given key and store both in the statements.
	#[cfg(feature = "std")]
	pub fn encrypt(
		&mut self,
		data: &[u8],
		key: &sp_core::ed25519::Public,
	) -> core::result::Result<(), ecies::Error> {
		let encrypted = ecies::encrypt_ed25519(key, data)?;
		self.data = Some(encrypted);
		self.decryption_key = Some((*key).into());
		Ok(())
	}

	/// Decrypt data (if any) with the given private key.
	#[cfg(feature = "std")]
	pub fn decrypt_private(
		&self,
		key: &sp_core::ed25519::Pair,
	) -> core::result::Result<Option<Vec<u8>>, ecies::Error> {
		self.data.as_ref().map(|d| ecies::decrypt_ed25519(key, d)).transpose()
	}
}

#[cfg(test)]
mod test {
	use crate::{hash_encoded, Field, Proof, SignatureVerificationResult, Statement};
	use codec::{Decode, Encode};
	use sp_application_crypto::Pair;

	#[test]
	fn statement_encoding_matches_vec() {
		let mut statement = Statement::new();
		assert!(statement.proof().is_none());
		let proof = Proof::OnChain { who: [42u8; 32], block_hash: [24u8; 32], event_index: 66 };

		let decryption_key = [0xde; 32];
		let topic1 = [0x01; 32];
		let topic2 = [0x02; 32];
		let data = vec![55, 99];
		let priority = 999;
		let channel = [0xcc; 32];

		statement.set_proof(proof.clone());
		statement.set_decryption_key(decryption_key);
		statement.set_priority(priority);
		statement.set_channel(channel);
		statement.set_topic(0, topic1);
		statement.set_topic(1, topic2);
		statement.set_plain_data(data.clone());

		statement.set_topic(5, [0x55; 32]);
		assert_eq!(statement.topic(5), None);

		let fields = vec![
			Field::AuthenticityProof(proof.clone()),
			Field::DecryptionKey(decryption_key),
			Field::Priority(priority),
			Field::Channel(channel),
			Field::Topic1(topic1),
			Field::Topic2(topic2),
			Field::Data(data.clone()),
		];

		let encoded = statement.encode();
		assert_eq!(statement.hash(), hash_encoded(&encoded));
		assert_eq!(encoded, fields.encode());

		let decoded = Statement::decode(&mut encoded.as_slice()).unwrap();
		assert_eq!(decoded, statement);
	}

	#[test]
	fn decode_checks_fields() {
		let topic1 = [0x01; 32];
		let topic2 = [0x02; 32];
		let priority = 999;

		let fields = vec![
			Field::Priority(priority),
			Field::Topic1(topic1),
			Field::Topic1(topic1),
			Field::Topic2(topic2),
		]
		.encode();

		assert!(Statement::decode(&mut fields.as_slice()).is_err());

		let fields =
			vec![Field::Topic1(topic1), Field::Priority(priority), Field::Topic2(topic2)].encode();

		assert!(Statement::decode(&mut fields.as_slice()).is_err());
	}

	#[test]
	fn sign_and_verify() {
		let mut statement = Statement::new();
		statement.set_plain_data(vec![42]);

		let sr25519_kp = sp_core::sr25519::Pair::from_string("//Alice", None).unwrap();
		let ed25519_kp = sp_core::ed25519::Pair::from_string("//Alice", None).unwrap();
		let secp256k1_kp = sp_core::ecdsa::Pair::from_string("//Alice", None).unwrap();

		statement.sign_sr25519_private(&sr25519_kp);
		assert_eq!(
			statement.verify_signature(),
			SignatureVerificationResult::Valid(sr25519_kp.public().0)
		);

		statement.sign_ed25519_private(&ed25519_kp);
		assert_eq!(
			statement.verify_signature(),
			SignatureVerificationResult::Valid(ed25519_kp.public().0)
		);

		statement.sign_ecdsa_private(&secp256k1_kp);
		assert_eq!(
			statement.verify_signature(),
			SignatureVerificationResult::Valid(sp_core::hashing::blake2_256(
				&secp256k1_kp.public().0
			))
		);

		// set an invalid signature
		statement.set_proof(Proof::Sr25519 { signature: [0u8; 64], signer: [0u8; 32] });
		assert_eq!(statement.verify_signature(), SignatureVerificationResult::Invalid);

		statement.remove_proof();
		assert_eq!(statement.verify_signature(), SignatureVerificationResult::NoSignature);
	}

	#[test]
	fn encrypt_decrypt() {
		let mut statement = Statement::new();
		let (pair, _) = sp_core::ed25519::Pair::generate();
		let plain = b"test data".to_vec();

		//let sr25519_kp = sp_core::sr25519::Pair::from_string("//Alice", None).unwrap();
		statement.encrypt(&plain, &pair.public()).unwrap();
		assert_ne!(plain.as_slice(), statement.data().unwrap().as_slice());

		let decrypted = statement.decrypt_private(&pair).unwrap();
		assert_eq!(decrypted, Some(plain));
	}
}
