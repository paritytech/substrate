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

//! Keystore traits
pub mod testing;
pub mod vrf;

use crate::vrf::{VRFSignature, VRFTranscriptData};
use sp_core::{
	crypto::{ByteArray, CryptoTypeId, KeyTypeId},
	ecdsa, ed25519, sr25519,
};
use std::sync::Arc;

/// Keystore error
#[derive(Debug, thiserror::Error)]
pub enum Error {
	/// Public key type is not supported
	#[error("Key not supported: {0:?}")]
	KeyNotSupported(KeyTypeId),
	/// Validation error
	#[error("Validation error: {0}")]
	ValidationError(String),
	/// Keystore unavailable
	#[error("Keystore unavailable")]
	Unavailable,
	/// Programming errors
	#[error("An unknown keystore error occurred: {0}")]
	Other(String),
}

/// Something that generates, stores and provides access to secret keys.
pub trait Keystore: Send + Sync {
	/// Returns all sr25519 public keys for the given key type.
	fn sr25519_public_keys(&self, id: KeyTypeId) -> Vec<sr25519::Public>;

	/// Generate a new sr25519 key pair for the given key type and an optional seed.
	///
	/// If the given seed is `Some(_)`, the key pair will only be stored in memory.
	///
	/// Returns the public key of the generated key pair.
	fn sr25519_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<sr25519::Public, Error>;

	/// TODO
	fn sr25519_sign(
		&self,
		id: KeyTypeId,
		public: &sr25519::Public,
		msg: &[u8],
	) -> Result<Option<sr25519::Signature>, Error>;

	/// Generate VRF signature  for given transcript data.
	///
	/// Receives KeyTypeId and Public key to be able to map
	/// them to a private key that exists in the keystore which
	/// is, in turn, used for signing the provided transcript.
	///
	/// Returns a result containing the signature data.
	/// Namely, VRFOutput and VRFProof which are returned
	/// inside the `VRFSignature` container struct.
	///
	/// This function will return `None` if the given `key_type` and `public` combination
	/// doesn't exist in the keystore or an `Err` when something failed.
	fn sr25519_vrf_sign(
		&self,
		key_type: KeyTypeId,
		public: &sr25519::Public,
		transcript_data: VRFTranscriptData,
	) -> Result<Option<VRFSignature>, Error>;

	/// Returns all ed25519 public keys for the given key type.
	fn ed25519_public_keys(&self, id: KeyTypeId) -> Vec<ed25519::Public>;

	/// Generate a new ed25519 key pair for the given key type and an optional seed.
	///
	/// If the given seed is `Some(_)`, the key pair will only be stored in memory.
	///
	/// Returns the public key of the generated key pair.
	fn ed25519_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<&str>,
	) -> Result<ed25519::Public, Error>;

	/// TODO
	fn ed25519_sign(
		&self,
		id: KeyTypeId,
		public: &ed25519::Public,
		msg: &[u8],
	) -> Result<Option<ed25519::Signature>, Error>;

	/// Returns all ecdsa public keys for the given key type.
	fn ecdsa_public_keys(&self, id: KeyTypeId) -> Vec<ecdsa::Public>;

	/// Generate a new ecdsa key pair for the given key type and an optional seed.
	///
	/// If the given seed is `Some(_)`, the key pair will only be stored in memory.
	///
	/// Returns the public key of the generated key pair.
	fn ecdsa_generate_new(&self, id: KeyTypeId, seed: Option<&str>)
		-> Result<ecdsa::Public, Error>;

	/// Generate an ECDSA signature for a given message.
	///
	/// Receives [`KeyTypeId`] and an [`ecdsa::Public`] key to be able to map
	/// them to a private key that exists in the keystore. This private key is,
	/// in turn, used for signing the provided pre-hashed message.
	///
	/// Returns an [`ecdsa::Signature`] or `None` in case the given `id` and
	/// `public` combination doesn't exist in the keystore. An `Err` will be
	/// returned if generating the signature itself failed.
	fn ecdsa_sign(
		&self,
		id: KeyTypeId,
		public: &ecdsa::Public,
		msg: &[u8],
	) -> Result<Option<ecdsa::Signature>, Error>;

	/// Generate an ECDSA signature for a given pre-hashed message.
	///
	/// Receives [`KeyTypeId`] and an [`ecdsa::Public`] key to be able to map
	/// them to a private key that exists in the keystore. This private key is,
	/// in turn, used for signing the provided pre-hashed message.
	///
	/// The `msg` argument provided should be a hashed message for which an
	/// ECDSA signature should be generated.
	///
	/// Returns an [`ecdsa::Signature`] or `None` in case the given `id` and
	/// `public` combination doesn't exist in the keystore. An `Err` will be
	/// returned if generating the signature itself failed.
	fn ecdsa_sign_prehashed(
		&self,
		id: KeyTypeId,
		public: &ecdsa::Public,
		msg: &[u8; 32],
	) -> Result<Option<ecdsa::Signature>, Error>;

	/// Insert a new secret key.
	fn insert(&self, key_type: KeyTypeId, suri: &str, public: &[u8]) -> Result<(), ()>;

	/// List all supported keys
	///
	/// Returns a set of public keys the signer supports.
	fn keys(&self, id: KeyTypeId) -> Result<Vec<Vec<u8>>, Error>;

	/// Checks if the private keys for the given public key and key type combinations exist.
	///
	/// Returns `true` iff all private keys could be found.
	fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool;

	/// Convenience method to sign a message using an opaque key type.
	///
	/// The message is signed using the cryptographic primitive specified by `KeyCryptoId`.
	///
	/// Schemes supported by the default trait implementation: sr25519, ed25519 and ecdsa.
	/// To support more schemes you can overwrite this method.
	///
	/// Returns the SCALE encoded signature if key is found and supported, `None` if the key doesn't
	/// exist or an error when something failed.
	fn sign_with(
		&self,
		id: KeyTypeId,
		crypto_id: CryptoTypeId,
		public: &[u8],
		msg: &[u8],
	) -> Result<Option<Vec<u8>>, Error> {
		use codec::Encode;

		let signature = match crypto_id {
			sr25519::CRYPTO_ID => {
				let public = sr25519::Public::from_slice(public)
					.map_err(|_| Error::ValidationError("Invalid public key format".into()))?;
				self.sr25519_sign(id, &public, msg)?.map(|s| s.encode())
			},
			ed25519::CRYPTO_ID => {
				let public = ed25519::Public::from_slice(public)
					.map_err(|_| Error::ValidationError("Invalid public key format".into()))?;
				self.ed25519_sign(id, &public, msg)?.map(|s| s.encode())
			},
			ecdsa::CRYPTO_ID => {
				let public = ecdsa::Public::from_slice(public)
					.map_err(|_| Error::ValidationError("Invalid public key format".into()))?;
				self.ecdsa_sign(id, &public, msg)?.map(|s| s.encode())
			},
			_ => return Err(Error::KeyNotSupported(id)),
		};
		Ok(signature)
	}
}

/// A shared pointer to a keystore implementation.
pub type KeystorePtr = Arc<dyn Keystore>;

sp_externalities::decl_extension! {
	/// The keystore extension to register/retrieve from the externalities.
	pub struct KeystoreExt(KeystorePtr);
}

impl KeystoreExt {
	/// Create a new instance of `KeystoreExt`
	pub fn new<T: Keystore + 'static>(keystore: T) -> Self {
		Self(Arc::new(keystore))
	}
}
