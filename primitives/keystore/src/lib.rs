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
	/// Returns all the sr25519 public keys for the given key type.
	fn sr25519_public_keys(&self, key_type: KeyTypeId) -> Vec<sr25519::Public>;

	/// Generate a new sr25519 key pair for the given key type and an optional seed.
	///
	/// Returns an `sr25519::Public` key of the generated key pair or an `Err` if
	/// something failed during key generation.
	fn sr25519_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> Result<sr25519::Public, Error>;

	/// Generate an sr25519 signature for a given message.
	///
	/// Receives [`KeyTypeId`] and an [`sr25519::Public`] key to be able to map
	/// them to a private key that exists in the keystore.
	///
	/// Returns an [`sr25519::Signature`] or `None` in case the given `key_type`
	/// and `public` combination doesn't exist in the keystore.
	/// An `Err` will be returned if generating the signature itself failed.
	fn sr25519_sign(
		&self,
		key_type: KeyTypeId,
		public: &sr25519::Public,
		msg: &[u8],
	) -> Result<Option<sr25519::Signature>, Error>;

	/// Generate an sr25519 VRF signature for the given data.
	///
	/// Receives [`KeyTypeId`] and an [`sr25519::Public`] key to be able to map
	/// them to a private key that exists in the keystore.
	///
	/// Returns `None` if the given `key_type` and `public` combination doesn't
	/// exist in the keystore or an `Err` when something failed.
	fn sr25519_vrf_sign(
		&self,
		key_type: KeyTypeId,
		public: &sr25519::Public,
		data: &sr25519::vrf::VrfSignData,
	) -> Result<Option<sr25519::vrf::VrfSignature>, Error>;

	/// Generate an sr25519 VRF output for a given input data.
	///
	/// Receives [`KeyTypeId`] and an [`sr25519::Public`] key to be able to map
	/// them to a private key that exists in the keystore.
	///
	/// Returns `None` if the given `key_type` and `public` combination doesn't
	/// exist in the keystore or an `Err` when something failed.
	fn sr25519_vrf_output(
		&self,
		key_type: KeyTypeId,
		public: &sr25519::Public,
		input: &sr25519::vrf::VrfInput,
	) -> Result<Option<sr25519::vrf::VrfOutput>, Error>;

	/// Returns all ed25519 public keys for the given key type.
	fn ed25519_public_keys(&self, key_type: KeyTypeId) -> Vec<ed25519::Public>;

	/// Generate a new ed25519 key pair for the given key type and an optional seed.
	///
	/// Returns an `ed25519::Public` key of the generated key pair or an `Err` if
	/// something failed during key generation.
	fn ed25519_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> Result<ed25519::Public, Error>;

	/// Generate an ed25519 signature for a given message.
	///
	/// Receives [`KeyTypeId`] and an [`ed25519::Public`] key to be able to map
	/// them to a private key that exists in the keystore.
	///
	/// Returns an [`ed25519::Signature`] or `None` in case the given `key_type`
	/// and `public` combination doesn't exist in the keystore.
	/// An `Err` will be returned if generating the signature itself failed.
	fn ed25519_sign(
		&self,
		key_type: KeyTypeId,
		public: &ed25519::Public,
		msg: &[u8],
	) -> Result<Option<ed25519::Signature>, Error>;

	/// Returns all ecdsa public keys for the given key type.
	fn ecdsa_public_keys(&self, key_type: KeyTypeId) -> Vec<ecdsa::Public>;

	/// Generate a new ecdsa key pair for the given key type and an optional seed.
	///
	/// Returns an `ecdsa::Public` key of the generated key pair or an `Err` if
	/// something failed during key generation.
	fn ecdsa_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> Result<ecdsa::Public, Error>;

	/// Generate an ecdsa signature for a given message.
	///
	/// Receives [`KeyTypeId`] and an [`ecdsa::Public`] key to be able to map
	/// them to a private key that exists in the keystore.
	///
	/// Returns an [`ecdsa::Signature`] or `None` in case the given `key_type`
	/// and `public` combination doesn't exist in the keystore.
	/// An `Err` will be returned if generating the signature itself failed.
	fn ecdsa_sign(
		&self,
		key_type: KeyTypeId,
		public: &ecdsa::Public,
		msg: &[u8],
	) -> Result<Option<ecdsa::Signature>, Error>;

	/// Generate an ecdsa signature for a given pre-hashed message.
	///
	/// Receives [`KeyTypeId`] and an [`ecdsa::Public`] key to be able to map
	/// them to a private key that exists in the keystore.
	///
	/// Returns an [`ecdsa::Signature`] or `None` in case the given `key_type`
	/// and `public` combination doesn't exist in the keystore.
	/// An `Err` will be returned if generating the signature itself failed.
	fn ecdsa_sign_prehashed(
		&self,
		key_type: KeyTypeId,
		public: &ecdsa::Public,
		msg: &[u8; 32],
	) -> Result<Option<ecdsa::Signature>, Error>;

	/// Insert a new secret key.
	fn insert(&self, key_type: KeyTypeId, suri: &str, public: &[u8]) -> Result<(), ()>;

	/// List all supported keys of a given type.
	///
	/// Returns a set of public keys the signer supports in raw format.
	fn keys(&self, key_type: KeyTypeId) -> Result<Vec<Vec<u8>>, Error>;

	/// Checks if the private keys for the given public key and key type combinations exist.
	///
	/// Returns `true` iff all private keys could be found.
	fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool;

	/// Convenience method to sign a message using the given key type and a raw public key
	/// for secret lookup.
	///
	/// The message is signed using the cryptographic primitive specified by `crypto_id`.
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
