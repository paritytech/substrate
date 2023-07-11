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

#[cfg(feature = "bls-experimental")]
use sp_core::{bls377, bls381};
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

	/// Returns all bls12-381 public keys for the given key type.
	#[cfg(feature = "bls-experimental")]
	fn bls381_public_keys(&self, id: KeyTypeId) -> Vec<bls381::Public>;

	/// Returns all bls12-377 public keys for the given key type.
	#[cfg(feature = "bls-experimental")]
	fn bls377_public_keys(&self, id: KeyTypeId) -> Vec<bls377::Public>;

	/// Generate a new bls381 key pair for the given key type and an optional seed.
	///
	/// Returns an `bls381::Public` key of the generated key pair or an `Err` if
	/// something failed during key generation.
	#[cfg(feature = "bls-experimental")]
	fn bls381_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> Result<bls381::Public, Error>;

	/// Generate a new bls377 key pair for the given key type and an optional seed.
	///
	/// Returns an `bls377::Public` key of the generated key pair or an `Err` if
	/// something failed during key generation.
	#[cfg(feature = "bls-experimental")]
	fn bls377_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> Result<bls377::Public, Error>;

	/// Generate a bls381 signature for a given message.
	///
	/// Receives [`KeyTypeId`] and a [`bls381::Public`] key to be able to map
	/// them to a private key that exists in the keystore.
	///
	/// Returns an [`bls381::Signature`] or `None` in case the given `key_type`
	/// and `public` combination doesn't exist in the keystore.
	/// An `Err` will be returned if generating the signature itself failed.
	#[cfg(feature = "bls-experimental")]
	fn bls381_sign(
		&self,
		key_type: KeyTypeId,
		public: &bls381::Public,
		msg: &[u8],
	) -> Result<Option<bls381::Signature>, Error>;

	/// Generate a bls377 signature for a given message.
	///
	/// Receives [`KeyTypeId`] and a [`bls377::Public`] key to be able to map
	/// them to a private key that exists in the keystore.
	///
	/// Returns an [`bls377::Signature`] or `None` in case the given `key_type`
	/// and `public` combination doesn't exist in the keystore.
	/// An `Err` will be returned if generating the signature itself failed.
	#[cfg(feature = "bls-experimental")]
	fn bls377_sign(
		&self,
		key_type: KeyTypeId,
		public: &bls377::Public,
		msg: &[u8],
	) -> Result<Option<bls377::Signature>, Error>;

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
	/// Schemes supported by the default trait implementation:
	/// - sr25519
	/// - ed25519
	/// - ecdsa
	/// - bls381
	/// - bls377
	///
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
			#[cfg(feature = "bls-experimental")]
			bls381::CRYPTO_ID => {
				let public = bls381::Public::from_slice(public)
					.map_err(|_| Error::ValidationError("Invalid public key format".into()))?;
				self.bls381_sign(id, &public, msg)?.map(|s| s.encode())
			},
			#[cfg(feature = "bls-experimental")]
			bls377::CRYPTO_ID => {
				let public = bls377::Public::from_slice(public)
					.map_err(|_| Error::ValidationError("Invalid public key format".into()))?;
				self.bls377_sign(id, &public, msg)?.map(|s| s.encode())
			},
			_ => return Err(Error::KeyNotSupported(id)),
		};
		Ok(signature)
	}
}

impl<T: Keystore + ?Sized> Keystore for Arc<T> {
	fn sr25519_public_keys(&self, key_type: KeyTypeId) -> Vec<sr25519::Public> {
		(**self).sr25519_public_keys(key_type)
	}

	fn sr25519_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> Result<sr25519::Public, Error> {
		(**self).sr25519_generate_new(key_type, seed)
	}

	fn sr25519_sign(
		&self,
		key_type: KeyTypeId,
		public: &sr25519::Public,
		msg: &[u8],
	) -> Result<Option<sr25519::Signature>, Error> {
		(**self).sr25519_sign(key_type, public, msg)
	}

	fn sr25519_vrf_sign(
		&self,
		key_type: KeyTypeId,
		public: &sr25519::Public,
		data: &sr25519::vrf::VrfSignData,
	) -> Result<Option<sr25519::vrf::VrfSignature>, Error> {
		(**self).sr25519_vrf_sign(key_type, public, data)
	}

	fn sr25519_vrf_output(
		&self,
		key_type: KeyTypeId,
		public: &sr25519::Public,
		input: &sr25519::vrf::VrfInput,
	) -> Result<Option<sr25519::vrf::VrfOutput>, Error> {
		(**self).sr25519_vrf_output(key_type, public, input)
	}

	fn ed25519_public_keys(&self, key_type: KeyTypeId) -> Vec<ed25519::Public> {
		(**self).ed25519_public_keys(key_type)
	}

	fn ed25519_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> Result<ed25519::Public, Error> {
		(**self).ed25519_generate_new(key_type, seed)
	}

	fn ed25519_sign(
		&self,
		key_type: KeyTypeId,
		public: &ed25519::Public,
		msg: &[u8],
	) -> Result<Option<ed25519::Signature>, Error> {
		(**self).ed25519_sign(key_type, public, msg)
	}

	fn ecdsa_public_keys(&self, key_type: KeyTypeId) -> Vec<ecdsa::Public> {
		(**self).ecdsa_public_keys(key_type)
	}

	fn ecdsa_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> Result<ecdsa::Public, Error> {
		(**self).ecdsa_generate_new(key_type, seed)
	}

	fn ecdsa_sign(
		&self,
		key_type: KeyTypeId,
		public: &ecdsa::Public,
		msg: &[u8],
	) -> Result<Option<ecdsa::Signature>, Error> {
		(**self).ecdsa_sign(key_type, public, msg)
	}

	fn ecdsa_sign_prehashed(
		&self,
		key_type: KeyTypeId,
		public: &ecdsa::Public,
		msg: &[u8; 32],
	) -> Result<Option<ecdsa::Signature>, Error> {
		(**self).ecdsa_sign_prehashed(key_type, public, msg)
	}

	fn insert(&self, key_type: KeyTypeId, suri: &str, public: &[u8]) -> Result<(), ()> {
		(**self).insert(key_type, suri, public)
	}

	fn keys(&self, key_type: KeyTypeId) -> Result<Vec<Vec<u8>>, Error> {
		(**self).keys(key_type)
	}

	fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool {
		(**self).has_keys(public_keys)
	}

	#[cfg(feature = "bls-experimental")]
	fn bls381_public_keys(&self, id: KeyTypeId) -> Vec<bls381::Public> {
		(**self).bls381_public_keys(id)
	}

	#[cfg(feature = "bls-experimental")]
	fn bls377_public_keys(&self, id: KeyTypeId) -> Vec<bls377::Public> {
		(**self).bls377_public_keys(id)
	}

	#[cfg(feature = "bls-experimental")]
	fn bls381_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> Result<bls381::Public, Error> {
		(**self).bls381_generate_new(key_type, seed)
	}

	#[cfg(feature = "bls-experimental")]
	fn bls377_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> Result<bls377::Public, Error> {
		(**self).bls377_generate_new(key_type, seed)
	}

	#[cfg(feature = "bls-experimental")]
	fn bls381_sign(
		&self,
		key_type: KeyTypeId,
		public: &bls381::Public,
		msg: &[u8],
	) -> Result<Option<bls381::Signature>, Error> {
		(**self).bls381_sign(key_type, public, msg)
	}

	#[cfg(feature = "bls-experimental")]
	fn bls377_sign(
		&self,
		key_type: KeyTypeId,
		public: &bls377::Public,
		msg: &[u8],
	) -> Result<Option<bls377::Signature>, Error> {
		(**self).bls377_sign(key_type, public, msg)
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
	///
	/// This is more performant as we don't need to wrap keystore in another [`Arc`].
	pub fn from(keystore: KeystorePtr) -> Self {
		Self(keystore)
	}

	/// Create a new instance of `KeystoreExt` using the given `keystore`.
	pub fn new<T: Keystore + 'static>(keystore: T) -> Self {
		Self(Arc::new(keystore))
	}
}
