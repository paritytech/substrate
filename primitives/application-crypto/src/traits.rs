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

#[cfg(feature = "full_crypto")]
use sp_core::crypto::Pair;

use codec::Codec;
use sp_core::crypto::{CryptoType, CryptoTypeId, IsWrappedBy, KeyTypeId, Public};
use sp_std::{fmt::Debug, vec::Vec};

/// An application-specific cryptographic object.
///
/// Combines all the core types and constants that are defined by a particular
/// cryptographic scheme when it is used in a specific application domain.
///
/// Typically, the implementers of this trait are its associated types themselves.
/// This provides a convenient way to access generic information about the scheme
/// given any of the associated types.
pub trait AppCrypto: 'static + Send + Sync + Sized + CryptoType + Clone {
	/// Identifier for application-specific key type.
	const ID: KeyTypeId;

	/// Identifier of the crypto type of this application-specific key type.
	const CRYPTO_ID: CryptoTypeId;

	/// The corresponding public key type in this application scheme.
	type Public: AppPublic;

	/// The corresponding signature type in this application scheme.
	type Signature: AppSignature;

	/// The corresponding key pair type in this application scheme.
	#[cfg(feature = "full_crypto")]
	type Pair: AppPair;
}

/// Type which implements Hash in std, not when no-std (std variant).
#[cfg(any(feature = "std", feature = "full_crypto"))]
pub trait MaybeHash: sp_std::hash::Hash {}
#[cfg(any(feature = "std", feature = "full_crypto"))]
impl<T: sp_std::hash::Hash> MaybeHash for T {}

/// Type which implements Hash in std, not when no-std (no-std variant).
#[cfg(all(not(feature = "std"), not(feature = "full_crypto")))]
pub trait MaybeHash {}
#[cfg(all(not(feature = "std"), not(feature = "full_crypto")))]
impl<T> MaybeHash for T {}

/// Type which implements Debug and Hash in std, not when no-std (no-std variant with crypto).
#[cfg(all(not(feature = "std"), feature = "full_crypto"))]
pub trait MaybeDebugHash: sp_std::hash::Hash {}
#[cfg(all(not(feature = "std"), feature = "full_crypto"))]
impl<T: sp_std::hash::Hash> MaybeDebugHash for T {}

/// A application's public key.
pub trait AppPublic:
	AppCrypto + Public + Ord + PartialOrd + Eq + PartialEq + Debug + MaybeHash + codec::Codec
{
	/// The wrapped type which is just a plain instance of `Public`.
	type Generic: IsWrappedBy<Self>
		+ Public
		+ Ord
		+ PartialOrd
		+ Eq
		+ PartialEq
		+ Debug
		+ MaybeHash
		+ codec::Codec;
}

/// A application's key pair.
#[cfg(feature = "full_crypto")]
pub trait AppPair: AppCrypto + Pair<Public = <Self as AppCrypto>::Public> {
	/// The wrapped type which is just a plain instance of `Pair`.
	type Generic: IsWrappedBy<Self>
		+ Pair<Public = <<Self as AppCrypto>::Public as AppPublic>::Generic>
		+ Pair<Signature = <<Self as AppCrypto>::Signature as AppSignature>::Generic>;
}

/// A application's signature.
pub trait AppSignature: AppCrypto + Eq + PartialEq + Debug + MaybeHash {
	/// The wrapped type which is just a plain instance of `Signature`.
	type Generic: IsWrappedBy<Self> + Eq + PartialEq + Debug + MaybeHash;
}

/// A runtime interface for a public key.
pub trait RuntimePublic: Sized {
	/// The signature that will be generated when signing with the corresponding private key.
	type Signature: Codec + Debug + MaybeHash + Eq + PartialEq + Clone;

	/// Returns all public keys for the given key type in the keystore.
	fn all(key_type: KeyTypeId) -> crate::Vec<Self>;

	/// Generate a public/private pair for the given key type with an optional `seed` and
	/// store it in the keystore.
	///
	/// The `seed` needs to be valid utf8.
	///
	/// Returns the generated public key.
	fn generate_pair(key_type: KeyTypeId, seed: Option<Vec<u8>>) -> Self;

	/// Sign the given message with the corresponding private key of this public key.
	///
	/// The private key will be requested from the keystore using the given key type.
	///
	/// Returns the signature or `None` if the private key could not be found or some other error
	/// occurred.
	fn sign<M: AsRef<[u8]>>(&self, key_type: KeyTypeId, msg: &M) -> Option<Self::Signature>;

	/// Verify that the given signature matches the given message using this public key.
	fn verify<M: AsRef<[u8]>>(&self, msg: &M, signature: &Self::Signature) -> bool;

	/// Returns `Self` as raw vec.
	fn to_raw_vec(&self) -> Vec<u8>;
}

/// A runtime interface for an application's public key.
pub trait RuntimeAppPublic: Sized {
	/// An identifier for this application-specific key type.
	const ID: KeyTypeId;
	/// The identifier of the crypto type of this application-specific key type.
	const CRYPTO_ID: CryptoTypeId;

	/// The signature that will be generated when signing with the corresponding private key.
	type Signature: Codec + Debug + MaybeHash + Eq + PartialEq + Clone + scale_info::TypeInfo;

	/// Returns all public keys for this application in the keystore.
	fn all() -> crate::Vec<Self>;

	/// Generate a public/private pair with an optional `seed` and store it in the keystore.
	///
	/// The `seed` needs to be valid utf8.
	///
	/// Returns the generated public key.
	fn generate_pair(seed: Option<Vec<u8>>) -> Self;

	/// Sign the given message with the corresponding private key of this public key.
	///
	/// The private key will be requested from the keystore.
	///
	/// Returns the signature or `None` if the private key could not be found or some other error
	/// occurred.
	fn sign<M: AsRef<[u8]>>(&self, msg: &M) -> Option<Self::Signature>;

	/// Verify that the given signature matches the given message using this public key.
	fn verify<M: AsRef<[u8]>>(&self, msg: &M, signature: &Self::Signature) -> bool;

	/// Returns `Self` as raw vec.
	fn to_raw_vec(&self) -> Vec<u8>;
}

/// Something that bound to a fixed [`RuntimeAppPublic`].
pub trait BoundToRuntimeAppPublic {
	/// The [`RuntimeAppPublic`] this type is bound to.
	type Public: RuntimeAppPublic;
}
