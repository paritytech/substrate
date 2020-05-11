// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

#[cfg(feature = "full_crypto")]
use sp_core::crypto::Pair;

use codec::Codec;
use sp_core::crypto::{KeyTypeId, CryptoType, CryptoTypeId, IsWrappedBy, Public};
use sp_std::{fmt::Debug, vec::Vec};

/// An application-specific key.
pub trait AppKey: 'static + Send + Sync + Sized + CryptoType + Clone {
	/// The corresponding type as a generic crypto type.
	type UntypedGeneric: IsWrappedBy<Self>;

	/// The corresponding public key type in this application scheme.
	type Public: AppPublic;

	/// The corresponding key pair type in this application scheme.
	#[cfg(feature = "full_crypto")]
	type Pair: AppPair;

	/// The corresponding signature type in this application scheme.
	type Signature: AppSignature;

	/// An identifier for this application-specific key type.
	const ID: KeyTypeId;
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
pub trait MaybeDebugHash: sp_std::hash::Hash  {}
#[cfg(all(not(feature = "std"), feature = "full_crypto"))]
impl<T: sp_std::hash::Hash> MaybeDebugHash for T {}

/// A application's public key.
pub trait AppPublic:
	AppKey + Public + Ord + PartialOrd + Eq + PartialEq + Debug + MaybeHash + codec::Codec
{
	/// The wrapped type which is just a plain instance of `Public`.
	type Generic:
		IsWrappedBy<Self> + Public + Ord + PartialOrd + Eq + PartialEq + Debug + MaybeHash + codec::Codec;
}

/// A application's key pair.
#[cfg(feature = "full_crypto")]
pub trait AppPair: AppKey + Pair<Public=<Self as AppKey>::Public> {
	/// The wrapped type which is just a plain instance of `Pair`.
	type Generic: IsWrappedBy<Self> + Pair<Public = <<Self as AppKey>::Public as AppPublic>::Generic>;
}

/// A application's signature.
pub trait AppSignature: AppKey + Eq + PartialEq + Debug + MaybeHash {
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
	type Signature: Codec + Debug + MaybeHash + Eq + PartialEq + Clone;

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

/// Something that bound to a fixed `RuntimeAppPublic`.
pub trait BoundToRuntimeAppPublic {
	/// The `RuntimeAppPublic` this type is bound to.
	type Public: RuntimeAppPublic;
}
