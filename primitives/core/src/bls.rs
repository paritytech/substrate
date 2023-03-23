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

//! Simple BLS (Boneh–Lynn–Shacham) Signature API.

#[cfg(feature = "full_crypto")]
use sp_std::vec::Vec;

use crate::{
	crypto::ByteArray,
	hash::{H384, H768},
};
use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

#[cfg(feature = "std")]
use crate::crypto::Ss58Codec;
use crate::crypto::{
	CryptoType, CryptoTypeId, CryptoTypePublicPair, Derive, Public as TraitPublic, UncheckedFrom,
};
#[cfg(feature = "full_crypto")]
use crate::crypto::{DeriveJunction, Pair as TraitPair, SecretStringError};
#[cfg(feature = "std")]
use bip39::{Language, Mnemonic, MnemonicType};
use bls_like::EngineBLS;
#[cfg(feature = "full_crypto")]
use bls_like::{Keypair, Message, SerializableToBytes};
use core::convert::TryFrom;
#[cfg(feature = "std")]
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use sp_runtime_interface::pass_by::PassByInner;
use sp_std::{marker::PhantomData, ops::Deref};
#[cfg(feature = "std")]
use substrate_bip39::seed_from_entropy;

#[cfg(feature = "std")]
use hex;

/// BLS-377 specialized types
pub mod bls377 {
	use crate::crypto::CryptoTypeId;
	use bls_like::BLS377;

	/// An identifier used to match public keys against BLS12-377 keys
	pub const CRYPTO_ID: CryptoTypeId = CryptoTypeId(*b"bls7");

	/// BLS12-377 key pair.
	#[cfg(feature = "full_crypto")]
	pub type Pair = super::Pair<BLS377>;
	/// BLS12-377 public key.
	pub type Public = super::Public<BLS377>;
	/// BLS12-377 signature.
	pub type Signature = super::Signature<BLS377>;
}

/// BLS-381 specialized types
pub mod bls381 {
	use crate::crypto::CryptoTypeId;
	use bls_like::ZBLS;

	/// An identifier used to match public keys against BLS12-381 keys
	pub const CRYPTO_ID: CryptoTypeId = CryptoTypeId(*b"bls8");

	/// BLS12-381 key pair.
	#[cfg(feature = "full_crypto")]
	pub type Pair = super::Pair<ZBLS>;
	/// BLS12-381 public key.
	pub type Public = super::Public<ZBLS>;
	/// BLS12-381 signature.
	pub type Signature = super::Signature<ZBLS>;
}

trait BlsBound: EngineBLS + Send + Sync + 'static {}

impl<T: EngineBLS + Send + Sync + 'static> BlsBound for T {}

// Secret key serialized side
#[cfg(feature = "full_crypto")]
const SECRET_KEY_SERIALIZED_SIZE: usize = 32;

// Public key serialized side
const PUBLIC_KEY_SERIALIZED_SIZE: usize = 48;

// Signature serialized size
const SIGNATURE_SERIALIZED_SIZE: usize = 96;

// TODO DAVXY REMOVE-ME (REMOVED FROM UPSTREAM)
/// Temporary crypto id
pub const TEMPORARY_CRYPTO_ID: CryptoTypeId = CryptoTypeId(*b"TEMP");

/// A secret seed.
///
/// It's not called a "secret key" because ring doesn't expose the secret keys
/// of the key pair (yeah, dumb); as such we're forced to remember the seed manually if we
/// will need it later (such as for HDKD).
#[cfg(feature = "full_crypto")]
type Seed = [u8; SECRET_KEY_SERIALIZED_SIZE];

/// A public key.
#[derive(Copy, Encode, Decode, MaxEncodedLen, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct Public<T> {
	inner: [u8; PUBLIC_KEY_SERIALIZED_SIZE],
	_phantom: PhantomData<fn() -> T>,
}

impl<T> Clone for Public<T> {
	fn clone(&self) -> Self {
		Self { inner: self.inner.clone(), _phantom: PhantomData }
	}
}

impl<T> PartialEq for Public<T> {
	fn eq(&self, other: &Self) -> bool {
		self.inner == other.inner
	}
}

impl<T> Eq for Public<T> {}

impl<T> PartialOrd for Public<T> {
	fn partial_cmp(&self, other: &Self) -> Option<sp_std::cmp::Ordering> {
		self.inner.partial_cmp(&other.inner)
	}
}

impl<T> Ord for Public<T> {
	fn cmp(&self, other: &Self) -> sp_std::cmp::Ordering {
		self.inner.cmp(&other.inner)
	}
}

#[cfg(feature = "full_crypto")]
impl<T> sp_std::hash::Hash for Public<T> {
	fn hash<H: sp_std::hash::Hasher>(&self, state: &mut H) {
		self.inner.hash(state)
	}
}

impl<T> Public<T> {
	/// A new instance from the given PUBLIC_KEY_SERIALIZED_SIZE-byte `data`.
	///
	/// NOTE: No checking goes on to ensure this is a real public key. Only use it if
	/// you are certain that the array actually is a pubkey. GIGO!
	pub fn from_raw(data: [u8; PUBLIC_KEY_SERIALIZED_SIZE]) -> Self {
		Public { inner: data, _phantom: PhantomData }
	}

	/// A new instance from an H384.
	///
	/// NOTE: No checking goes on to ensure this is a real public key. Only use it if
	/// you are certain that the array actually is a pubkey. GIGO!
	pub fn from_h384(x: H384) -> Self {
		Self::from_raw(x.into())
	}
}

impl<T> ByteArray for Public<T> {
	const LEN: usize = PUBLIC_KEY_SERIALIZED_SIZE;
}

impl<T> PassByInner for Public<T> {
	type Inner = [u8; PUBLIC_KEY_SERIALIZED_SIZE];

	fn into_inner(self) -> Self::Inner {
		self.inner
	}

	fn inner(&self) -> &Self::Inner {
		&self.inner
	}

	fn from_inner(inner: Self::Inner) -> Self {
		Self { inner, _phantom: PhantomData }
	}
}

impl<T> AsRef<[u8; PUBLIC_KEY_SERIALIZED_SIZE]> for Public<T> {
	fn as_ref(&self) -> &[u8; PUBLIC_KEY_SERIALIZED_SIZE] {
		&self.inner
	}
}

impl<T> AsRef<[u8]> for Public<T> {
	fn as_ref(&self) -> &[u8] {
		&self.inner[..]
	}
}

impl<T> AsMut<[u8]> for Public<T> {
	fn as_mut(&mut self) -> &mut [u8] {
		&mut self.inner[..]
	}
}

impl<T> Deref for Public<T> {
	type Target = [u8];

	fn deref(&self) -> &Self::Target {
		&self.inner
	}
}

impl<T> TryFrom<&[u8]> for Public<T> {
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() != PUBLIC_KEY_SERIALIZED_SIZE {
			return Err(())
		}
		let mut r = [0u8; PUBLIC_KEY_SERIALIZED_SIZE];
		r.copy_from_slice(data);
		Ok(Self::unchecked_from(r))
	}
}

impl<T> From<Public<T>> for [u8; PUBLIC_KEY_SERIALIZED_SIZE] {
	fn from(x: Public<T>) -> Self {
		x.inner
	}
}

#[cfg(feature = "full_crypto")]
impl<T: BlsBound> From<Pair<T>> for Public<T> {
	fn from(x: Pair<T>) -> Self {
		x.public()
	}
}

impl<T> From<Public<T>> for H384 {
	fn from(x: Public<T>) -> Self {
		x.inner.into()
	}
}

impl<T> UncheckedFrom<[u8; PUBLIC_KEY_SERIALIZED_SIZE]> for Public<T> {
	fn unchecked_from(x: [u8; PUBLIC_KEY_SERIALIZED_SIZE]) -> Self {
		Public::from_raw(x)
	}
}

impl<T> UncheckedFrom<H384> for Public<T> {
	fn unchecked_from(x: H384) -> Self {
		Public::from_h384(x)
	}
}

#[cfg(feature = "std")]
impl<T: BlsBound> std::str::FromStr for Public<T> {
	type Err = crate::crypto::PublicError;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Self::from_ss58check(s)
	}
}

#[cfg(feature = "std")]
impl<T: BlsBound> std::fmt::Display for Public<T> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.to_ss58check())
	}
}

#[cfg(feature = "std")]
impl<T: BlsBound> sp_std::fmt::Debug for Public<T> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		let s = self.to_ss58check();
		write!(f, "{} ({}...)", crate::hexdisplay::HexDisplay::from(&self.inner), &s[0..8])
	}
}

#[cfg(not(feature = "std"))]
impl<T> sp_std::fmt::Debug for Public<T> {
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

#[cfg(feature = "std")]
impl<T: BlsBound> Serialize for Public<T> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		serializer.serialize_str(&self.to_ss58check())
	}
}

#[cfg(feature = "std")]
impl<'de, T: BlsBound> Deserialize<'de> for Public<T> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		Public::from_ss58check(&String::deserialize(deserializer)?)
			.map_err(|e| de::Error::custom(format!("{:?}", e)))
	}
}

impl<T: BlsBound> TraitPublic for Public<T> {
	fn to_public_crypto_pair(&self) -> CryptoTypePublicPair {
		CryptoTypePublicPair(TEMPORARY_CRYPTO_ID, self.to_raw_vec())
	}
}

impl<T> Derive for Public<T> {}

impl<T> From<Public<T>> for CryptoTypePublicPair {
	fn from(key: Public<T>) -> Self {
		(&key).into()
	}
}

impl<T> From<&Public<T>> for CryptoTypePublicPair {
	fn from(key: &Public<T>) -> Self {
		CryptoTypePublicPair(TEMPORARY_CRYPTO_ID, key.to_raw_vec())
	}
}

impl<T: BlsBound> CryptoType for Public<T> {
	#[cfg(feature = "full_crypto")]
	type Pair = Pair<T>;
}

/// A generic BLS signature.
#[derive(Copy, Encode, Decode, MaxEncodedLen, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct Signature<T> {
	inner: [u8; SIGNATURE_SERIALIZED_SIZE],
	_phantom: PhantomData<fn() -> T>,
}

impl<T> Clone for Signature<T> {
	fn clone(&self) -> Self {
		Self { inner: self.inner.clone(), _phantom: PhantomData }
	}
}

impl<T> PartialEq for Signature<T> {
	fn eq(&self, other: &Self) -> bool {
		self.inner == other.inner
	}
}

impl<T> Eq for Signature<T> {}

#[cfg(feature = "full_crypto")]
impl<T> sp_std::hash::Hash for Signature<T> {
	fn hash<H: sp_std::hash::Hasher>(&self, state: &mut H) {
		self.inner.hash(state)
	}
}

impl<T> Signature<T> {
	/// A new instance from the given SIGNATURE_SERIALIZED_SIZE-byte `data`.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_raw(data: [u8; SIGNATURE_SERIALIZED_SIZE]) -> Self {
		Signature { inner: data, _phantom: PhantomData }
	}

	/// A new instance from the given slice that should be 64 bytes long.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_slice(data: &[u8]) -> Option<Self> {
		if data.len() != SIGNATURE_SERIALIZED_SIZE {
			return None
		}
		let mut r = [0u8; SIGNATURE_SERIALIZED_SIZE];
		r.copy_from_slice(data);
		Some(Signature::from_raw(r))
	}

	/// A new instance from an H768.
	///
	/// NOTE: No checking goes on to ensure this is a real signature. Only use it if
	/// you are certain that the array actually is a signature. GIGO!
	pub fn from_h768(hash: H768) -> Self {
		Signature::from_raw(hash.into())
	}
}

impl<T> TryFrom<&[u8]> for Signature<T> {
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() == SIGNATURE_SERIALIZED_SIZE {
			let mut inner = [0u8; SIGNATURE_SERIALIZED_SIZE];
			inner.copy_from_slice(data);
			Ok(Signature::from_raw(inner))
		} else {
			Err(())
		}
	}
}

#[cfg(feature = "std")]
impl<T> Serialize for Signature<T> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		serializer.serialize_str(&hex::encode(self.inner))
	}
}

#[cfg(feature = "std")]
impl<'de, T> Deserialize<'de> for Signature<T> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let signature_hex = hex::decode(&String::deserialize(deserializer)?)
			.map_err(|e| de::Error::custom(format!("{:?}", e)))?;
		Signature::try_from(signature_hex.as_ref())
			.map_err(|e| de::Error::custom(format!("{:?}", e)))
	}
}

impl<T> From<Signature<T>> for H768 {
	fn from(signature: Signature<T>) -> H768 {
		H768::from(signature.inner)
	}
}

impl<T> From<Signature<T>> for [u8; SIGNATURE_SERIALIZED_SIZE] {
	fn from(signature: Signature<T>) -> [u8; SIGNATURE_SERIALIZED_SIZE] {
		signature.inner
	}
}

impl<T> AsRef<[u8; SIGNATURE_SERIALIZED_SIZE]> for Signature<T> {
	fn as_ref(&self) -> &[u8; SIGNATURE_SERIALIZED_SIZE] {
		&self.inner
	}
}

impl<T> AsRef<[u8]> for Signature<T> {
	fn as_ref(&self) -> &[u8] {
		&self.inner[..]
	}
}

impl<T> AsMut<[u8]> for Signature<T> {
	fn as_mut(&mut self) -> &mut [u8] {
		&mut self.inner[..]
	}
}

impl<T> sp_std::fmt::Debug for Signature<T> {
	#[cfg(feature = "std")]
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "{}", crate::hexdisplay::HexDisplay::from(&self.inner))
	}

	#[cfg(not(feature = "std"))]
	fn fmt(&self, _: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		Ok(())
	}
}

impl<T> UncheckedFrom<[u8; SIGNATURE_SERIALIZED_SIZE]> for Signature<T> {
	fn unchecked_from(data: [u8; SIGNATURE_SERIALIZED_SIZE]) -> Self {
		Signature::from_raw(data)
	}
}

impl<T: BlsBound> CryptoType for Signature<T> {
	#[cfg(feature = "full_crypto")]
	type Pair = Pair<T>;
}

/// A key pair.
#[cfg(feature = "full_crypto")]
pub struct Pair<T: EngineBLS>(Keypair<T>);

#[cfg(feature = "full_crypto")]
impl<T: EngineBLS> Clone for Pair<T> {
	fn clone(&self) -> Self {
		Pair(self.0.clone())
	}
}

/// Derive a single hard junction.
#[cfg(feature = "full_crypto")]
fn derive_hard_junction(secret_seed: &Seed, cc: &[u8; 32]) -> Seed {
	("BLS12377HDKD", secret_seed, cc).using_encoded(sp_core_hashing::blake2_256)
}

/// An error when deriving a key.
#[cfg(feature = "full_crypto")]
pub enum DeriveError {
	/// A soft key was found in the path (and is unsupported).
	SoftKeyInPath,
}

#[cfg(feature = "full_crypto")]
impl<T: EngineBLS> Pair<T> {
	/// Get the seed for this key.
	pub fn seed(&self) -> Seed {
		self.0.secret.to_bytes()
	}

	// TODO DAVXY: is this required??? If yes add when it will be 😃
	// /// Exactly as `from_string` except that if no matches are found then, the the first 32
	// /// characters are taken (padded with spaces as necessary) and used as the MiniSecretKey.
	// #[cfg(feature = "std")]
	// pub fn from_legacy_string(s: &str, password_override: Option<&str>) -> Self {
	// 	Self::from_string(s, password_override).unwrap_or_else(|_| {
	// 		let mut padded_seed: Seed = [b' '; 32];
	// 		let len = s.len().min(32);
	// 		padded_seed[..len].copy_from_slice(&s.as_bytes()[..len]);
	// 		Self::from_seed(&padded_seed)
	// 	})
	// }
}

#[cfg(feature = "full_crypto")]
impl<T: BlsBound> TraitPair for Pair<T> {
	type Seed = Seed;
	type Public = Public<T>;
	type Signature = Signature<T>;
	// TODO DAVXY: this is not required to be an associated type...
	type DeriveError = DeriveError;

	/// Generate new secure (random) key pair and provide the recovery phrase.
	///
	/// You can recover the same key later with `from_phrase`.
	#[cfg(feature = "std")]
	fn generate_with_phrase(password: Option<&str>) -> (Self, String, Seed) {
		let mnemonic = Mnemonic::new(MnemonicType::Words12, Language::English);
		let phrase = mnemonic.phrase();
		let (pair, seed) = Self::from_phrase(phrase, password)
			.expect("All phrases generated by Mnemonic are valid; qed");
		(pair, phrase.to_owned(), seed)
	}

	/// Generate key pair from given recovery phrase and password.
	#[cfg(feature = "std")]
	fn from_phrase(
		phrase: &str,
		password: Option<&str>,
	) -> Result<(Self, Seed), SecretStringError> {
		let big_seed = seed_from_entropy(
			Mnemonic::from_phrase(phrase, Language::English)
				.map_err(|_| SecretStringError::InvalidPhrase)?
				.entropy(),
			password.unwrap_or(""),
		)
		.map_err(|_| SecretStringError::InvalidSeed)?;
		let mut seed = Seed::default();
		seed.copy_from_slice(&big_seed[0..32]);
		Self::from_seed_slice(&big_seed[0..32]).map(|x| (x, seed))
	}

	/// Make a new key pair from secret seed material.
	///
	/// You should never need to use this; generate(), generate_with_phrase
	fn from_seed(seed: &Seed) -> Self {
		Self::from_seed_slice(&seed[..]).expect("seed has valid length; qed")
	}

	/// Make a new key pair from secret seed material. The slice must be 32 bytes long or it
	/// will return `None`.
	///
	/// You should never need to use this; generate(), generate_with_phrase
	fn from_seed_slice(seed_slice: &[u8]) -> Result<Self, SecretStringError> {
		if seed_slice.len() != SECRET_KEY_SERIALIZED_SIZE {
			return Err(SecretStringError::InvalidSeedLength)
		}
		let secret = bls_like::SecretKey::from_seed(seed_slice);
		let public = secret.into_public();
		Ok(Pair(bls_like::Keypair { secret, public }))
	}

	/// Derive a child key from a series of given junctions.
	fn derive<Iter: Iterator<Item = DeriveJunction>>(
		&self,
		path: Iter,
		_seed: Option<Seed>,
	) -> Result<(Self, Option<Seed>), DeriveError> {
		let mut acc = self.0.secret.to_bytes();
		for j in path {
			match j {
				DeriveJunction::Soft(_cc) => return Err(DeriveError::SoftKeyInPath),
				DeriveJunction::Hard(cc) => acc = derive_hard_junction(&acc, &cc),
			}
		}
		Ok((Self::from_seed(&acc), Some(acc)))
	}

	/// Get the public key.
	fn public(&self) -> Self::Public {
		let mut raw = [0u8; PUBLIC_KEY_SERIALIZED_SIZE];
		let pk = self.0.public.to_bytes();
		raw.copy_from_slice(pk.as_slice());
		Self::Public::from_raw(raw)
	}

	/// Sign a message.
	fn sign(&self, message: &[u8]) -> Self::Signature {
		let mut mutable_self = self.clone();
		let r = mutable_self.0.sign(Message::new(b"", message)).to_bytes();
		Self::Signature::from_raw(r)
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	fn verify<M: AsRef<[u8]>>(sig: &Self::Signature, message: M, pubkey: &Self::Public) -> bool {
		Self::verify_weak(&sig.inner[..], message.as_ref(), pubkey)
	}

	/// Verify a signature on a message. Returns true if the signature is good.
	///
	/// This doesn't use the type system to ensure that `sig` and `pubkey` are the correct
	/// size. Use it only if you're coming from byte buffers and need the speed.
	fn verify_weak<P: AsRef<[u8]>, M: AsRef<[u8]>>(sig: &[u8], message: M, pubkey: P) -> bool {
		let pubkey_array: [u8; PUBLIC_KEY_SERIALIZED_SIZE] = match pubkey.as_ref().try_into() {
			Ok(pk) => pk,
			Err(_) => return false,
		};
		let public_key = match bls_like::PublicKey::<T>::from_bytes(&pubkey_array) {
			Ok(pk) => pk,
			Err(_) => return false,
		};

		let sig_array = match sig.try_into() {
			Ok(s) => s,
			Err(_) => return false,
		};
		let sig = match bls_like::Signature::from_bytes(sig_array) {
			Ok(s) => s,
			Err(_) => return false,
		};

		sig.verify(Message::new(b"", message.as_ref()), &public_key)
	}

	/// Return a vec filled with raw data.
	fn to_raw_vec(&self) -> Vec<u8> {
		self.seed().to_vec()
	}
}

#[cfg(feature = "full_crypto")]
impl<T: BlsBound> CryptoType for Pair<T> {
	type Pair = Pair<T>;
}

// Test set excercising the BLS12-377 implementation
#[cfg(test)]
mod test {
	use super::*;
	use crate::crypto::DEV_PHRASE;
	use bls377::{Pair, Public, Signature};
	use hex_literal::hex;

	#[test]
	fn default_phrase_should_be_used() {
		assert_eq!(
			Pair::from_string("//Alice///password", None).unwrap().public(),
			Pair::from_string(&format!("{}//Alice", DEV_PHRASE), Some("password"))
				.unwrap()
				.public(),
		);
	}

	//only passes if the seed = seed (mod ScalarField)
	#[test]
	fn seed_and_derive_should_work() {
		let seed = hex!("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f00");
		let pair = Pair::from_seed(&seed);
		// we are using hash to field so this is not going to work
		// assert_eq!(pair.seed(), seed);
		let path = vec![DeriveJunction::Hard([0u8; 32])];
		let derived = pair.derive(path.into_iter(), None).ok().unwrap().0;
		assert_eq!(
			derived.seed(),
			hex!("a4f2269333b3e87c577aa00c4a2cd650b3b30b2e8c286a47c251279ff3a26e0d")
		);
	}

	// TODO FIXME Is this supposed to be successful?
	// Where is the test vector defined?
	#[test]
	fn test_vector_should_work() {
		let pair = Pair::from_seed(&hex!(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
		));
		let public = pair.public();
		assert_eq!(
			public,
			Public::from_raw(hex!(
				"7a84ca8ce4c37c93c95ecee6a3c0c9a7b9c225093cf2f12dc4f69cbfb847ef9424a18f5755d5a742247d386ff2aabb80"
			))
		);
		let message = b"";
		let signature =
	hex!("0e5854002b249175764e463165aec0e38a46ddd44c2db29d6fec3022a3993b3390b001b53a04d155a4d216dd361df90087281be27c58ae22c7f1333820259ff5ae1b321126d1a001bf91ee088fb56ca9d4aa484d129ede7e701ced08df631581"
	);
		let signature = Signature::from_raw(signature);
		assert!(pair.sign(&message[..]) == signature);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

	// TODO FIXME Is this expected to be pass?
	// Where the test vectors were taken?
	#[test]
	fn test_vector_by_string_should_work() {
		let pair = Pair::from_string(
			"0x9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
			None,
		)
		.unwrap();
		let public = pair.public();
		assert_eq!(
			public,
			Public::from_raw(hex!(
				"6dc6be608fab3c6bd894a606be86db346cc170db85c733853a371f3db54ae1b12052c0888d472760c81b537572a26f00"
			))
		);
		let message = b"";
		let signature =
	hex!("9f7d07e0fdd6aa342f6defaade946b59bfeba8af45c243f86b208cd339b2c713421844e3007e0acafd0a529542ee050047b739fe5bfd311d884451542204e173d784e648eb55f4bd32da747f006120fadf4801c2b1c88f9745c50c2141b1d380"
	);
		let signature = Signature::from_raw(signature);
		assert!(pair.sign(&message[..]) == signature);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

	#[test]
	fn generated_pair_should_work() {
		let (pair, _) = Pair::generate();
		let public = pair.public();
		let message = b"Something important";
		let signature = pair.sign(&message[..]);
		assert!(Pair::verify(&signature, &message[..], &public));
		assert!(!Pair::verify(&signature, b"Something else", &public));
	}

	#[test]
	fn seeded_pair_should_work() {
		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let public = pair.public();
		assert_eq!(
			public,
			Public::from_raw(
				hex!(
				"754d2f2bbfa67df54d7e0e951979a18a1e0f45948857752cc2bac6bbb0b1d05e8e48bcc453920bf0c4bbd59932124801")
			)
		);
		let message =
	hex!("2f8c6129d816cf51c374bc7f08c3e63ed156cf78aefb4a6550d97b87997977ee00000000000000000200d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a4500000000000000"
	);
		let signature = pair.sign(&message[..]);
		println!("Correct signature: {:?}", signature);
		assert!(Pair::verify(&signature, &message[..], &public));
		assert!(!Pair::verify(&signature, "Other message", &public));
	}

	#[test]
	fn generate_with_phrase_recovery_possible() {
		let (pair1, phrase, _) = Pair::generate_with_phrase(None);
		let (pair2, _) = Pair::from_phrase(&phrase, None).unwrap();

		assert_eq!(pair1.public(), pair2.public());
	}

	#[test]
	fn generate_with_password_phrase_recovery_possible() {
		let (pair1, phrase, _) = Pair::generate_with_phrase(Some("password"));
		let (pair2, _) = Pair::from_phrase(&phrase, Some("password")).unwrap();

		assert_eq!(pair1.public(), pair2.public());
	}

	#[test]
	fn password_does_something() {
		let (pair1, phrase, _) = Pair::generate_with_phrase(Some("password"));
		let (pair2, _) = Pair::from_phrase(&phrase, None).unwrap();

		assert_ne!(pair1.public(), pair2.public());
	}

	#[test]
	fn ss58check_roundtrip_works() {
		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let public = pair.public();
		let s = public.to_ss58check();
		println!("Correct: {}", s);
		let cmp = Public::from_ss58check(&s).unwrap();
		assert_eq!(cmp, public);
	}

	#[test]
	fn signature_serialization_works() {
		let pair = Pair::from_seed(b"12345678901234567890123456789012");
		let message = b"Something important";
		let signature = pair.sign(&message[..]);
		let serialized_signature = serde_json::to_string(&signature).unwrap();
		// Signature is 96 bytes, so 192 chars + 2 quote chars
		assert_eq!(serialized_signature.len(), 194);
		let signature = serde_json::from_str(&serialized_signature).unwrap();
		assert!(Pair::verify(&signature, &message[..], &pair.public()));
	}

	#[test]
	fn signature_serialization_doesnt_panic() {
		fn deserialize_signature(text: &str) -> Result<Signature, serde_json::error::Error> {
			serde_json::from_str(text)
		}
		assert!(deserialize_signature("Not valid json.").is_err());
		assert!(deserialize_signature("\"Not an actual signature.\"").is_err());
		// Poorly-sized
		assert!(deserialize_signature("\"abc123\"").is_err());
	}
}
