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

#[cfg(feature = "std")]
use crate::crypto::Ss58Codec;
use crate::crypto::{ByteArray, CryptoType, Derive, Public as TraitPublic, UncheckedFrom};
#[cfg(feature = "full_crypto")]
use crate::crypto::{DeriveError, DeriveJunction, Pair as TraitPair, SecretStringError};

#[cfg(feature = "full_crypto")]
use sp_std::vec::Vec;

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
#[cfg(feature = "std")]
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use w3f_bls::{DoublePublicKey, DoubleSignature, EngineBLS, SerializableToBytes, TinyBLS381};
#[cfg(feature = "full_crypto")]
use w3f_bls::{DoublePublicKeyScheme, Keypair, Message, SecretKey};

use sp_runtime_interface::pass_by::PassByInner;
use sp_std::{convert::TryFrom, marker::PhantomData, ops::Deref};

/// BLS-377 specialized types
pub mod bls377 {
	use crate::crypto::CryptoTypeId;
	use w3f_bls::TinyBLS377;

	/// An identifier used to match public keys against BLS12-377 keys
	pub const CRYPTO_ID: CryptoTypeId = CryptoTypeId(*b"bls7");

	/// BLS12-377 key pair.
	#[cfg(feature = "full_crypto")]
	pub type Pair = super::Pair<TinyBLS377>;
	/// BLS12-377 public key.
	pub type Public = super::Public<TinyBLS377>;
	/// BLS12-377 signature.
	pub type Signature = super::Signature<TinyBLS377>;

	impl super::HardJunctionId for TinyBLS377 {
		const ID: &'static str = "BLS12377HDKD";
	}
}

/// BLS-381 specialized types
pub mod bls381 {
	use crate::crypto::CryptoTypeId;
	use w3f_bls::TinyBLS381;

	/// An identifier used to match public keys against BLS12-381 keys
	pub const CRYPTO_ID: CryptoTypeId = CryptoTypeId(*b"bls8");

	/// BLS12-381 key pair.
	#[cfg(feature = "full_crypto")]
	pub type Pair = super::Pair<TinyBLS381>;
	/// BLS12-381 public key.
	pub type Public = super::Public<TinyBLS381>;
	/// BLS12-381 signature.
	pub type Signature = super::Signature<TinyBLS381>;

	impl super::HardJunctionId for TinyBLS381 {
		const ID: &'static str = "BLS12381HDKD";
	}
}

trait BlsBound: EngineBLS + HardJunctionId + Send + Sync + 'static {}

impl<T: EngineBLS + HardJunctionId + Send + Sync + 'static> BlsBound for T {}

// Secret key serialized size
#[cfg(feature = "full_crypto")]
const SECRET_KEY_SERIALIZED_SIZE: usize =
	<SecretKey<TinyBLS381> as SerializableToBytes>::SERIALIZED_BYTES_SIZE;

// Public key serialized size
const PUBLIC_KEY_SERIALIZED_SIZE: usize =
	<DoublePublicKey<TinyBLS381> as SerializableToBytes>::SERIALIZED_BYTES_SIZE;

// Signature serialized size
const SIGNATURE_SERIALIZED_SIZE: usize =
	<DoubleSignature<TinyBLS381> as SerializableToBytes>::SERIALIZED_BYTES_SIZE;

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
		Self { inner: self.inner, _phantom: PhantomData }
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

impl<T> UncheckedFrom<[u8; PUBLIC_KEY_SERIALIZED_SIZE]> for Public<T> {
	fn unchecked_from(data: [u8; PUBLIC_KEY_SERIALIZED_SIZE]) -> Self {
		Public { inner: data, _phantom: PhantomData }
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

impl<T: BlsBound> TraitPublic for Public<T> {}

impl<T> Derive for Public<T> {}

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
		Self { inner: self.inner, _phantom: PhantomData }
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

impl<T> TryFrom<&[u8]> for Signature<T> {
	type Error = ();

	fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
		if data.len() != SIGNATURE_SERIALIZED_SIZE {
			return Err(())
		}
		let mut inner = [0u8; SIGNATURE_SERIALIZED_SIZE];
		inner.copy_from_slice(data);
		Ok(Signature::unchecked_from(inner))
	}
}

#[cfg(feature = "std")]
impl<T> Serialize for Signature<T> {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
	{
		serializer.serialize_str(&array_bytes::bytes2hex("", self.as_ref()))
	}
}

#[cfg(feature = "std")]
impl<'de, T> Deserialize<'de> for Signature<T> {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		let signature_hex = array_bytes::hex2bytes(&String::deserialize(deserializer)?)
			.map_err(|e| de::Error::custom(format!("{:?}", e)))?;
		Signature::try_from(signature_hex.as_ref())
			.map_err(|e| de::Error::custom(format!("{:?}", e)))
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
		Signature { inner: data, _phantom: PhantomData }
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

trait HardJunctionId {
	const ID: &'static str;
}

/// Derive a single hard junction.
#[cfg(feature = "full_crypto")]
fn derive_hard_junction<T: HardJunctionId>(secret_seed: &Seed, cc: &[u8; 32]) -> Seed {
	(T::ID, secret_seed, cc).using_encoded(sp_core_hashing::blake2_256)
}

#[cfg(feature = "full_crypto")]
impl<T: EngineBLS> Pair<T> {}

#[cfg(feature = "full_crypto")]
impl<T: BlsBound> TraitPair for Pair<T> {
	type Seed = Seed;
	type Public = Public<T>;
	type Signature = Signature<T>;

	fn from_seed_slice(seed_slice: &[u8]) -> Result<Self, SecretStringError> {
		if seed_slice.len() != SECRET_KEY_SERIALIZED_SIZE {
			return Err(SecretStringError::InvalidSeedLength)
		}
		let secret = w3f_bls::SecretKey::from_seed(seed_slice);
		let public = secret.into_public();
		Ok(Pair(w3f_bls::Keypair { secret, public }))
	}

	fn derive<Iter: Iterator<Item = DeriveJunction>>(
		&self,
		path: Iter,
		_seed: Option<Seed>,
	) -> Result<(Self, Option<Seed>), DeriveError> {
		let mut acc: [u8; SECRET_KEY_SERIALIZED_SIZE] =
			self.0.secret.to_bytes().try_into().expect(
				"Secret key serializer returns a vector of SECRET_KEY_SERIALIZED_SIZE size",
			);
		for j in path {
			match j {
				DeriveJunction::Soft(_cc) => return Err(DeriveError::SoftKeyInPath),
				DeriveJunction::Hard(cc) => acc = derive_hard_junction::<T>(&acc, &cc),
			}
		}
		Ok((Self::from_seed(&acc), Some(acc)))
	}

	fn public(&self) -> Self::Public {
		let mut raw = [0u8; PUBLIC_KEY_SERIALIZED_SIZE];
		let pk = DoublePublicKeyScheme::into_double_public_key(&self.0).to_bytes();
		raw.copy_from_slice(pk.as_slice());
		Self::Public::unchecked_from(raw)
	}

	fn sign(&self, message: &[u8]) -> Self::Signature {
		let mut mutable_self = self.clone();
		let r: [u8; SIGNATURE_SERIALIZED_SIZE] =
			DoublePublicKeyScheme::sign(&mut mutable_self.0, &Message::new(b"", message))
				.to_bytes()
				.try_into()
				.expect("Signature serializer returns vectors of SIGNATURE_SERIALIZED_SIZE size");
		Self::Signature::unchecked_from(r)
	}

	fn verify<M: AsRef<[u8]>>(sig: &Self::Signature, message: M, pubkey: &Self::Public) -> bool {
		let pubkey_array: [u8; PUBLIC_KEY_SERIALIZED_SIZE] =
			match <[u8; PUBLIC_KEY_SERIALIZED_SIZE]>::try_from(pubkey.as_ref()) {
				Ok(pk) => pk,
				Err(_) => return false,
			};
		let public_key = match w3f_bls::double::DoublePublicKey::<T>::from_bytes(&pubkey_array) {
			Ok(pk) => pk,
			Err(_) => return false,
		};

		let sig_array = match sig.inner[..].try_into() {
			Ok(s) => s,
			Err(_) => return false,
		};
		let sig = match w3f_bls::double::DoubleSignature::from_bytes(sig_array) {
			Ok(s) => s,
			Err(_) => return false,
		};

		sig.verify(&Message::new(b"", message.as_ref()), &public_key)
	}

	/// Get the seed for this key.
	fn to_raw_vec(&self) -> Vec<u8> {
		self.0
			.secret
			.to_bytes()
			.try_into()
			.expect("Secret key serializer returns a vector of SECRET_KEY_SERIALIZED_SIZE size")
	}
}

#[cfg(feature = "full_crypto")]
impl<T: BlsBound> CryptoType for Pair<T> {
	type Pair = Pair<T>;
}

// Test set exercising the BLS12-377 implementation
#[cfg(test)]
mod test {
	use super::*;
	use crate::crypto::DEV_PHRASE;
	use bls377::{Pair, Signature};
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

	// Only passes if the seed = (seed mod ScalarField)
	#[test]
	fn seed_and_derive_should_work() {
		let seed = hex!("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f00");
		let pair = Pair::from_seed(&seed);
		// we are using hash to field so this is not going to work
		// assert_eq!(pair.seed(), seed);
		let path = vec![DeriveJunction::Hard([0u8; 32])];
		let derived = pair.derive(path.into_iter(), None).ok().unwrap().0;
		assert_eq!(
			derived.to_raw_vec(),
			hex!("a4f2269333b3e87c577aa00c4a2cd650b3b30b2e8c286a47c251279ff3a26e0d")
		);
	}

	#[test]
	fn test_vector_should_work() {
		let pair = Pair::from_seed(&hex!(
			"9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
		));
		let public = pair.public();
		assert_eq!(
			public,
			Public::unchecked_from(hex!(
				"7a84ca8ce4c37c93c95ecee6a3c0c9a7b9c225093cf2f12dc4f69cbfb847ef9424a18f5755d5a742247d386ff2aabb806bcf160eff31293ea9616976628f77266c8a8cc1d8753be04197bd6cdd8c5c87a148f782c4c1568d599b48833fd539001e580cff64bbc71850605433fcd051f3afc3b74819786f815ffb5272030a8d03e5df61e6183f8fd8ea85f26defa83400"
			))
		);
		let message = b"";
		let signature =
	hex!("d1e3013161991e142d8751017d4996209c2ff8a9ee160f373733eda3b4b785ba6edce9f45f87104bbe07aa6aa6eb2780aa705efb2c13d3b317d6409d159d23bdc7cdd5c2a832d1551cf49d811d49c901495e527dbd532e3a462335ce2686009104aba7bc11c5b22be78f3198d2727a0b"
	);
		let signature = Signature::unchecked_from(signature);
		assert!(pair.sign(&message[..]) == signature);
		assert!(Pair::verify(&signature, &message[..], &public));
	}

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
			Public::unchecked_from(hex!(
				"6dc6be608fab3c6bd894a606be86db346cc170db85c733853a371f3db54ae1b12052c0888d472760c81b537572a26f00db865e5963aef8634f9917571c51b538b564b2a9ceda938c8b930969ee3b832448e08e33a79e9ddd28af419a3ce45300f5dbc768b067781f44f3fe05a19e6b07b1c4196151ec3f8ea37e4f89a8963030d2101e931276bb9ebe1f20102239d780"
			))
		);
		let message = b"";
		let signature =
	hex!("bbb395bbdee1a35930912034f5fde3b36df2835a0536c865501b0675776a1d5931a3bea2e66eff73b2546c6af2061a8019223e4ebbbed661b2538e0f5823f2c708eb89c406beca8fcb53a5c13dbc7c0c42e4cf2be2942bba96ea29297915a06bd2b1b979c0e2ac8fd4ec684a6b5d110c"
	);
		let expected_signature = Signature::unchecked_from(signature);
		println!("signature is {:?}", pair.sign(&message[..]));
		let signature = pair.sign(&message[..]);
		assert!(signature == expected_signature);
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
			Public::unchecked_from(
				hex!(
				"754d2f2bbfa67df54d7e0e951979a18a1e0f45948857752cc2bac6bbb0b1d05e8e48bcc453920bf0c4bbd5993212480112a1fb433f04d74af0a8b700d93dc957ab3207f8d071e948f5aca1a7632c00bdf6d06be05b43e2e6216dccc8a5d55a0071cb2313cfd60b7e9114619cd17c06843b352f0b607a99122f6651df8f02e1ad3697bd208e62af047ddd7b942ba80080")
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
		// Signature is 112 bytes, hexify * 2, so 224  chars + 2 quote chars
		assert_eq!(serialized_signature.len(), 226);
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
