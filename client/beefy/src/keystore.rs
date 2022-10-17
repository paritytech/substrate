// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use std::convert::{From, TryInto};

use sp_application_crypto::RuntimeAppPublic;
use sp_core::keccak_256;
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};

use log::warn;

use beefy_primitives::{
	crypto::{Public, Signature},
	KEY_TYPE,
};

use crate::error;

/// A BEEFY specific keystore implemented as a `Newtype`. This is basically a
/// wrapper around [`sp_keystore::SyncCryptoStore`] and allows to customize
/// common cryptographic functionality.
pub(crate) struct BeefyKeystore(Option<SyncCryptoStorePtr>);

impl BeefyKeystore {
	/// Check if the keystore contains a private key for one of the public keys
	/// contained in `keys`. A public key with a matching private key is known
	/// as a local authority id.
	///
	/// Return the public key for which we also do have a private key. If no
	/// matching private key is found, `None` will be returned.
	pub fn authority_id(&self, keys: &[Public]) -> Option<Public> {
		let store = self.0.clone()?;

		// we do check for multiple private keys as a key store sanity check.
		let public: Vec<Public> = keys
			.iter()
			.filter(|k| SyncCryptoStore::has_keys(&*store, &[(k.to_raw_vec(), KEY_TYPE)]))
			.cloned()
			.collect();

		if public.len() > 1 {
			warn!(target: "beefy", "🥩 Multiple private keys found for: {:?} ({})", public, public.len());
		}

		public.get(0).cloned()
	}

	/// Sign `message` with the `public` key.
	///
	/// Note that `message` usually will be pre-hashed before being signed.
	///
	/// Return the message signature or an error in case of failure.
	pub fn sign(&self, public: &Public, message: &[u8]) -> Result<Signature, error::Error> {
		let store = self.0.clone().ok_or_else(|| error::Error::Keystore("no Keystore".into()))?;

		let msg = keccak_256(message);
		let public = public.as_ref();

		let sig = SyncCryptoStore::ecdsa_sign_prehashed(&*store, KEY_TYPE, public, &msg)
			.map_err(|e| error::Error::Keystore(e.to_string()))?
			.ok_or_else(|| error::Error::Signature("ecdsa_sign_prehashed() failed".to_string()))?;

		// check that `sig` has the expected result type
		let sig = sig.clone().try_into().map_err(|_| {
			error::Error::Signature(format!("invalid signature {:?} for key {:?}", sig, public))
		})?;

		Ok(sig)
	}

	/// Returns a vector of [`beefy_primitives::crypto::Public`] keys which are currently supported
	/// (i.e. found in the keystore).
	pub fn public_keys(&self) -> Result<Vec<Public>, error::Error> {
		let store = self.0.clone().ok_or_else(|| error::Error::Keystore("no Keystore".into()))?;

		let pk: Vec<Public> = SyncCryptoStore::ecdsa_public_keys(&*store, KEY_TYPE)
			.drain(..)
			.map(Public::from)
			.collect();

		Ok(pk)
	}

	/// Use the `public` key to verify that `sig` is a valid signature for `message`.
	///
	/// Return `true` if the signature is authentic, `false` otherwise.
	pub fn verify(public: &Public, sig: &Signature, message: &[u8]) -> bool {
		let msg = keccak_256(message);
		let sig = sig.as_ref();
		let public = public.as_ref();

		sp_core::ecdsa::Pair::verify_prehashed(sig, &msg, public)
	}
}

impl From<Option<SyncCryptoStorePtr>> for BeefyKeystore {
	fn from(store: Option<SyncCryptoStorePtr>) -> BeefyKeystore {
		BeefyKeystore(store)
	}
}

#[cfg(test)]
pub mod tests {
	use std::sync::Arc;

	use sc_keystore::LocalKeystore;
	use sp_core::{ecdsa, keccak_256, Pair};
	use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};

	use beefy_primitives::{crypto, KEY_TYPE};

	use super::BeefyKeystore;
	use crate::error::Error;

	/// Set of test accounts using [`beefy_primitives::crypto`] types.
	#[allow(missing_docs)]
	#[derive(Debug, Clone, Copy, PartialEq, Eq, strum::Display, strum::EnumIter)]
	pub(crate) enum Keyring {
		Alice,
		Bob,
		Charlie,
		Dave,
		Eve,
		Ferdie,
		One,
		Two,
	}

	impl Keyring {
		/// Sign `msg`.
		pub fn sign(self, msg: &[u8]) -> crypto::Signature {
			let msg = keccak_256(msg);
			ecdsa::Pair::from(self).sign_prehashed(&msg).into()
		}

		/// Return key pair.
		pub fn pair(self) -> crypto::Pair {
			ecdsa::Pair::from_string(self.to_seed().as_str(), None).unwrap().into()
		}

		/// Return public key.
		pub fn public(self) -> crypto::Public {
			self.pair().public()
		}

		/// Return seed string.
		pub fn to_seed(self) -> String {
			format!("//{}", self)
		}
	}

	impl From<Keyring> for crypto::Pair {
		fn from(k: Keyring) -> Self {
			k.pair()
		}
	}

	impl From<Keyring> for ecdsa::Pair {
		fn from(k: Keyring) -> Self {
			k.pair().into()
		}
	}

	fn keystore() -> SyncCryptoStorePtr {
		Arc::new(LocalKeystore::in_memory())
	}

	#[test]
	fn verify_should_work() {
		let msg = keccak_256(b"I am Alice!");
		let sig = Keyring::Alice.sign(b"I am Alice!");

		assert!(ecdsa::Pair::verify_prehashed(
			&sig.clone().into(),
			&msg,
			&Keyring::Alice.public().into(),
		));

		// different public key -> fail
		assert!(!ecdsa::Pair::verify_prehashed(
			&sig.clone().into(),
			&msg,
			&Keyring::Bob.public().into(),
		));

		let msg = keccak_256(b"I am not Alice!");

		// different msg -> fail
		assert!(
			!ecdsa::Pair::verify_prehashed(&sig.into(), &msg, &Keyring::Alice.public().into(),)
		);
	}

	#[test]
	fn pair_works() {
		let want = crypto::Pair::from_string("//Alice", None).expect("Pair failed").to_raw_vec();
		let got = Keyring::Alice.pair().to_raw_vec();
		assert_eq!(want, got);

		let want = crypto::Pair::from_string("//Bob", None).expect("Pair failed").to_raw_vec();
		let got = Keyring::Bob.pair().to_raw_vec();
		assert_eq!(want, got);

		let want = crypto::Pair::from_string("//Charlie", None).expect("Pair failed").to_raw_vec();
		let got = Keyring::Charlie.pair().to_raw_vec();
		assert_eq!(want, got);

		let want = crypto::Pair::from_string("//Dave", None).expect("Pair failed").to_raw_vec();
		let got = Keyring::Dave.pair().to_raw_vec();
		assert_eq!(want, got);

		let want = crypto::Pair::from_string("//Eve", None).expect("Pair failed").to_raw_vec();
		let got = Keyring::Eve.pair().to_raw_vec();
		assert_eq!(want, got);

		let want = crypto::Pair::from_string("//Ferdie", None).expect("Pair failed").to_raw_vec();
		let got = Keyring::Ferdie.pair().to_raw_vec();
		assert_eq!(want, got);

		let want = crypto::Pair::from_string("//One", None).expect("Pair failed").to_raw_vec();
		let got = Keyring::One.pair().to_raw_vec();
		assert_eq!(want, got);

		let want = crypto::Pair::from_string("//Two", None).expect("Pair failed").to_raw_vec();
		let got = Keyring::Two.pair().to_raw_vec();
		assert_eq!(want, got);
	}

	#[test]
	fn authority_id_works() {
		let store = keystore();

		let alice: crypto::Public =
			SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&Keyring::Alice.to_seed()))
				.ok()
				.unwrap()
				.into();

		let bob = Keyring::Bob.public();
		let charlie = Keyring::Charlie.public();

		let store: BeefyKeystore = Some(store).into();

		let mut keys = vec![bob, charlie];

		let id = store.authority_id(keys.as_slice());
		assert!(id.is_none());

		keys.push(alice.clone());

		let id = store.authority_id(keys.as_slice()).unwrap();
		assert_eq!(id, alice);
	}

	#[test]
	fn sign_works() {
		let store = keystore();

		let alice: crypto::Public =
			SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&Keyring::Alice.to_seed()))
				.ok()
				.unwrap()
				.into();

		let store: BeefyKeystore = Some(store).into();

		let msg = b"are you involved or commited?";

		let sig1 = store.sign(&alice, msg).unwrap();
		let sig2 = Keyring::Alice.sign(msg);

		assert_eq!(sig1, sig2);
	}

	#[test]
	fn sign_error() {
		let store = keystore();

		let _ =
			SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&Keyring::Bob.to_seed()))
				.ok()
				.unwrap();

		let store: BeefyKeystore = Some(store).into();

		let alice = Keyring::Alice.public();

		let msg = b"are you involved or commited?";
		let sig = store.sign(&alice, msg).err().unwrap();
		let err = Error::Signature("ecdsa_sign_prehashed() failed".to_string());

		assert_eq!(sig, err);
	}

	#[test]
	fn sign_no_keystore() {
		let store: BeefyKeystore = None.into();

		let alice = Keyring::Alice.public();
		let msg = b"are you involved or commited";

		let sig = store.sign(&alice, msg).err().unwrap();
		let err = Error::Keystore("no Keystore".to_string());
		assert_eq!(sig, err);
	}

	#[test]
	fn verify_works() {
		let store = keystore();

		let alice: crypto::Public =
			SyncCryptoStore::ecdsa_generate_new(&*store, KEY_TYPE, Some(&Keyring::Alice.to_seed()))
				.ok()
				.unwrap()
				.into();

		let store: BeefyKeystore = Some(store).into();

		// `msg` and `sig` match
		let msg = b"are you involved or commited?";
		let sig = store.sign(&alice, msg).unwrap();
		assert!(BeefyKeystore::verify(&alice, &sig, msg));

		// `msg and `sig` don't match
		let msg = b"you are just involved";
		assert!(!BeefyKeystore::verify(&alice, &sig, msg));
	}

	// Note that we use keys with and without a seed for this test.
	#[test]
	fn public_keys_works() {
		const TEST_TYPE: sp_application_crypto::KeyTypeId =
			sp_application_crypto::KeyTypeId(*b"test");

		let store = keystore();

		let add_key = |key_type, seed: Option<&str>| {
			SyncCryptoStore::ecdsa_generate_new(&*store, key_type, seed).unwrap()
		};

		// test keys
		let _ = add_key(TEST_TYPE, Some(Keyring::Alice.to_seed().as_str()));
		let _ = add_key(TEST_TYPE, Some(Keyring::Bob.to_seed().as_str()));

		let _ = add_key(TEST_TYPE, None);
		let _ = add_key(TEST_TYPE, None);

		// BEEFY keys
		let _ = add_key(KEY_TYPE, Some(Keyring::Dave.to_seed().as_str()));
		let _ = add_key(KEY_TYPE, Some(Keyring::Eve.to_seed().as_str()));

		let key1: crypto::Public = add_key(KEY_TYPE, None).into();
		let key2: crypto::Public = add_key(KEY_TYPE, None).into();

		let store: BeefyKeystore = Some(store).into();

		let keys = store.public_keys().ok().unwrap();

		assert!(keys.len() == 4);
		assert!(keys.contains(&Keyring::Dave.public()));
		assert!(keys.contains(&Keyring::Eve.public()));
		assert!(keys.contains(&key1));
		assert!(keys.contains(&key2));
	}
}
