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

use std::convert::TryInto;

use sp_application_crypto::RuntimeAppPublic;
use sp_core::keccak_256;
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};

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

		for key in keys {
			if SyncCryptoStore::has_keys(&*store, &[(key.to_raw_vec(), KEY_TYPE)]) {
				return Some(key.clone());
			}
		}

		None
	}

	/// Sign `message` with the `public` key.
	///
	/// Note that `message` usually will be pre-hashed before being singed.
	///
	/// Return the message signature or an error in case of failure.
	pub fn sign(&self, public: &Public, message: &[u8]) -> Result<Signature, error::Error> {
		let store = if let Some(store) = self.0.clone() {
			store
		} else {
			return Err(error::Error::Keystore("no Keystore".to_string()));
		};

		let msg = keccak_256(message);
		let public = public.as_ref();

		let sig = SyncCryptoStore::ecdsa_sign_prehashed(&*store, KEY_TYPE, public, &msg)
			.map_err(|e| error::Error::Keystore(e.to_string()))?
			.ok_or_else(|| error::Error::Signature("ecdsa_sign_prehashed() failed".to_string()))?;

		// check that `sig` has the expected result type
		let sig = sig
			.clone()
			.try_into()
			.map_err(|_| error::Error::Signature(format!("invalid signature {:?} for key {:?}", sig, public)))?;

		Ok(sig)
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
mod tests {
	#![allow(clippy::unit_cmp)]

	use sp_core::{keccak_256, Pair};
	use sp_keystore::{testing::KeyStore, SyncCryptoStore, SyncCryptoStorePtr};

	use beefy_primitives::{crypto, KEY_TYPE};

	use super::BeefyKeystore;
	use crate::error::Error;

	#[test]
	fn authority_id_works() {
		let store: SyncCryptoStorePtr = KeyStore::new().into();

		let alice = crypto::Pair::from_string("//Alice", None).unwrap();
		let _ = SyncCryptoStore::insert_unknown(&*store, KEY_TYPE, "//Alice", alice.public().as_ref()).unwrap();

		let bob = crypto::Pair::from_string("//Bob", None).unwrap();
		let charlie = crypto::Pair::from_string("//Charlie", None).unwrap();

		let store: BeefyKeystore = Some(store).into();

		let mut keys = vec![bob.public(), charlie.public()];

		let id = store.authority_id(keys.as_slice());
		assert!(id.is_none());

		keys.push(alice.public());

		let id = store.authority_id(keys.as_slice()).unwrap();
		assert_eq!(id, alice.public());
	}

	#[test]
	fn sign_works() {
		let store: SyncCryptoStorePtr = KeyStore::new().into();

		let suri = "//Alice";
		let pair = sp_core::ecdsa::Pair::from_string(suri, None).unwrap();

		let res = SyncCryptoStore::insert_unknown(&*store, KEY_TYPE, suri, pair.public().as_ref()).unwrap();
		assert_eq!((), res);

		let beefy_store: BeefyKeystore = Some(store.clone()).into();

		let msg = b"are you involved or commited?";
		let sig1 = beefy_store.sign(&pair.public().into(), msg).unwrap();

		let msg = keccak_256(b"are you involved or commited?");
		let sig2 = SyncCryptoStore::ecdsa_sign_prehashed(&*store, KEY_TYPE, &pair.public(), &msg)
			.unwrap()
			.unwrap();

		assert_eq!(sig1, sig2.into());
	}

	#[test]
	fn sign_error() {
		let store: SyncCryptoStorePtr = KeyStore::new().into();

		let bob = crypto::Pair::from_string("//Bob", None).unwrap();
		let res = SyncCryptoStore::insert_unknown(&*store, KEY_TYPE, "//Bob", bob.public().as_ref()).unwrap();
		assert_eq!((), res);

		let alice = crypto::Pair::from_string("//Alice", None).unwrap();

		let store: BeefyKeystore = Some(store).into();

		let msg = b"are you involved or commited?";
		let sig = store.sign(&alice.public(), msg).err().unwrap();
		let err = Error::Signature("ecdsa_sign_prehashed() failed".to_string());
		assert_eq!(sig, err);
	}

	#[test]
	fn sign_no_keystore() {
		let store: BeefyKeystore = None.into();

		let alice = crypto::Pair::from_string("//Alice", None).unwrap();
		let msg = b"are you involved or commited";

		let sig = store.sign(&alice.public(), msg).err().unwrap();
		let err = Error::Keystore("no Keystore".to_string());
		assert_eq!(sig, err);
	}

	#[test]
	fn verify_works() {
		let store: SyncCryptoStorePtr = KeyStore::new().into();

		let suri = "//Alice";
		let pair = crypto::Pair::from_string(suri, None).unwrap();

		let res = SyncCryptoStore::insert_unknown(&*store, KEY_TYPE, suri, pair.public().as_ref()).unwrap();
		assert_eq!((), res);

		let store: BeefyKeystore = Some(store).into();

		// `msg` and `sig` match
		let msg = b"are you involved or commited?";
		let sig = store.sign(&pair.public(), msg).unwrap();
		assert!(BeefyKeystore::verify(&pair.public(), &sig, msg));

		// `msg and `sig` don't match
		let msg = b"you are just involved";
		assert!(!BeefyKeystore::verify(&pair.public(), &sig, msg));
	}
}
