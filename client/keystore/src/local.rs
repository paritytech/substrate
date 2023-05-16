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
//
//! Local keystore implementation

use parking_lot::RwLock;
use sp_application_crypto::{AppCrypto, AppPair, IsWrappedBy};
#[cfg(feature = "bls-experimental")]
use sp_core::{bls377, bls381};
use sp_core::{
	crypto::{ByteArray, ExposeSecret, KeyTypeId, Pair as CorePair, SecretString, VrfSecret},
	ecdsa, ed25519, sr25519,
};
use sp_keystore::{Error as TraitError, Keystore, KeystorePtr};
use std::{
	collections::HashMap,
	fs::{self, File},
	io::Write,
	path::PathBuf,
	sync::Arc,
};

use crate::{Error, Result};

/// A local based keystore that is either memory-based or filesystem-based.
pub struct LocalKeystore(RwLock<KeystoreInner>);

impl LocalKeystore {
	/// Create a local keystore from filesystem.
	pub fn open<T: Into<PathBuf>>(path: T, password: Option<SecretString>) -> Result<Self> {
		let inner = KeystoreInner::open(path, password)?;
		Ok(Self(RwLock::new(inner)))
	}

	/// Create a local keystore in memory.
	pub fn in_memory() -> Self {
		let inner = KeystoreInner::new_in_memory();
		Self(RwLock::new(inner))
	}

	/// Get a key pair for the given public key.
	///
	/// Returns `Ok(None)` if the key doesn't exist, `Ok(Some(_))` if the key exists and
	/// `Err(_)` when something failed.
	pub fn key_pair<Pair: AppPair>(
		&self,
		public: &<Pair as AppCrypto>::Public,
	) -> Result<Option<Pair>> {
		self.0.read().key_pair::<Pair>(public)
	}

	fn public_keys<T: CorePair>(&self, key_type: KeyTypeId) -> Vec<T::Public> {
		self.0
			.read()
			.raw_public_keys(key_type)
			.map(|v| {
				v.into_iter().filter_map(|k| T::Public::from_slice(k.as_slice()).ok()).collect()
			})
			.unwrap_or_default()
	}

	fn generate_new<T: CorePair>(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<T::Public, TraitError> {
		let pair = match seed {
			Some(seed) => self.0.write().insert_ephemeral_from_seed_by_type::<T>(seed, key_type),
			None => self.0.write().generate_by_type::<T>(key_type),
		}
		.map_err(|e| -> TraitError { e.into() })?;
		Ok(pair.public())
	}

	fn sign<T: CorePair>(
		&self,
		key_type: KeyTypeId,
		public: &T::Public,
		msg: &[u8],
	) -> std::result::Result<Option<T::Signature>, TraitError> {
		let signature = self
			.0
			.read()
			.key_pair_by_type::<T>(public, key_type)?
			.map(|pair| pair.sign(msg));
		Ok(signature)
	}

	fn vrf_sign<T: CorePair + VrfSecret>(
		&self,
		key_type: KeyTypeId,
		public: &T::Public,
		data: &T::VrfSignData,
	) -> std::result::Result<Option<T::VrfSignature>, TraitError> {
		let sig = self
			.0
			.read()
			.key_pair_by_type::<T>(public, key_type)?
			.map(|pair| pair.vrf_sign(data));
		Ok(sig)
	}

	fn vrf_output<T: CorePair + VrfSecret>(
		&self,
		key_type: KeyTypeId,
		public: &T::Public,
		input: &T::VrfInput,
	) -> std::result::Result<Option<T::VrfOutput>, TraitError> {
		let preout = self
			.0
			.read()
			.key_pair_by_type::<T>(public, key_type)?
			.map(|pair| pair.vrf_output(input));
		Ok(preout)
	}
}

impl Keystore for LocalKeystore {
	fn sr25519_public_keys(&self, key_type: KeyTypeId) -> Vec<sr25519::Public> {
		self.public_keys::<sr25519::Pair>(key_type)
	}

	/// Generate a new pair compatible with the 'ed25519' signature scheme.
	///
	/// If `[seed]` is `Some` then the key will be ephemeral and stored in memory.
	fn sr25519_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<sr25519::Public, TraitError> {
		self.generate_new::<sr25519::Pair>(key_type, seed)
	}

	fn sr25519_sign(
		&self,
		key_type: KeyTypeId,
		public: &sr25519::Public,
		msg: &[u8],
	) -> std::result::Result<Option<sr25519::Signature>, TraitError> {
		self.sign::<sr25519::Pair>(key_type, public, msg)
	}

	fn sr25519_vrf_sign(
		&self,
		key_type: KeyTypeId,
		public: &sr25519::Public,
		data: &sr25519::vrf::VrfSignData,
	) -> std::result::Result<Option<sr25519::vrf::VrfSignature>, TraitError> {
		self.vrf_sign::<sr25519::Pair>(key_type, public, data)
	}

	fn sr25519_vrf_output(
		&self,
		key_type: KeyTypeId,
		public: &sr25519::Public,
		input: &sr25519::vrf::VrfInput,
	) -> std::result::Result<Option<sr25519::vrf::VrfOutput>, TraitError> {
		self.vrf_output::<sr25519::Pair>(key_type, public, input)
	}

	fn ed25519_public_keys(&self, key_type: KeyTypeId) -> Vec<ed25519::Public> {
		self.public_keys::<ed25519::Pair>(key_type)
	}

	/// Generate a new pair compatible with the 'sr25519' signature scheme.
	///
	/// If `[seed]` is `Some` then the key will be ephemeral and stored in memory.
	fn ed25519_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<ed25519::Public, TraitError> {
		self.generate_new::<ed25519::Pair>(key_type, seed)
	}

	fn ed25519_sign(
		&self,
		key_type: KeyTypeId,
		public: &ed25519::Public,
		msg: &[u8],
	) -> std::result::Result<Option<ed25519::Signature>, TraitError> {
		self.sign::<ed25519::Pair>(key_type, public, msg)
	}

	fn ecdsa_public_keys(&self, key_type: KeyTypeId) -> Vec<ecdsa::Public> {
		self.public_keys::<ecdsa::Pair>(key_type)
	}

	/// Generate a new pair compatible with the 'ecdsa' signature scheme.
	///
	/// If `[seed]` is `Some` then the key will be ephemeral and stored in memory.
	fn ecdsa_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<ecdsa::Public, TraitError> {
		self.generate_new::<ecdsa::Pair>(key_type, seed)
	}

	fn ecdsa_sign(
		&self,
		key_type: KeyTypeId,
		public: &ecdsa::Public,
		msg: &[u8],
	) -> std::result::Result<Option<ecdsa::Signature>, TraitError> {
		self.sign::<ecdsa::Pair>(key_type, public, msg)
	}

	fn ecdsa_sign_prehashed(
		&self,
		key_type: KeyTypeId,
		public: &ecdsa::Public,
		msg: &[u8; 32],
	) -> std::result::Result<Option<ecdsa::Signature>, TraitError> {
		let sig = self
			.0
			.read()
			.key_pair_by_type::<ecdsa::Pair>(public, key_type)?
			.map(|pair| pair.sign_prehashed(msg));
		Ok(sig)
	}

	#[cfg(feature = "bls-experimental")]
	fn bls381_public_keys(&self, key_type: KeyTypeId) -> Vec<bls381::Public> {
		self.public_keys::<bls381::Pair>(key_type)
	}

	#[cfg(feature = "bls-experimental")]
	/// Generate a new pair compatible with the 'bls381' signature scheme.
	///
	/// If `[seed]` is `Some` then the key will be ephemeral and stored in memory.
	fn bls381_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<bls381::Public, TraitError> {
		self.generate_new::<bls381::Pair>(key_type, seed)
	}

	#[cfg(feature = "bls-experimental")]
	fn bls381_sign(
		&self,
		key_type: KeyTypeId,
		public: &bls381::Public,
		msg: &[u8],
	) -> std::result::Result<Option<bls381::Signature>, TraitError> {
		self.sign::<bls381::Pair>(key_type, public, msg)
	}

	#[cfg(feature = "bls-experimental")]
	fn bls377_public_keys(&self, key_type: KeyTypeId) -> Vec<bls377::Public> {
		self.public_keys::<bls377::Pair>(key_type)
	}

	#[cfg(feature = "bls-experimental")]
	/// Generate a new pair compatible with the 'bls377' signature scheme.
	///
	/// If `[seed]` is `Some` then the key will be ephemeral and stored in memory.
	fn bls377_generate_new(
		&self,
		key_type: KeyTypeId,
		seed: Option<&str>,
	) -> std::result::Result<bls377::Public, TraitError> {
		self.generate_new::<bls377::Pair>(key_type, seed)
	}

	#[cfg(feature = "bls-experimental")]
	fn bls377_sign(
		&self,
		key_type: KeyTypeId,
		public: &bls377::Public,
		msg: &[u8],
	) -> std::result::Result<Option<bls377::Signature>, TraitError> {
		self.sign::<bls377::Pair>(key_type, public, msg)
	}

	fn insert(
		&self,
		key_type: KeyTypeId,
		suri: &str,
		public: &[u8],
	) -> std::result::Result<(), ()> {
		self.0.write().insert(key_type, suri, public).map_err(|_| ())
	}

	fn keys(&self, key_type: KeyTypeId) -> std::result::Result<Vec<Vec<u8>>, TraitError> {
		self.0.read().raw_public_keys(key_type).map_err(|e| e.into())
	}

	fn has_keys(&self, public_keys: &[(Vec<u8>, KeyTypeId)]) -> bool {
		public_keys
			.iter()
			.all(|(p, t)| self.0.read().key_phrase_by_type(p, *t).ok().flatten().is_some())
	}
}

impl Into<KeystorePtr> for LocalKeystore {
	fn into(self) -> KeystorePtr {
		Arc::new(self)
	}
}

/// A local key store.
///
/// Stores key pairs in a file system store + short lived key pairs in memory.
///
/// Every pair that is being generated by a `seed`, will be placed in memory.
struct KeystoreInner {
	path: Option<PathBuf>,
	/// Map over `(KeyTypeId, Raw public key)` -> `Key phrase/seed`
	additional: HashMap<(KeyTypeId, Vec<u8>), String>,
	password: Option<SecretString>,
}

impl KeystoreInner {
	/// Open the store at the given path.
	///
	/// Optionally takes a password that will be used to encrypt/decrypt the keys.
	fn open<T: Into<PathBuf>>(path: T, password: Option<SecretString>) -> Result<Self> {
		let path = path.into();
		fs::create_dir_all(&path)?;

		Ok(Self { path: Some(path), additional: HashMap::new(), password })
	}

	/// Get the password for this store.
	fn password(&self) -> Option<&str> {
		self.password.as_ref().map(|p| p.expose_secret()).map(|p| p.as_str())
	}

	/// Create a new in-memory store.
	fn new_in_memory() -> Self {
		Self { path: None, additional: HashMap::new(), password: None }
	}

	/// Get the key phrase for the given public key and key type from the in-memory store.
	fn get_additional_pair(&self, public: &[u8], key_type: KeyTypeId) -> Option<&String> {
		let key = (key_type, public.to_vec());
		self.additional.get(&key)
	}

	/// Insert the given public/private key pair with the given key type.
	///
	/// Does not place it into the file system store.
	fn insert_ephemeral_pair<Pair: CorePair>(
		&mut self,
		pair: &Pair,
		seed: &str,
		key_type: KeyTypeId,
	) {
		let key = (key_type, pair.public().to_raw_vec());
		self.additional.insert(key, seed.into());
	}

	/// Insert a new key with anonymous crypto.
	///
	/// Places it into the file system store, if a path is configured.
	fn insert(&self, key_type: KeyTypeId, suri: &str, public: &[u8]) -> Result<()> {
		if let Some(path) = self.key_file_path(public, key_type) {
			Self::write_to_file(path, suri)?;
		}

		Ok(())
	}

	/// Generate a new key.
	///
	/// Places it into the file system store, if a path is configured. Otherwise insert
	/// it into the memory cache only.
	fn generate_by_type<Pair: CorePair>(&mut self, key_type: KeyTypeId) -> Result<Pair> {
		let (pair, phrase, _) = Pair::generate_with_phrase(self.password());
		if let Some(path) = self.key_file_path(pair.public().as_slice(), key_type) {
			Self::write_to_file(path, &phrase)?;
		} else {
			self.insert_ephemeral_pair(&pair, &phrase, key_type);
		}

		Ok(pair)
	}

	/// Write the given `data` to `file`.
	fn write_to_file(file: PathBuf, data: &str) -> Result<()> {
		let mut file = File::create(file)?;

		#[cfg(target_family = "unix")]
		{
			use std::os::unix::fs::PermissionsExt;
			file.set_permissions(fs::Permissions::from_mode(0o600))?;
		}

		serde_json::to_writer(&file, data)?;
		file.flush()?;
		Ok(())
	}

	/// Create a new key from seed.
	///
	/// Does not place it into the file system store.
	fn insert_ephemeral_from_seed_by_type<Pair: CorePair>(
		&mut self,
		seed: &str,
		key_type: KeyTypeId,
	) -> Result<Pair> {
		let pair = Pair::from_string(seed, None).map_err(|_| Error::InvalidSeed)?;
		self.insert_ephemeral_pair(&pair, seed, key_type);
		Ok(pair)
	}

	/// Get the key phrase for a given public key and key type.
	fn key_phrase_by_type(&self, public: &[u8], key_type: KeyTypeId) -> Result<Option<String>> {
		if let Some(phrase) = self.get_additional_pair(public, key_type) {
			return Ok(Some(phrase.clone()))
		}

		let path = if let Some(path) = self.key_file_path(public, key_type) {
			path
		} else {
			return Ok(None)
		};

		if path.exists() {
			let file = File::open(path)?;

			serde_json::from_reader(&file).map_err(Into::into).map(Some)
		} else {
			Ok(None)
		}
	}

	/// Get a key pair for the given public key and key type.
	fn key_pair_by_type<Pair: CorePair>(
		&self,
		public: &Pair::Public,
		key_type: KeyTypeId,
	) -> Result<Option<Pair>> {
		let phrase = if let Some(p) = self.key_phrase_by_type(public.as_slice(), key_type)? {
			p
		} else {
			return Ok(None)
		};

		let pair = Pair::from_string(&phrase, self.password()).map_err(|_| Error::InvalidPhrase)?;

		if &pair.public() == public {
			Ok(Some(pair))
		} else {
			Err(Error::PublicKeyMismatch)
		}
	}

	/// Get the file path for the given public key and key type.
	///
	/// Returns `None` if the keystore only exists in-memory and there isn't any path to provide.
	fn key_file_path(&self, public: &[u8], key_type: KeyTypeId) -> Option<PathBuf> {
		let mut buf = self.path.as_ref()?.clone();
		let key_type = array_bytes::bytes2hex("", &key_type.0);
		let key = array_bytes::bytes2hex("", public);
		buf.push(key_type + key.as_str());
		Some(buf)
	}

	/// Returns a list of raw public keys filtered by `KeyTypeId`
	fn raw_public_keys(&self, key_type: KeyTypeId) -> Result<Vec<Vec<u8>>> {
		let mut public_keys: Vec<Vec<u8>> = self
			.additional
			.keys()
			.into_iter()
			.filter_map(|k| if k.0 == key_type { Some(k.1.clone()) } else { None })
			.collect();

		if let Some(path) = &self.path {
			for entry in fs::read_dir(&path)? {
				let entry = entry?;
				let path = entry.path();

				// skip directories and non-unicode file names (hex is unicode)
				if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
					match array_bytes::hex2bytes(name) {
						Ok(ref hex) if hex.len() > 4 => {
							if hex[0..4] != key_type.0 {
								continue
							}
							let public = hex[4..].to_vec();
							public_keys.push(public);
						},
						_ => continue,
					}
				}
			}
		}

		Ok(public_keys)
	}

	/// Get a key pair for the given public key.
	///
	/// Returns `Ok(None)` if the key doesn't exist, `Ok(Some(_))` if the key exists or `Err(_)`
	/// when something failed.
	pub fn key_pair<Pair: AppPair>(
		&self,
		public: &<Pair as AppCrypto>::Public,
	) -> Result<Option<Pair>> {
		self.key_pair_by_type::<Pair::Generic>(IsWrappedBy::from_ref(public), Pair::ID)
			.map(|v| v.map(Into::into))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_application_crypto::{ed25519, sr25519, AppPublic};
	use sp_core::{crypto::Ss58Codec, testing::SR25519, Pair};
	use std::{fs, str::FromStr};
	use tempfile::TempDir;

	const TEST_KEY_TYPE: KeyTypeId = KeyTypeId(*b"test");

	impl KeystoreInner {
		fn insert_ephemeral_from_seed<Pair: AppPair>(&mut self, seed: &str) -> Result<Pair> {
			self.insert_ephemeral_from_seed_by_type::<Pair::Generic>(seed, Pair::ID)
				.map(Into::into)
		}

		fn public_keys<Public: AppPublic>(&self) -> Result<Vec<Public>> {
			self.raw_public_keys(Public::ID).map(|v| {
				v.into_iter().filter_map(|k| Public::from_slice(k.as_slice()).ok()).collect()
			})
		}

		fn generate<Pair: AppPair>(&mut self) -> Result<Pair> {
			self.generate_by_type::<Pair::Generic>(Pair::ID).map(Into::into)
		}
	}

	#[test]
	fn basic_store() {
		let temp_dir = TempDir::new().unwrap();
		let mut store = KeystoreInner::open(temp_dir.path(), None).unwrap();

		assert!(store.public_keys::<ed25519::AppPublic>().unwrap().is_empty());

		let key: ed25519::AppPair = store.generate().unwrap();
		let key2: ed25519::AppPair = store.key_pair(&key.public()).unwrap().unwrap();

		assert_eq!(key.public(), key2.public());

		assert_eq!(store.public_keys::<ed25519::AppPublic>().unwrap()[0], key.public());
	}

	#[test]
	fn has_keys_works() {
		let temp_dir = TempDir::new().unwrap();
		let store = LocalKeystore::open(temp_dir.path(), None).unwrap();

		let key: ed25519::AppPair = store.0.write().generate().unwrap();
		let key2 = ed25519::Pair::generate().0;

		assert!(!store.has_keys(&[(key2.public().to_vec(), ed25519::AppPublic::ID)]));

		assert!(!store.has_keys(&[
			(key2.public().to_vec(), ed25519::AppPublic::ID),
			(key.public().to_raw_vec(), ed25519::AppPublic::ID),
		],));

		assert!(store.has_keys(&[(key.public().to_raw_vec(), ed25519::AppPublic::ID)]));
	}

	#[test]
	fn test_insert_ephemeral_from_seed() {
		let temp_dir = TempDir::new().unwrap();
		let mut store = KeystoreInner::open(temp_dir.path(), None).unwrap();

		let pair: ed25519::AppPair = store
			.insert_ephemeral_from_seed(
				"0x3d97c819d68f9bafa7d6e79cb991eebcd77d966c5334c0b94d9e1fa7ad0869dc",
			)
			.unwrap();
		assert_eq!(
			"5DKUrgFqCPV8iAXx9sjy1nyBygQCeiUYRFWurZGhnrn3HJCA",
			pair.public().to_ss58check()
		);

		drop(store);
		let store = KeystoreInner::open(temp_dir.path(), None).unwrap();
		// Keys generated from seed should not be persisted!
		assert!(store.key_pair::<ed25519::AppPair>(&pair.public()).unwrap().is_none());
	}

	#[test]
	fn password_being_used() {
		let password = String::from("password");
		let temp_dir = TempDir::new().unwrap();
		let mut store = KeystoreInner::open(
			temp_dir.path(),
			Some(FromStr::from_str(password.as_str()).unwrap()),
		)
		.unwrap();

		let pair: ed25519::AppPair = store.generate().unwrap();
		assert_eq!(
			pair.public(),
			store.key_pair::<ed25519::AppPair>(&pair.public()).unwrap().unwrap().public(),
		);

		// Without the password the key should not be retrievable
		let store = KeystoreInner::open(temp_dir.path(), None).unwrap();
		assert!(store.key_pair::<ed25519::AppPair>(&pair.public()).is_err());

		let store = KeystoreInner::open(
			temp_dir.path(),
			Some(FromStr::from_str(password.as_str()).unwrap()),
		)
		.unwrap();
		assert_eq!(
			pair.public(),
			store.key_pair::<ed25519::AppPair>(&pair.public()).unwrap().unwrap().public(),
		);
	}

	#[test]
	fn public_keys_are_returned() {
		let temp_dir = TempDir::new().unwrap();
		let mut store = KeystoreInner::open(temp_dir.path(), None).unwrap();

		let mut keys = Vec::new();
		for i in 0..10 {
			keys.push(store.generate::<ed25519::AppPair>().unwrap().public());
			keys.push(
				store
					.insert_ephemeral_from_seed::<ed25519::AppPair>(&format!(
						"0x3d97c819d68f9bafa7d6e79cb991eebcd7{}d966c5334c0b94d9e1fa7ad0869dc",
						i
					))
					.unwrap()
					.public(),
			);
		}

		// Generate a key of a different type
		store.generate::<sr25519::AppPair>().unwrap();

		keys.sort();
		let mut store_pubs = store.public_keys::<ed25519::AppPublic>().unwrap();
		store_pubs.sort();

		assert_eq!(keys, store_pubs);
	}

	#[test]
	fn store_unknown_and_extract_it() {
		let temp_dir = TempDir::new().unwrap();
		let store = KeystoreInner::open(temp_dir.path(), None).unwrap();

		let secret_uri = "//Alice";
		let key_pair = sr25519::AppPair::from_string(secret_uri, None).expect("Generates key pair");

		store
			.insert(SR25519, secret_uri, key_pair.public().as_ref())
			.expect("Inserts unknown key");

		let store_key_pair = store
			.key_pair_by_type::<sr25519::AppPair>(&key_pair.public(), SR25519)
			.expect("Gets key pair from keystore")
			.unwrap();

		assert_eq!(key_pair.public(), store_key_pair.public());
	}

	#[test]
	fn store_ignores_files_with_invalid_name() {
		let temp_dir = TempDir::new().unwrap();
		let store = LocalKeystore::open(temp_dir.path(), None).unwrap();

		let file_name = temp_dir.path().join(array_bytes::bytes2hex("", &SR25519.0[..2]));
		fs::write(file_name, "test").expect("Invalid file is written");

		assert!(store.sr25519_public_keys(SR25519).is_empty());
	}

	#[test]
	fn generate_with_seed_is_not_stored() {
		let temp_dir = TempDir::new().unwrap();
		let store = LocalKeystore::open(temp_dir.path(), None).unwrap();
		let _alice_tmp_key = store.sr25519_generate_new(TEST_KEY_TYPE, Some("//Alice")).unwrap();

		assert_eq!(store.sr25519_public_keys(TEST_KEY_TYPE).len(), 1);

		drop(store);
		let store = LocalKeystore::open(temp_dir.path(), None).unwrap();
		assert_eq!(store.sr25519_public_keys(TEST_KEY_TYPE).len(), 0);
	}

	#[test]
	fn generate_can_be_fetched_in_memory() {
		let store = LocalKeystore::in_memory();
		store.sr25519_generate_new(TEST_KEY_TYPE, Some("//Alice")).unwrap();

		assert_eq!(store.sr25519_public_keys(TEST_KEY_TYPE).len(), 1);
		store.sr25519_generate_new(TEST_KEY_TYPE, None).unwrap();
		assert_eq!(store.sr25519_public_keys(TEST_KEY_TYPE).len(), 2);
	}

	#[test]
	#[cfg(target_family = "unix")]
	fn uses_correct_file_permissions_on_unix() {
		use std::os::unix::fs::PermissionsExt;

		let temp_dir = TempDir::new().unwrap();
		let store = LocalKeystore::open(temp_dir.path(), None).unwrap();

		let public = store.sr25519_generate_new(TEST_KEY_TYPE, None).unwrap();

		let path = store.0.read().key_file_path(public.as_ref(), TEST_KEY_TYPE).unwrap();
		let permissions = File::open(path).unwrap().metadata().unwrap().permissions();

		assert_eq!(0o100600, permissions.mode());
	}
}
