// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! Keystore (and session key management) for ed25519 based chains like Polkadot.

#![warn(missing_docs)]
use std::io;
use sp_core::crypto::KeyTypeId;
use sp_keystore::Error as TraitError;

/// Local keystore implementation
mod local;
pub use local::LocalKeystore;

/// Keystore error.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// IO error.
	Io(io::Error),
	/// JSON error.
	Json(serde_json::Error),
	/// Invalid password.
	#[display(fmt="Invalid password")]
	InvalidPassword,
	/// Invalid BIP39 phrase
	#[display(fmt="Invalid recovery phrase (BIP39) data")]
	InvalidPhrase,
	/// Invalid seed
	#[display(fmt="Invalid seed")]
	InvalidSeed,
	/// Public key type is not supported
	#[display(fmt="Key crypto type is not supported")]
	KeyNotSupported(KeyTypeId),
	/// Pair not found for public key and KeyTypeId
	#[display(fmt="Pair not found for {} public key", "_0")]
	PairNotFound(String),
	/// Keystore unavailable
	#[display(fmt="Keystore unavailable")]
	Unavailable,
}

/// Keystore Result
pub type Result<T> = std::result::Result<T, Error>;

impl From<Error> for TraitError {
	fn from(error: Error) -> Self {
		match error {
			Error::KeyNotSupported(id) => TraitError::KeyNotSupported(id),
			Error::PairNotFound(e) => TraitError::PairNotFound(e),
			Error::InvalidSeed | Error::InvalidPhrase | Error::InvalidPassword => {
				TraitError::ValidationError(error.to_string())
			},
			Error::Unavailable => TraitError::Unavailable,
			Error::Io(e) => TraitError::Other(e.to_string()),
			Error::Json(e) => TraitError::Other(e.to_string()),
		}
	}
}

impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			Error::Io(ref err) => Some(err),
			Error::Json(ref err) => Some(err),
			_ => None,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use tempfile::TempDir;
	use sp_core::{Pair, testing::SR25519, crypto::Ss58Codec};
	use sp_keystore::CryptoStore;
	use sp_application_crypto::{ed25519, sr25519};
	use futures::executor::block_on;
	use std::{
		fs,
		str::FromStr,
	};
	#[test]
	fn basic_store() {
		let temp_dir = TempDir::new().unwrap();
		let store = local::KeystoreInner::open(temp_dir.path(), None).unwrap();

		assert!(store.public_keys::<ed25519::AppPublic>().unwrap().is_empty());

		let key: ed25519::AppPair = store.generate().unwrap();
		let key2: ed25519::AppPair = store.key_pair(&key.public()).unwrap();

		assert_eq!(key.public(), key2.public());

		assert_eq!(store.public_keys::<ed25519::AppPublic>().unwrap()[0], key.public());
	}

	#[test]
	fn test_insert_ephemeral_from_seed() {
		let temp_dir = TempDir::new().unwrap();
		let mut store = local::KeystoreInner::open(temp_dir.path(), None).unwrap();

		let pair: ed25519::AppPair = store
			.insert_ephemeral_from_seed("0x3d97c819d68f9bafa7d6e79cb991eebcd77d966c5334c0b94d9e1fa7ad0869dc")
			.unwrap();
		assert_eq!(
			"5DKUrgFqCPV8iAXx9sjy1nyBygQCeiUYRFWurZGhnrn3HJCA",
			pair.public().to_ss58check()
		);

		drop(store);
		let store = local::KeystoreInner::open(temp_dir.path(), None).unwrap();
		// Keys generated from seed should not be persisted!
		assert!(store.key_pair::<ed25519::AppPair>(&pair.public()).is_err());
	}

	#[test]
	fn password_being_used() {
		let password = String::from("password");
		let temp_dir = TempDir::new().unwrap();
		let store = local::KeystoreInner::open(
			temp_dir.path(),
			Some(FromStr::from_str(password.as_str()).unwrap()),
		).unwrap();

		let pair: ed25519::AppPair = store.generate().unwrap();
		assert_eq!(
			pair.public(),
			store.key_pair::<ed25519::AppPair>(&pair.public()).unwrap().public(),
		);

		// Without the password the key should not be retrievable
		let store = local::KeystoreInner::open(temp_dir.path(), None).unwrap();
		assert!(store.key_pair::<ed25519::AppPair>(&pair.public()).is_err());

		let store = local::KeystoreInner::open(
			temp_dir.path(),
			Some(FromStr::from_str(password.as_str()).unwrap()),
		).unwrap();
		assert_eq!(
			pair.public(),
			store.key_pair::<ed25519::AppPair>(&pair.public()).unwrap().public(),
		);
	}

	#[test]
	fn public_keys_are_returned() {
		let temp_dir = TempDir::new().unwrap();
		let mut store = local::KeystoreInner::open(temp_dir.path(), None).unwrap();

		let mut public_keys = Vec::new();
		for i in 0..10 {
			public_keys.push(store.generate::<ed25519::AppPair>().unwrap().public());
			public_keys.push(store.insert_ephemeral_from_seed::<ed25519::AppPair>(
				&format!("0x3d97c819d68f9bafa7d6e79cb991eebcd7{}d966c5334c0b94d9e1fa7ad0869dc", i),
			).unwrap().public());
		}

		// Generate a key of a different type
		store.generate::<sr25519::AppPair>().unwrap();

		public_keys.sort();
		let mut store_pubs = store.public_keys::<ed25519::AppPublic>().unwrap();
		store_pubs.sort();

		assert_eq!(public_keys, store_pubs);
	}

	#[test]
	fn store_unknown_and_extract_it() {
		let temp_dir = TempDir::new().unwrap();
		let store = local::KeystoreInner::open(temp_dir.path(), None).unwrap();

		let secret_uri = "//Alice";
		let key_pair = sr25519::AppPair::from_string(secret_uri, None).expect("Generates key pair");

		store.insert_unknown(
			SR25519,
			secret_uri,
			key_pair.public().as_ref(),
		).expect("Inserts unknown key");

		let store_key_pair = store.key_pair_by_type::<sr25519::AppPair>(
			&key_pair.public(),
			SR25519,
		).expect("Gets key pair from keystore");

		assert_eq!(key_pair.public(), store_key_pair.public());
	}

	#[test]
	fn store_ignores_files_with_invalid_name() {
		let temp_dir = TempDir::new().unwrap();
		let store = local::LocalKeystore::open(temp_dir.path(), None).unwrap();

		let file_name = temp_dir.path().join(hex::encode(&SR25519.0[..2]));
		fs::write(file_name, "test").expect("Invalid file is written");

		assert!(
			block_on(store.sr25519_public_keys(SR25519)).is_empty(),
		);
	}
}
