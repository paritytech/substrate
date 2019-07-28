// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

use std::collections::HashMap;
use std::path::PathBuf;
use std::fs::{self, File};
use std::io::{self, Write};

use substrate_primitives::crypto::{
	KeyTypeId, AppPublic, AppKey, AppPair, Pair, Public, IsWrappedBy
};

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
}

/// Keystore Result
pub type Result<T> = std::result::Result<T, Error>;

impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			Error::Io(ref err) => Some(err),
			Error::Json(ref err) => Some(err),
			_ => None,
		}
	}
}

/// Key store.
pub struct Store {
	path: PathBuf,
	additional: HashMap<(KeyTypeId, Vec<u8>), Vec<u8>>,
}

impl Store {
	/// Create a new store at the given path.
	pub fn open(path: PathBuf) -> Result<Self> {
		fs::create_dir_all(&path)?;
		Ok(Store { path, additional: HashMap::new() })
	}

	fn get_pair<TPair: Pair>(&self, public: &TPair::Public, key_type: KeyTypeId) -> Result<Option<TPair>> {
		let key = (key_type, public.to_raw_vec());
		if let Some(bytes) = self.additional.get(&key) {
			let pair = TPair::from_seed_slice(bytes)
				.map_err(|_| Error::InvalidSeed)?;
			return Ok(Some(pair));
		}
		Ok(None)
	}

	fn insert_pair<TPair: Pair>(&mut self, pair: &TPair, key_type: KeyTypeId) {
		let key = (key_type, pair.public().to_raw_vec());
		self.additional.insert(key, pair.to_raw_vec());
	}

	/// Generate a new key, placing it into the store.
	pub fn generate_by_type<TPair: Pair>(&self, password: &str, key_type: KeyTypeId) -> Result<TPair> {
		let (pair, phrase, _) = TPair::generate_with_phrase(Some(password));
		let mut file = File::create(self.key_file_path::<TPair>(&pair.public(), key_type))?;
		::serde_json::to_writer(&file, &phrase)?;
		file.flush()?;
		Ok(pair)
	}

	/// Create a new key from seed. Do not place it into the store.
	pub fn generate_from_seed_by_type<TPair: Pair>(&mut self, seed: &str, key_type: KeyTypeId) -> Result<TPair> {
		let pair = TPair::from_string(seed, None)
			.ok().ok_or(Error::InvalidSeed)?;
		self.insert_pair(&pair, key_type);
		Ok(pair)
	}

	/// Generate a new key, placing it into the store.
	pub fn generate<
		Pair: AppPair
	>(&self, password: &str) -> Result<Pair> {
		self.generate_by_type::<Pair::Generic>(password, Pair::ID)
			.map(Into::into)
	}

	/// Create a new key from seed. Do not place it into the store.
	pub fn generate_from_seed<
		Pair: AppPair,
	>(&mut self, seed: &str) -> Result<Pair> {
		self.generate_from_seed_by_type::<Pair::Generic>(seed, Pair::ID)
			.map(Into::into)
	}

	/// Load a key file with given public key.
	pub fn load_by_type<TPair: Pair>(&self,
		public: &TPair::Public,
		password: &str,
		key_type: KeyTypeId
	) -> Result<TPair> {
		if let Some(pair) = self.get_pair(public, key_type)? {
			return Ok(pair)
		}

		let path = self.key_file_path::<TPair>(public, key_type);
		let file = File::open(path)?;

		let phrase: String = ::serde_json::from_reader(&file)?;
		let (pair, _) = TPair::from_phrase(&phrase, Some(password))
			.ok().ok_or(Error::InvalidPhrase)?;
		if &pair.public() != public {
			return Err(Error::InvalidPassword);
		}
		Ok(pair)
	}

	/// Load a key file with given public key.
	pub fn load<
		Pair_: AppPair
	>(&self, public: &<Pair_ as AppKey>::Public, password: &str) -> Result<Pair_> {
		self.load_by_type::<Pair_::Generic>(IsWrappedBy::from_ref(public), password, Pair_::ID)
			.map(Into::into)
	}

	/// Get public keys of all stored keys.
	pub fn contents_by_type<TPublic: Public>(&self, key_type: KeyTypeId) -> Result<Vec<TPublic>> {
		let mut public_keys: Vec<TPublic> = self.additional.keys()
			.filter_map(|(ty, public)| {
				if *ty != key_type {
					return None
				}
				Some(TPublic::from_slice(public))
			})
			.collect();

		for entry in fs::read_dir(&self.path)? {
			let entry = entry?;
			let path = entry.path();

			// skip directories and non-unicode file names (hex is unicode)
			if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
				match hex::decode(name) {
					Ok(ref hex) => {
						if hex[0..4] != key_type { continue	}
						let public = TPublic::from_slice(&hex[4..]);
						public_keys.push(public);
					}
					_ => continue,
				}
			}
		}

		Ok(public_keys)
	}

	/// Get public keys of all stored keys.
	///
	/// This will just use the type of the public key (a list of which to be returned) in order
	/// to determine the key type. Unless you use a specialised application-type public key, then
	/// this only give you keys registered under generic cryptography, and will not return keys
	/// registered under the application type.
	pub fn contents<
		Public: AppPublic
	>(&self) -> Result<Vec<Public>> {
		self.contents_by_type::<Public::Generic>(Public::ID)
			.map(|v| v.into_iter().map(Into::into).collect())
	}

	fn key_file_path<TPair: Pair>(&self, public: &TPair::Public, key_type: KeyTypeId) -> PathBuf {
		let mut buf = self.path.clone();
		let key_type = hex::encode(key_type);
		let key = hex::encode(public.as_slice());
		buf.push(key_type + key.as_str());
		buf
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use tempdir::TempDir;
	use substrate_primitives::ed25519;
	use substrate_primitives::crypto::Ss58Codec;

	#[test]
	fn basic_store() {
		let temp_dir = TempDir::new("keystore").unwrap();
		let store = Store::open(temp_dir.path().to_owned()).unwrap();

		assert!(store.contents::<ed25519::Public>().unwrap().is_empty());

		let key: ed25519::Pair = store.generate("thepassword").unwrap();
		let key2: ed25519::Pair = store.load(&key.public(), "thepassword").unwrap();

		assert!(store.load::<ed25519::Pair>(&key.public(), "notthepassword").is_err());

		assert_eq!(key.public(), key2.public());

		assert_eq!(store.contents::<ed25519::Public>().unwrap()[0], key.public());
	}

	#[test]
	fn test_generate_from_seed() {
		let temp_dir = TempDir::new("keystore").unwrap();
		let mut store = Store::open(temp_dir.path().to_owned()).unwrap();

		let pair: ed25519::Pair = store
			.generate_from_seed("0x3d97c819d68f9bafa7d6e79cb991eebcd77d966c5334c0b94d9e1fa7ad0869dc")
			.unwrap();
		assert_eq!("5DKUrgFqCPV8iAXx9sjy1nyBygQCeiUYRFWurZGhnrn3HJCA", pair.public().to_ss58check());
	}
}
