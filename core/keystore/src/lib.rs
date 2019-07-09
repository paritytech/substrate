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

use substrate_primitives::crypto::{KeyTypeId, Pair, Public};

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

	fn get_pair<TPair: Pair>(&self, public: &TPair::Public) -> Result<Option<TPair>> {
		let key = (TPair::KEY_TYPE, public.to_raw_vec());
		if let Some(bytes) = self.additional.get(&key) {
			let pair = TPair::from_seed_slice(bytes)
				.map_err(|_| Error::InvalidSeed)?;
			return Ok(Some(pair));
		}
		Ok(None)
	}

	fn insert_pair<TPair: Pair>(&mut self, pair: &TPair) {
		let key = (TPair::KEY_TYPE, pair.public().to_raw_vec());
		self.additional.insert(key, pair.to_raw_vec());
	}

	/// Generate a new key, placing it into the store.
	pub fn generate<TPair: Pair>(&self, password: &str) -> Result<TPair> {
		let (pair, phrase, _) = TPair::generate_with_phrase(Some(password));
		let mut file = File::create(self.key_file_path::<TPair>(&pair.public()))?;
		::serde_json::to_writer(&file, &phrase)?;
		file.flush()?;
		Ok(pair)
	}

	/// Create a new key from seed. Do not place it into the store.
	pub fn generate_from_seed<TPair: Pair>(&mut self, seed: &str) -> Result<TPair> {
		let pair = TPair::from_string(seed, None)
			.ok().ok_or(Error::InvalidSeed)?;
		self.insert_pair(&pair);
		Ok(pair)
	}

	/// Load a key file with given public key.
	pub fn load<TPair: Pair>(&self, public: &TPair::Public, password: &str) -> Result<TPair> {
		if let Some(pair) = self.get_pair(public)? {
			return Ok(pair)
		}

		let path = self.key_file_path::<TPair>(public);
		let file = File::open(path)?;

		let phrase: String = ::serde_json::from_reader(&file)?;
		let (pair, _) = TPair::from_phrase(&phrase, Some(password))
			.ok().ok_or(Error::InvalidPhrase)?;
		if &pair.public() != public {
			return Err(Error::InvalidPassword);
		}
		Ok(pair)
	}

	/// Get public keys of all stored keys.
	pub fn contents<TPublic: Public>(&self) -> Result<Vec<TPublic>> {
		let mut public_keys: Vec<TPublic> = self.additional.keys()
			.filter_map(|(ty, public)| {
				if *ty != TPublic::KEY_TYPE {
					return None
				}
				Some(TPublic::from_slice(public))
			})
			.collect();

		let key_type: [u8; 4] = TPublic::KEY_TYPE.to_le_bytes();
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

	fn key_file_path<TPair: Pair>(&self, public: &TPair::Public) -> PathBuf {
		let mut buf = self.path.clone();
		let bytes: [u8; 4] = TPair::KEY_TYPE.to_le_bytes();
		let key_type = hex::encode(bytes);
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
