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

use substrate_primitives::{ed25519::{Pair, Public}, Pair as PairT};

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
	additional: HashMap<Public, Pair>,
}

impl Store {
	/// Create a new store at the given path.
	pub fn open(path: PathBuf) -> Result<Self> {
		fs::create_dir_all(&path)?;
		Ok(Store { path, additional: HashMap::new() })
	}

	/// Generate a new key, placing it into the store.
	pub fn generate(&self, password: &str) -> Result<Pair> {
		let (pair, phrase, _) = Pair::generate_with_phrase(Some(password));
		let mut file = File::create(self.key_file_path(&pair.public()))?;
		::serde_json::to_writer(&file, &phrase)?;
		file.flush()?;
		Ok(pair)
	}

	/// Create a new key from seed. Do not place it into the store.
	pub fn generate_from_seed(&mut self, seed: &str) -> Result<Pair> {
		let pair = Pair::from_string(seed, None)
			.ok().ok_or(Error::InvalidSeed)?;
		self.additional.insert(pair.public(), pair.clone());
		Ok(pair)
	}

	/// Load a key file with given public key.
	pub fn load(&self, public: &Public, password: &str) -> Result<Pair> {
		if let Some(pair) = self.additional.get(public) {
			return Ok(pair.clone());
		}
		let path = self.key_file_path(public);
		let file = File::open(path)?;

		let phrase: String = ::serde_json::from_reader(&file)?;
		let (pair, _) = Pair::from_phrase(&phrase, Some(password))
			.ok().ok_or(Error::InvalidPhrase)?;
		if &pair.public() != public {
			return Err(Error::InvalidPassword);
		}
		Ok(pair)
	}

	/// Get public keys of all stored keys.
	pub fn contents(&self) -> Result<Vec<Public>> {
		let mut public_keys: Vec<Public> = self.additional.keys().cloned().collect();
		for entry in fs::read_dir(&self.path)? {
			let entry = entry?;
			let path = entry.path();

			// skip directories and non-unicode file names (hex is unicode)
			if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
				if name.len() != 64 { continue }

				match hex::decode(name) {
					Ok(ref hex) if hex.len() == 32 => {
						let mut buf = [0; 32];
						buf.copy_from_slice(&hex[..]);

						public_keys.push(Public(buf));
					}
					_ => continue,
				}
			}
		}

		Ok(public_keys)
	}

	fn key_file_path(&self, public: &Public) -> PathBuf {
		let mut buf = self.path.clone();
		buf.push(hex::encode(public.as_slice()));
		buf
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use tempdir::TempDir;
	use substrate_primitives::crypto::Ss58Codec;

	#[test]
	fn basic_store() {
		let temp_dir = TempDir::new("keystore").unwrap();
		let store = Store::open(temp_dir.path().to_owned()).unwrap();

		assert!(store.contents().unwrap().is_empty());

		let key = store.generate("thepassword").unwrap();
		let key2 = store.load(&key.public(), "thepassword").unwrap();

		assert!(store.load(&key.public(), "notthepassword").is_err());

		assert_eq!(key.public(), key2.public());

		assert_eq!(store.contents().unwrap()[0], key.public());
	}

	#[test]
	fn test_generate_from_seed() {
		let temp_dir = TempDir::new("keystore").unwrap();
		let mut store = Store::open(temp_dir.path().to_owned()).unwrap();

		let pair = store.generate_from_seed("0x3d97c819d68f9bafa7d6e79cb991eebcd77d966c5334c0b94d9e1fa7ad0869dc").unwrap();
		assert_eq!("5DKUrgFqCPV8iAXx9sjy1nyBygQCeiUYRFWurZGhnrn3HJCA", pair.public().to_ss58check());
	}
}
