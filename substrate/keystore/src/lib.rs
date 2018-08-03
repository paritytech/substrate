// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

extern crate ethcore_crypto as crypto;
extern crate subtle;
extern crate ed25519;
extern crate rand;
extern crate serde_json;
extern crate serde;
extern crate hex;

#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate error_chain;

#[cfg(test)]
extern crate tempdir;

use std::collections::HashMap;
use std::path::PathBuf;
use std::fs::{self, File};
use std::io::{self, Write};

use crypto::Keccak256;
use ed25519::{Pair, Public, PKCS_LEN};

pub use crypto::KEY_ITERATIONS;

error_chain! {
	foreign_links {
		Io(io::Error);
		Json(serde_json::Error);
	}

	errors {
		InvalidPassword {
			description("Invalid password"),
			display("Invalid password"),
		}
		InvalidPKCS8 {
			description("Invalid PKCS#8 data"),
			display("Invalid PKCS#8 data"),
		}
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidPassword;

#[derive(Serialize, Deserialize)]
struct EncryptedKey {
	mac: [u8; 32],
	salt: [u8; 32],
	ciphertext: Vec<u8>, // TODO: switch to fixed-size when serde supports
	iv: [u8; 16],
	iterations: u32,
}

impl EncryptedKey {
	fn encrypt(plain: &[u8; PKCS_LEN], password: &str, iterations: u32) -> Self {
		use rand::{Rng, OsRng};

		let mut rng = OsRng::new().expect("OS Randomness available on all supported platforms; qed");

		let salt: [u8; 32] = rng.gen();
		let iv: [u8; 16] = rng.gen();

		// two parts of derived key
		// DK = [ DK[0..15] DK[16..31] ] = [derived_left_bits, derived_right_bits]
		let (derived_left_bits, derived_right_bits) = crypto::derive_key_iterations(password.as_bytes(), &salt, iterations);

		// preallocated (on-stack in case of `Secret`) buffer to hold cipher
		// length = length(plain) as we are using CTR-approach
		let mut ciphertext = vec![0; PKCS_LEN];

		// aes-128-ctr with initial vector of iv
		crypto::aes::encrypt_128_ctr(&derived_left_bits, &iv, plain, &mut *ciphertext)
			.expect("input lengths of key and iv are both 16; qed");

		// KECCAK(DK[16..31] ++ <ciphertext>), where DK[16..31] - derived_right_bits
		let mac = crypto::derive_mac(&derived_right_bits, &*ciphertext).keccak256();

		EncryptedKey {
			salt,
			iv,
			mac,
			iterations,
			ciphertext,
		}
	}

	fn decrypt(&self, password: &str) -> Result<[u8; PKCS_LEN]> {
		let (derived_left_bits, derived_right_bits) =
			crypto::derive_key_iterations(password.as_bytes(), &self.salt, self.iterations);

		let mac = crypto::derive_mac(&derived_right_bits, &self.ciphertext).keccak256();

		if subtle::slices_equal(&mac[..], &self.mac[..]) != 1 {
			return Err(ErrorKind::InvalidPassword.into());
		}

		let mut plain = [0; PKCS_LEN];
		crypto::aes::decrypt_128_ctr(&derived_left_bits, &self.iv, &self.ciphertext, &mut plain[..])
			.expect("input lengths of key and iv are both 16; qed");
		Ok(plain)
	}
}

type Seed = [u8; 32];

/// Key store.
pub struct Store {
	path: PathBuf,
	additional: HashMap<Public, Seed>,
}

impl Store {
	/// Create a new store at the given path.
	pub fn open(path: PathBuf) -> Result<Self> {
		fs::create_dir_all(&path)?;
		Ok(Store { path, additional: HashMap::new() })
	}

	/// Generate a new key, placing it into the store.
	pub fn generate(&self, password: &str) -> Result<Pair> {
		let (pair, pkcs_bytes) = Pair::generate_with_pkcs8();
		let key_file = EncryptedKey::encrypt(&pkcs_bytes, password, KEY_ITERATIONS as u32);

		let mut file = File::create(self.key_file_path(&pair.public()))?;
		::serde_json::to_writer(&file, &key_file)?;

		file.flush()?;

		Ok(pair)
	}

	/// Create a new key from seed. Do not place it into the store.
	/// Only the first 32 bytes of the sead are used. This is meant to be used for testing only.
	// TODO: Remove this
	pub fn generate_from_seed(&mut self, seed: &str) -> Result<Pair> {
		let mut s: [u8; 32] = [' ' as u8; 32];

		let was_hex = if seed.len() == 66 && &seed[0..2] == "0x" {
			if let Ok(d) = hex::decode(&seed[2..]) {
				s.copy_from_slice(&d);
				true
			} else { false }
		} else { false };

		if !was_hex {
			let len = ::std::cmp::min(32, seed.len());
			&mut s[..len].copy_from_slice(&seed.as_bytes()[..len]);
		}

		let pair = Pair::from_seed(&s);
		self.additional.insert(pair.public(), s);
		Ok(pair)
	}

	/// Load a key file with given public key.
	pub fn load(&self, public: &Public, password: &str) -> Result<Pair> {
		if let Some(ref seed) = self.additional.get(public) {
			let pair = Pair::from_seed(seed);
			return Ok(pair);
		}
		let path = self.key_file_path(public);
		let file = File::open(path)?;

		let encrypted_key: EncryptedKey = ::serde_json::from_reader(&file)?;
		let pkcs_bytes = encrypted_key.decrypt(password)?;

		Pair::from_pkcs8(&pkcs_bytes[..]).map_err(|_| ErrorKind::InvalidPKCS8.into())
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

	#[test]
	fn encrypt_and_decrypt() {
		let plain = [1; PKCS_LEN];
		let encrypted_key = EncryptedKey::encrypt(&plain, "thepassword", KEY_ITERATIONS as u32);

		let decrypted_key = encrypted_key.decrypt("thepassword").unwrap();

		assert_eq!(&plain[..], &decrypted_key[..]);
	}

	#[test]
	fn decrypt_wrong_password_fails() {
		let plain = [1; PKCS_LEN];
		let encrypted_key = EncryptedKey::encrypt(&plain, "thepassword", KEY_ITERATIONS as u32);

		assert!(encrypted_key.decrypt("thepassword2").is_err());
	}

	#[test]
	fn decrypt_wrong_iterations_fails() {
		let plain = [1; PKCS_LEN];
		let mut encrypted_key = EncryptedKey::encrypt(&plain, "thepassword", KEY_ITERATIONS as u32);

		encrypted_key.iterations -= 64;

		assert!(encrypted_key.decrypt("thepassword").is_err());
	}

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

		let pair = store.generate_from_seed("0x1").unwrap();
		assert_eq!("5GqhgbUd2S9uc5Tm7hWhw29Tw2jBnuHshmTV1fDF4V1w3G2z", pair.public().to_ss58check());

		let pair = store.generate_from_seed("0x3d97c819d68f9bafa7d6e79cb991eebcd77d966c5334c0b94d9e1fa7ad0869dc").unwrap();
		assert_eq!("5DKUrgFqCPV8iAXx9sjy1nyBygQCeiUYRFWurZGhnrn3HBL8", pair.public().to_ss58check());

		let pair = store.generate_from_seed("12345678901234567890123456789022").unwrap();
		assert_eq!("5DscZvfjnM5im7oKRXXP9xtCG1SEwfMb8J5eGLmw5EHhoHR3", pair.public().to_ss58check());

		let pair = store.generate_from_seed("1").unwrap();
		assert_eq!("5DYnksEZFc7kgtfyNM1xK2eBtW142gZ3Ho3NQubrF2S6B2fq", pair.public().to_ss58check());
	}
}
