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

// tag::description[]
//! ECIES encryption scheme using x25519 key exchange and AEAD.
// end::description[]

use aes_gcm::{aead::Aead, AeadCore, KeyInit};
use rand::rngs::OsRng;
use sha2::Digest;
use sp_core::crypto::Pair;

/// x25519 secret key.
pub type SecretKey = x25519_dalek::StaticSecret;
/// x25519 public key.
pub type PublicKey = x25519_dalek::PublicKey;

/// Encryption or decryption error.
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
	/// Generic AES encryption error.
	#[error("Encryption error")]
	Encryption,
	/// Generic AES decryption error.
	#[error("Decryption error")]
	Decryption,
	/// Error reading key data. Not enough data in the buffer.
	#[error("Bad cypher text")]
	BadData,
}

const NONCE_LEN: usize = 12;
const PK_LEN: usize = 32;
const AES_KEY_LEN: usize = 32;

fn aes_encrypt(key: &[u8; AES_KEY_LEN], nonce: &[u8], plaintext: &[u8]) -> Result<Vec<u8>, Error> {
	let enc = aes_gcm::Aes256Gcm::new(key.into());

	enc.encrypt(nonce.into(), aes_gcm::aead::Payload { msg: plaintext, aad: b"" })
		.map_err(|_| Error::Encryption)
}

fn aes_decrypt(key: &[u8; AES_KEY_LEN], nonce: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>, Error> {
	let dec = aes_gcm::Aes256Gcm::new(key.into());
	dec.decrypt(nonce.into(), aes_gcm::aead::Payload { msg: ciphertext, aad: b"" })
		.map_err(|_| Error::Decryption)
}

fn kdf(shared_secret: &[u8]) -> [u8; AES_KEY_LEN] {
	let hkdf = hkdf::Hkdf::<sha2::Sha256>::new(None, shared_secret);
	let mut aes_key = [0u8; AES_KEY_LEN];
	hkdf.expand(b"", &mut aes_key)
		.expect("There's always enough data for derivation. qed.");
	aes_key
}

/// Encrypt `plaintext` with the given public x25519 public key. Decryption can be performed with
/// the matching secret key.
pub fn encrypt_x25519(pk: &PublicKey, plaintext: &[u8]) -> Result<Vec<u8>, Error> {
	let ephemeral_sk = x25519_dalek::StaticSecret::random_from_rng(OsRng);
	let ephemeral_pk = x25519_dalek::PublicKey::from(&ephemeral_sk);

	let mut shared_secret = ephemeral_sk.diffie_hellman(pk).to_bytes().to_vec();
	shared_secret.extend_from_slice(ephemeral_pk.as_bytes());

	let aes_key = kdf(&shared_secret);

	let nonce = aes_gcm::Aes256Gcm::generate_nonce(OsRng);
	let ciphertext = aes_encrypt(&aes_key, &nonce, plaintext)?;

	let mut out = Vec::with_capacity(ciphertext.len() + PK_LEN + NONCE_LEN);
	out.extend_from_slice(ephemeral_pk.as_bytes());
	out.extend_from_slice(nonce.as_slice());
	out.extend_from_slice(ciphertext.as_slice());

	Ok(out)
}

/// Encrypt `plaintext` with the given ed25519 public key. Decryption can be performed with the
/// matching secret key.
pub fn encrypt_ed25519(pk: &sp_core::ed25519::Public, plaintext: &[u8]) -> Result<Vec<u8>, Error> {
	let ed25519 = curve25519_dalek::edwards::CompressedEdwardsY(pk.0);
	let x25519 = ed25519.decompress().ok_or(Error::BadData)?.to_montgomery();
	let montgomery = x25519_dalek::PublicKey::from(x25519.to_bytes());
	encrypt_x25519(&montgomery, plaintext)
}

/// Decrypt with the given x25519 secret key.
pub fn decrypt_x25519(sk: &SecretKey, encrypted: &[u8]) -> Result<Vec<u8>, Error> {
	if encrypted.len() < PK_LEN + NONCE_LEN {
		return Err(Error::BadData)
	}
	let mut ephemeral_pk: [u8; PK_LEN] = Default::default();
	ephemeral_pk.copy_from_slice(&encrypted[0..PK_LEN]);
	let ephemeral_pk = PublicKey::from(ephemeral_pk);

	let mut shared_secret = sk.diffie_hellman(&ephemeral_pk).to_bytes().to_vec();
	shared_secret.extend_from_slice(ephemeral_pk.as_bytes());

	let aes_key = kdf(&shared_secret);

	let nonce = &encrypted[PK_LEN..PK_LEN + NONCE_LEN];
	aes_decrypt(&aes_key, &nonce, &encrypted[PK_LEN + NONCE_LEN..])
}

/// Decrypt with the given ed25519 key pair.
pub fn decrypt_ed25519(pair: &sp_core::ed25519::Pair, encrypted: &[u8]) -> Result<Vec<u8>, Error> {
	let raw = pair.to_raw_vec();
	let hash: [u8; 32] = sha2::Sha512::digest(&raw).as_slice()[..32]
		.try_into()
		.map_err(|_| Error::Decryption)?;
	let secret = x25519_dalek::StaticSecret::from(hash);
	decrypt_x25519(&secret, encrypted)
}

#[cfg(test)]
mod test {
	use super::*;
	use rand::rngs::OsRng;
	use sp_core::crypto::Pair;

	#[test]
	fn basic_x25519_encryption() {
		let sk = SecretKey::random_from_rng(OsRng);
		let pk = PublicKey::from(&sk);

		let plain_message = b"An important secret message";
		let encrypted = encrypt_x25519(&pk, plain_message).unwrap();

		let decrypted = decrypt_x25519(&sk, &encrypted).unwrap();
		assert_eq!(plain_message, decrypted.as_slice());
	}

	#[test]
	fn basic_ed25519_encryption() {
		let (pair, _) = sp_core::ed25519::Pair::generate();
		let pk = pair.into();

		let plain_message = b"An important secret message";
		let encrypted = encrypt_ed25519(&pk, plain_message).unwrap();

		let decrypted = decrypt_ed25519(&pair, &encrypted).unwrap();
		assert_eq!(plain_message, decrypted.as_slice());
	}

	#[test]
	fn fails_on_bad_data() {
		let sk = SecretKey::random_from_rng(OsRng);
		let pk = PublicKey::from(&sk);

		let plain_message = b"An important secret message";
		let encrypted = encrypt_x25519(&pk, plain_message).unwrap();

		assert_eq!(decrypt_x25519(&sk, &[]), Err(Error::BadData));
		assert_eq!(
			decrypt_x25519(&sk, &encrypted[0..super::PK_LEN + super::NONCE_LEN - 1]),
			Err(Error::BadData)
		);
	}
}
