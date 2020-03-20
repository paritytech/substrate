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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Hash utilities.

use codec::{Codec, Decode};
use sp_std::prelude::Vec;
use sp_io::hashing::{blake2_128, blake2_256, twox_64, twox_128, twox_256};

// This trait must be kept coherent with frame-support-procedural HasherKind usage
pub trait Hashable: Sized {
	fn blake2_128(&self) -> [u8; 16];
	fn blake2_256(&self) -> [u8; 32];
	fn blake2_128_concat(&self) -> Vec<u8>;
	fn twox_128(&self) -> [u8; 16];
	fn twox_256(&self) -> [u8; 32];
	fn twox_64_concat(&self) -> Vec<u8>;
	fn identity(&self) -> Vec<u8>;
}

impl<T: Codec> Hashable for T {
	fn blake2_128(&self) -> [u8; 16] {
		self.using_encoded(blake2_128)
	}
	fn blake2_256(&self) -> [u8; 32] {
		self.using_encoded(blake2_256)
	}
	fn blake2_128_concat(&self) -> Vec<u8> {
		self.using_encoded(Blake2_128Concat::hash)
	}
	fn twox_128(&self) -> [u8; 16] {
		self.using_encoded(twox_128)
	}
	fn twox_256(&self) -> [u8; 32] {
		self.using_encoded(twox_256)
	}
	fn twox_64_concat(&self) -> Vec<u8> {
		self.using_encoded(Twox64Concat::hash)
	}
	fn identity(&self) -> Vec<u8> { self.encode() }
}

/// Hasher to use to hash keys to insert to storage.
pub trait StorageHasher: 'static {
	type Output: AsRef<[u8]>;
	fn hash(x: &[u8]) -> Self::Output;
}

/// Hasher to use to hash keys to insert to storage.
pub trait ReversibleStorageHasher: StorageHasher {
	fn reverse(x: &[u8]) -> &[u8];
}

/// Trait to retrieve some info from hash of type `Key` encoded.
pub trait StorageHasherInfo<Key> {
	/// Some info contained in the hash of type `Key` encoded.
	type Info;

	/// Decode the hash and then decode the info from the decoded hash.
	///
	/// # WARNING
	///
	/// Even if info is (), input must be modified to have read the entire encoded hash.
	fn decode_hash_and_then_info<I: codec::Input>(input: &mut I)
		-> Result<Self::Info, codec::Error>;
}

/// Store the key directly.
pub struct Identity;
impl StorageHasher for Identity {
	type Output = Vec<u8>;
	fn hash(x: &[u8]) -> Vec<u8> {
		x.to_vec()
	}
}
impl ReversibleStorageHasher for Identity {
	fn reverse(x: &[u8]) -> &[u8] {
		x
	}
}
impl<Key: Decode> StorageHasherInfo<Key> for Identity {
	type Info = Key;
	fn decode_hash_and_then_info<I: codec::Input>(input: &mut I)
		-> Result<Self::Info, codec::Error>
	{
		Key::decode(input)
	}
}

/// Hash storage keys with `concat(twox64(key), key)`
pub struct Twox64Concat;
impl StorageHasher for Twox64Concat {
	type Output = Vec<u8>;
	fn hash(x: &[u8]) -> Vec<u8> {
		twox_64(x)
			.iter()
			.chain(x.into_iter())
			.cloned()
			.collect::<Vec<_>>()
	}
}
impl ReversibleStorageHasher for Twox64Concat {
	fn reverse(x: &[u8]) -> &[u8] {
		&x[8..]
	}
}
impl<Key: Decode> StorageHasherInfo<Key> for Twox64Concat {
	type Info = Key;
	fn decode_hash_and_then_info<I: codec::Input>(input: &mut I)
		-> Result<Self::Info, codec::Error>
	{
		input.read(&mut [0u8; 8])?;
		Key::decode(input)
	}
}

/// Hash storage keys with `concat(blake2_128(key), key)`
pub struct Blake2_128Concat;
impl StorageHasher for Blake2_128Concat {
	type Output = Vec<u8>;
	fn hash(x: &[u8]) -> Vec<u8> {
		blake2_128(x)
			.iter()
			.chain(x.into_iter())
			.cloned()
			.collect::<Vec<_>>()
	}
}
impl ReversibleStorageHasher for Blake2_128Concat {
	fn reverse(x: &[u8]) -> &[u8] {
		&x[16..]
	}
}
impl<Key: Decode> StorageHasherInfo<Key> for Blake2_128Concat {
	type Info = Key;
	fn decode_hash_and_then_info<I: codec::Input>(input: &mut I)
		-> Result<Self::Info, codec::Error>
	{
		input.read(&mut [0u8; 16])?;
		Key::decode(input)
	}
}

/// Hash storage keys with blake2 128
pub struct Blake2_128;
impl StorageHasher for Blake2_128 {
	type Output = [u8; 16];
	fn hash(x: &[u8]) -> [u8; 16] {
		blake2_128(x)
	}
}
impl<Key> StorageHasherInfo<Key> for Blake2_128 {
	type Info = ();
	fn decode_hash_and_then_info<I: codec::Input>(input: &mut I)
		-> Result<Self::Info, codec::Error>
	{
		input.read(&mut [0u8; 16])?;
		Ok(())
	}
}

/// Hash storage keys with blake2 256
pub struct Blake2_256;
impl StorageHasher for Blake2_256 {
	type Output = [u8; 32];
	fn hash(x: &[u8]) -> [u8; 32] {
		blake2_256(x)
	}
}
impl<Key> StorageHasherInfo<Key> for Blake2_256 {
	type Info = ();
	fn decode_hash_and_then_info<I: codec::Input>(input: &mut I)
		-> Result<Self::Info, codec::Error>
	{
		input.read(&mut [0u8; 32])?;
		Ok(())
	}
}

/// Hash storage keys with twox 128
pub struct Twox128;
impl StorageHasher for Twox128 {
	type Output = [u8; 16];
	fn hash(x: &[u8]) -> [u8; 16] {
		twox_128(x)
	}
}
impl<Key> StorageHasherInfo<Key> for Twox128 {
	type Info = ();
	fn decode_hash_and_then_info<I: codec::Input>(input: &mut I)
		-> Result<Self::Info, codec::Error>
	{
		input.read(&mut [0u8; 16])?;
		Ok(())
	}
}

/// Hash storage keys with twox 256
pub struct Twox256;
impl StorageHasher for Twox256 {
	type Output = [u8; 32];
	fn hash(x: &[u8]) -> [u8; 32] {
		twox_256(x)
	}
}
impl<Key> StorageHasherInfo<Key> for Twox256 {
	type Info = ();
	fn decode_hash_and_then_info<I: codec::Input>(input: &mut I)
		-> Result<Self::Info, codec::Error>
	{
		input.read(&mut [0u8; 32])?;
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::Encode;

	#[test]
	fn test_twox_64_concat() {
		let r = Twox64Concat::hash(b"foo");
		assert_eq!(r.split_at(8), (&twox_128(b"foo")[..8], &b"foo"[..]))
	}

	#[test]
	fn test_blake2_128_concat() {
		let r = Blake2_128Concat::hash(b"foo");
		assert_eq!(r.split_at(16), (&blake2_128(b"foo")[..], &b"foo"[..]))
	}

	#[test]
	fn test_storage_hasher_info() {
		type KeyType = [u8; 15];
		let key: KeyType = [3u8; 15];

		let mut r = &Identity::hash(&(&key).encode()[..])[..];
		assert_eq!(<Identity as StorageHasherInfo<KeyType>>::decode_hash_and_then_info(&mut r), Ok(key));
		assert_eq!(r.len(), 0); // Assert input has indeed decoded the hash.

		let mut r = &Twox64Concat::hash(&(&key).encode()[..])[..];
		assert_eq!(<Twox64Concat as StorageHasherInfo<KeyType>>::decode_hash_and_then_info(&mut r), Ok(key));
		assert_eq!(r.len(), 0); // Assert input has indeed decoded the hash.

		let mut r = &Twox128::hash(&(&key).encode()[..])[..];
		assert_eq!(<Twox128 as StorageHasherInfo<KeyType>>::decode_hash_and_then_info(&mut r), Ok(()));
		assert_eq!(r.len(), 0); // Assert input has indeed decoded the hash.

		let mut r = &Twox256::hash(&(&key).encode()[..])[..];
		assert_eq!(<Twox256 as StorageHasherInfo<KeyType>>::decode_hash_and_then_info(&mut r), Ok(()));
		assert_eq!(r.len(), 0); // Assert input has indeed decoded the hash.

		let mut r = &Blake2_128Concat::hash(&(&key).encode()[..])[..];
		assert_eq!(<Blake2_128Concat as StorageHasherInfo<KeyType>>::decode_hash_and_then_info(&mut r), Ok(key));
		assert_eq!(r.len(), 0); // Assert input has indeed decoded the hash.

		let mut r = &Blake2_128::hash(&(&key).encode()[..])[..];
		assert_eq!(<Blake2_128 as StorageHasherInfo<KeyType>>::decode_hash_and_then_info(&mut r), Ok(()));
		assert_eq!(r.len(), 0); // Assert input has indeed decoded the hash.

		let mut r = &Blake2_256::hash(&(&key).encode()[..])[..];
		assert_eq!(<Blake2_256 as StorageHasherInfo<KeyType>>::decode_hash_and_then_info(&mut r), Ok(()));
		assert_eq!(r.len(), 0); // Assert input has indeed decoded the hash.
	}
}
