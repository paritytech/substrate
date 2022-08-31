// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Some utilities for helping access storage with arbitrary key types.

use sp_std::prelude::*;
use codec::{Encode, Decode};
use crate::{StorageHasher, Twox128};
use crate::hash::ReversibleStorageHasher;

/// Utility to iterate through raw items in storage.
pub struct StorageIterator<T> {
	prefix: Vec<u8>,
	previous_key: Vec<u8>,
	drain: bool,
	_phantom: ::sp_std::marker::PhantomData<T>,
}

impl<T> StorageIterator<T> {
	/// Construct iterator to iterate over map items in `module` for the map called `item`.
	pub fn new(module: &[u8], item: &[u8]) -> Self {
		Self::with_suffix(module, item, &[][..])
	}

	/// Construct iterator to iterate over map items in `module` for the map called `item`.
	pub fn with_suffix(module: &[u8], item: &[u8], suffix: &[u8]) -> Self {
		let mut prefix = Vec::new();
		prefix.extend_from_slice(&Twox128::hash(module));
		prefix.extend_from_slice(&Twox128::hash(item));
		prefix.extend_from_slice(suffix);
		let previous_key = prefix.clone();
		Self { prefix, previous_key, drain: false, _phantom: Default::default() }
	}

	/// Mutate this iterator into a draining iterator; items iterated are removed from storage.
	pub fn drain(mut self) -> Self {
		self.drain = true;
		self
	}
}

impl<T: Decode + Sized> Iterator for StorageIterator<T> {
	type Item = (Vec<u8>, T);

	fn next(&mut self) -> Option<(Vec<u8>, T)> {
		loop {
			let maybe_next = sp_io::storage::next_key(&self.previous_key)
				.filter(|n| n.starts_with(&self.prefix));
			break match maybe_next {
				Some(next) => {
					self.previous_key = next.clone();
					let maybe_value = frame_support::storage::unhashed::get::<T>(&next);
					match maybe_value {
						Some(value) => {
							if self.drain {
								frame_support::storage::unhashed::kill(&next);
							}
							Some((self.previous_key[self.prefix.len()..].to_vec(), value))
						}
						None => continue,
					}
				}
				None => None,
			}
		}
	}
}

/// Utility to iterate through raw items in storage.
pub struct StorageKeyIterator<K, T, H: ReversibleStorageHasher> {
	prefix: Vec<u8>,
	previous_key: Vec<u8>,
	drain: bool,
	_phantom: ::sp_std::marker::PhantomData<(K, T, H)>,
}

impl<K, T, H: ReversibleStorageHasher> StorageKeyIterator<K, T, H> {
	/// Construct iterator to iterate over map items in `module` for the map called `item`.
	pub fn new(module: &[u8], item: &[u8]) -> Self {
		Self::with_suffix(module, item, &[][..])
	}

	/// Construct iterator to iterate over map items in `module` for the map called `item`.
	pub fn with_suffix(module: &[u8], item: &[u8], suffix: &[u8]) -> Self {
		let mut prefix = Vec::new();
		prefix.extend_from_slice(&Twox128::hash(module));
		prefix.extend_from_slice(&Twox128::hash(item));
		prefix.extend_from_slice(suffix);
		let previous_key = prefix.clone();
		Self { prefix, previous_key, drain: false, _phantom: Default::default() }
	}

	/// Mutate this iterator into a draining iterator; items iterated are removed from storage.
	pub fn drain(mut self) -> Self {
		self.drain = true;
		self
	}
}

impl<K: Decode + Sized, T: Decode + Sized, H: ReversibleStorageHasher> Iterator
	for StorageKeyIterator<K, T, H>
{
	type Item = (K, T);

	fn next(&mut self) -> Option<(K, T)> {
		loop {
			let maybe_next = sp_io::storage::next_key(&self.previous_key)
				.filter(|n| n.starts_with(&self.prefix));
			break match maybe_next {
				Some(next) => {
					self.previous_key = next.clone();
					let mut key_material = H::reverse(&next[self.prefix.len()..]);
					match K::decode(&mut key_material) {
						Ok(key) => {
							let maybe_value = frame_support::storage::unhashed::get::<T>(&next);
							match maybe_value {
								Some(value) => {
									if self.drain {
										frame_support::storage::unhashed::kill(&next);
									}
									Some((key, value))
								}
								None => continue,
							}
						}
						Err(_) => continue,
					}
				}
				None => None,
			}
		}
	}
}

/// Get a particular value in storage by the `module`, the map's `item` name and the key `hash`.
pub fn have_storage_value(module: &[u8], item: &[u8], hash: &[u8]) -> bool {
	get_storage_value::<()>(module, item, hash).is_some()
}

/// Get a particular value in storage by the `module`, the map's `item` name and the key `hash`.
pub fn get_storage_value<T: Decode + Sized>(module: &[u8], item: &[u8], hash: &[u8]) -> Option<T> {
	let mut key = vec![0u8; 32 + hash.len()];
	key[0..16].copy_from_slice(&Twox128::hash(module));
	key[16..32].copy_from_slice(&Twox128::hash(item));
	key[32..].copy_from_slice(hash);
	frame_support::storage::unhashed::get::<T>(&key)
}

/// Take a particular value in storage by the `module`, the map's `item` name and the key `hash`.
pub fn take_storage_value<T: Decode + Sized>(module: &[u8], item: &[u8], hash: &[u8]) -> Option<T> {
	let mut key = vec![0u8; 32 + hash.len()];
	key[0..16].copy_from_slice(&Twox128::hash(module));
	key[16..32].copy_from_slice(&Twox128::hash(item));
	key[32..].copy_from_slice(hash);
	frame_support::storage::unhashed::take::<T>(&key)
}

/// Put a particular value into storage by the `module`, the map's `item` name and the key `hash`.
pub fn put_storage_value<T: Encode>(module: &[u8], item: &[u8], hash: &[u8], value: T) {
	let mut key = vec![0u8; 32 + hash.len()];
	key[0..16].copy_from_slice(&Twox128::hash(module));
	key[16..32].copy_from_slice(&Twox128::hash(item));
	key[32..].copy_from_slice(hash);
	frame_support::storage::unhashed::put(&key, &value);
}

/// Get a particular value in storage by the `module`, the map's `item` name and the key `hash`.
pub fn remove_storage_prefix(module: &[u8], item: &[u8], hash: &[u8]) {
	let mut key = vec![0u8; 32 + hash.len()];
	key[0..16].copy_from_slice(&Twox128::hash(module));
	key[16..32].copy_from_slice(&Twox128::hash(item));
	key[32..].copy_from_slice(hash);
	frame_support::storage::unhashed::kill_prefix(&key)
}

/// Get a particular value in storage by the `module`, the map's `item` name and the key `hash`.
pub fn take_storage_item<K: Encode + Sized, T: Decode + Sized, H: StorageHasher>(
	module: &[u8],
	item: &[u8],
	key: K,
) -> Option<T> {
	take_storage_value(module, item, key.using_encoded(H::hash).as_ref())
}
