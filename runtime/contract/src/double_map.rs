// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! An implementation of double map backed by storage.
//!
//! This implementation is somewhat specialized to the tracking of the storage of accounts.

use rstd::prelude::*;
use codec::{Codec, Encode};
use runtime_support::storage::unhashed;
use runtime_io::{blake2_256, twox_128};

/// Returns only a first part of the storage key.
///
/// Hashed by XX.
fn first_part_of_key<M: StorageDoubleMap + ?Sized>(k1: M::Key1) -> [u8; 16] {
	let mut raw_prefix = Vec::new();
	raw_prefix.extend(M::PREFIX);
	raw_prefix.extend(Encode::encode(&k1));
	twox_128(&raw_prefix)
}

/// Returns a compound key that consist of the two parts: (prefix, `k1`) and `k2`.
///
/// The first part is hased by XX and then concatenated with a blake2 hash of `k2`.
fn full_key<M: StorageDoubleMap + ?Sized>(k1: M::Key1, k2: M::Key2) -> Vec<u8> {
	let first_part = first_part_of_key::<M>(k1);
	let second_part = blake2_256(&Encode::encode(&k2));

	let mut k = Vec::new();
	k.extend(&first_part);
	k.extend(&second_part);
	k
}

/// An implementation of a map with a two keys.
///
/// It provides an important ability to efficiently remove all entries
/// that have a common first key.
///
/// # Mapping of keys to a storage path
///
/// The storage key (i.e. the key under which the `Value` will be stored) is created from two parts.
/// The first part is a XX hash of a concatenation of the `PREFIX` and `Key1`. And the second part
/// is a blake2 hash of a `Key2`.
///
/// Blake2 is used for `Key2` is because it will be used as a key for contract's storage and
/// thus will be susceptible for a untrusted input.
pub trait StorageDoubleMap {
	type Key1: Codec;
	type Key2: Codec;
	type Value: Codec + Default;

	const PREFIX: &'static [u8];

	/// Insert an entry into this map.
	fn insert(k1: Self::Key1, k2: Self::Key2, val: Self::Value) {
		unhashed::put(&full_key::<Self>(k1, k2)[..], &val);
	}

	/// Remove an entry from this map.
	fn remove(k1: Self::Key1, k2: Self::Key2) {
		unhashed::kill(&full_key::<Self>(k1, k2)[..]);
	}

	/// Get an entry from this map.
	///
	/// If there is entry stored under the given keys, returns `None`.
	fn get(k1: Self::Key1, k2: Self::Key2) -> Option<Self::Value> {
		unhashed::get(&full_key::<Self>(k1, k2)[..])
	}

	/// Removes all entries that shares the `k1` as the first key.
	fn remove_prefix(k1: Self::Key1) {
		unhashed::kill_prefix(&first_part_of_key::<Self>(k1))
	}
}
