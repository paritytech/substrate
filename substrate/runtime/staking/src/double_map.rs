// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//!

use rstd::prelude::*;
use codec::Slicable;
use runtime_support::storage::unhashed;
use runtime_io::{blake2_256, twox_128};

/// Returns only a first part of the storage key.
///
/// Hashed by XX.
fn first_part_of_key<M: StorageDoubleMap + ?Sized>(k1: M::Key1) -> [u8; 16] {
	let mut raw_prefix = Vec::new();
	raw_prefix.extend(M::PREFIX);
	raw_prefix.extend(Slicable::encode(&k1));
	twox_128(&raw_prefix)
}

/// Returns a compound key that consist of the two parts: (prefix, `k1`) and `k2`.
///
/// The first part is hased by XX and then concatenated with a blake2 hash of `k2`.
fn full_key<M: StorageDoubleMap + ?Sized>(k1: M::Key1, k2: M::Key2) -> Vec<u8> {
	let first_part = first_part_of_key::<M>(k1);
	let second_part = blake2_256(&Slicable::encode(&k2));

	let mut k = Vec::new();
	k.extend(&first_part);
	k.extend(&second_part);
	k
}

pub trait StorageDoubleMap {
	type Key1: Slicable;
	type Key2: Slicable;
	type Value: Slicable + Default;

	const PREFIX: &'static [u8];

	fn insert(k1: Self::Key1, k2: Self::Key2, val: Self::Value) {
		unhashed::put(&full_key::<Self>(k1, k2)[..], &val);
	}

	fn remove(k1: Self::Key1, k2: Self::Key2) {
		unhashed::kill(&full_key::<Self>(k1, k2)[..]);
	}

	fn get(k1: Self::Key1, k2: Self::Key2) -> Option<Self::Value> {
		unhashed::get(&full_key::<Self>(k1, k2)[..])
	}

	fn remove_prefix(k1: Self::Key1) {
		unhashed::kill_prefix(&first_part_of_key::<Self>(k1))
	}
}
