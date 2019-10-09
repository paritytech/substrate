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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use primitives::{
	blake2_128, blake2_256, twox_128, twox_256, twox_64, ed25519, Blake2Hasher, sr25519, Pair, H256,
	traits::KeystoreExt, storage::ChildStorageKey, hexdisplay::HexDisplay, Hasher,
	offchain::{self, OffchainExt},
};
// Switch to this after PoC-3
// pub use primitives::BlakeHasher;
pub use substrate_state_machine::{BasicExternalities, TestExternalities};

use trie::{TrieConfiguration, trie_types::Layout};

use std::{collections::HashMap, convert::TryFrom};

/// Additional bounds for `Hasher` trait for with_std.
pub trait HasherBounds {}
impl<T: Hasher> HasherBounds for T {}

/// Execute the given closure with global function available whose functionality routes into the
/// externalities `ext`. Forwards the value that the closure returns.
// NOTE: need a concrete hasher here due to limitations of the `environmental!` macro, otherwise a type param would have been fine I think.
pub fn with_externalities<R, F: FnOnce() -> R>(ext: &mut dyn Externalities<Blake2Hasher>, f: F) -> R {
	unimplemented!()
}

/// A set of key value pairs for storage.
pub type StorageOverlay = HashMap<Vec<u8>, Vec<u8>>;

/// A set of key value pairs for children storage;
pub type ChildrenStorageOverlay = HashMap<Vec<u8>, StorageOverlay>;

/// Execute the given closure with global functions available whose functionality routes into
/// externalities that draw from and populate `storage` and `children_storage`.
/// Forwards the value that the closure returns.
pub fn with_storage<R, F: FnOnce() -> R>(
	storage: &mut (StorageOverlay, ChildrenStorageOverlay),
	f: F
) -> R {
	let mut alt_storage = Default::default();
	rstd::mem::swap(&mut alt_storage, storage);

	let mut ext = BasicExternalities::new(alt_storage.0, alt_storage.1);
	// let r = ext::using(&mut ext, f);

	// *storage = ext.into_storages();

	// r

	unimplemented!()
}

#[cfg(test)]
mod std_tests {
	use super::*;
	use primitives::map;

	#[test]
	fn storage_works() {
		let mut t = BasicExternalities::default();
		assert!(set_and_run_with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), None);
			set_storage(b"hello", b"world");
			assert_eq!(storage(b"hello"), Some(b"world".to_vec()));
			assert_eq!(storage(b"foo"), None);
			set_storage(b"foo", &[1, 2, 3][..]);
			true
		}));

		t = BasicExternalities::new(map![b"foo".to_vec() => b"bar".to_vec()], map![]);

		assert!(!set_and_run_with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), None);
			assert_eq!(storage(b"foo"), Some(b"bar".to_vec()));
			false
		}));
	}

	#[test]
	fn read_storage_works() {
		let mut t = BasicExternalities::new(map![
			b":test".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		], map![]);

		set_and_run_with_externalities(&mut t, || {
			let mut v = [0u8; 4];
			assert!(read_storage(b":test", &mut v[..], 0).unwrap() >= 4);
			assert_eq!(v, [11u8, 0, 0, 0]);
			let mut w = [0u8; 11];
			assert!(read_storage(b":test", &mut w[..], 4).unwrap() >= 11);
			assert_eq!(&w, b"Hello world");
		});
	}

	#[test]
	fn clear_prefix_works() {
		let mut t = BasicExternalities::new(map![
			b":a".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abcd".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abc".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abdd".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		], map![]);

		set_and_run_with_externalities(&mut t, || {
			clear_prefix(b":abc");

			assert!(storage(b":a").is_some());
			assert!(storage(b":abdd").is_some());
			assert!(storage(b":abcd").is_none());
			assert!(storage(b":abc").is_none());
		});
	}
}
