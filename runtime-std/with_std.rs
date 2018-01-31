// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.


#[macro_use]
extern crate environmental;

extern crate polkadot_state_machine;
extern crate polkadot_primitives as primitives;
extern crate triehash;

use std::fmt;
use primitives::ed25519;

pub use std::vec;
pub use std::rc;
pub use std::cell;
pub use std::boxed;
pub use std::slice;
pub use std::mem;

pub use polkadot_state_machine::{Externalities, ExternalitiesError, TestExternalities};
use primitives::hexdisplay::HexDisplay;

// TODO: use the real error, not NoError.

#[derive(Debug)]
/// As it says - an empty type we use for errors.
pub struct NoError;
impl fmt::Display for NoError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "") }
}

environmental!(ext : trait Externalities);

/// Get `key` from storage and return a `Vec`, empty if there's a problem.
pub fn storage(key: &[u8]) -> Vec<u8> {
	ext::with(|ext| ext.storage(key).ok().map(|s| s.to_vec()))
		.expect("read_storage cannot be called outside of an Externalities-provided environment.")
		.unwrap_or_else(Vec::new)
}

/// Get `key` from storage, placing the value into `value_out` (as much as possible) and return
/// the number of bytes that the key in storage was.
pub fn read_storage(key: &[u8], value_out: &mut [u8], value_offset: usize) -> usize {
	ext::with(|ext| {
		if let Ok(value) = ext.storage(key) {
			let value = &value[value_offset..];
			let written = ::std::cmp::min(value.len(), value_out.len());
			value_out[0..written].copy_from_slice(&value[0..written]);
			value.len()
		} else {
			// no-entry is treated as an empty vector of bytes.
			// TODO: consider allowing empty-vector to exist separately to no-entry (i.e. return
			// Option<usize>)
			0
		}
	}).expect("read_storage cannot be called outside of an Externalities-provided environment.")
}

/// Set the storage to some particular key.
pub fn set_storage(key: &[u8], value: &[u8]) {
	ext::with(|ext|
		ext.set_storage(key.to_vec(), value.to_vec())
	);
}

/// The current relay chain identifier.
pub fn chain_id() -> u64 {
	ext::with(|ext|
		ext.chain_id()
	).unwrap_or(0)
}

/// "Commit" all existing operations and get the resultant storage root.
pub fn storage_root() -> [u8; 32] {
	ext::with(|ext|
		ext.storage_root()
	).unwrap_or([0u8; 32])
}

/// "Commit" all existing operations and get the resultant storage root.
pub fn enumerated_trie_root(serialised_values: &[&[u8]]) -> [u8; 32] {
	triehash::ordered_trie_root(serialised_values.iter().map(|s| s.to_vec())).0
}

/// Conduct a Keccak-256 hash of the given data.
pub use primitives::{blake2_256, twox_128, twox_256};

/// Verify a ed25519 signature.
pub fn ed25519_verify(sig: &[u8; 64], msg: &[u8], pubkey: &[u8; 32]) -> bool {
	ed25519::verify(&sig[..], msg, &pubkey[..])
}

/// Execute the given closure with global function available whose functionality routes into the
/// externalities `ext`. Forwards the value that the closure returns.
pub fn with_externalities<R, F: FnOnce() -> R>(ext: &mut Externalities, f: F) -> R {
	ext::using(ext, f)
}

/// Trait for things which can be printed.
pub trait Printable {
	fn print(self);
}

impl<'a> Printable for &'a [u8] {
	fn print(self) {
		println!("Runtime: {}", HexDisplay::from(&self));
	}
}

impl<'a> Printable for &'a str {
	fn print(self) {
		println!("Runtime: {}", self);
	}
}

impl Printable for u64 {
	fn print(self) {
		println!("Runtime: {}", self);
	}
}

/// Print a printable value.
pub fn print<T: Printable + Sized>(value: T) {
	value.print();
}

#[macro_export]
macro_rules! impl_stubs {
	($( $name:ident ),*) => {}
}

#[cfg(test)]
mod tests {
	use super::*;

	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	#[test]
	fn storage_works() {
		let mut t = TestExternalities { storage: map![], };
		assert!(with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), b"".to_vec());
			set_storage(b"hello", b"world");
			assert_eq!(storage(b"hello"), b"world".to_vec());
			assert_eq!(storage(b"foo"), b"".to_vec());
			set_storage(b"foo", &[1, 2, 3][..]);
			true
		}));

		t.storage = map![b"foo".to_vec() => b"bar".to_vec()];

		assert!(!with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), b"".to_vec());
			assert_eq!(storage(b"foo"), b"bar".to_vec());
			false
		}));
	}

	#[test]
	fn read_storage_works() {
		let mut t = TestExternalities { storage: map![
			b":test".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		], };

		with_externalities(&mut t, || {
			let mut v = [0u8; 4];
			assert!(read_storage(b":test", &mut v[..], 0) >= 4);
			assert_eq!(v, [11u8, 0, 0, 0]);
			let mut w = [0u8; 11];
			assert!(read_storage(b":test", &mut w[..], 4) >= 11);
			assert_eq!(&w, b"Hello world");
		});
	}
}
