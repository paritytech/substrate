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

#[macro_use]
extern crate environmental;

#[cfg_attr(test, macro_use)]
extern crate substrate_primitives as primitives;

extern crate substrate_state_machine;
extern crate triehash;
extern crate hashdb;
extern crate rlp;

#[doc(hidden)]
pub extern crate parity_codec as codec;
// re-export hashing functions.
pub use primitives::{blake2_256, twox_128, twox_256, ed25519};

pub use primitives::{Blake2Hasher, RlpCodec};
// Switch to this after PoC-3
// pub use primitives::BlakeHasher;
pub use substrate_state_machine::{Externalities, TestExternalities};
use primitives::hexdisplay::HexDisplay;
use primitives::H256;
use hashdb::Hasher;
use rlp::Encodable;

// TODO: use the real error, not NoError.

environmental!(ext: trait Externalities<Blake2Hasher>);

/// Get `key` from storage and return a `Vec`, empty if there's a problem.
pub fn storage(key: &[u8]) -> Option<Vec<u8>> {
	ext::with(|ext| ext.storage(key).map(|s| s.to_vec()))
		.expect("storage cannot be called outside of an Externalities-provided environment.")
}

/// Get `key` from storage, placing the value into `value_out` (as much of it as possible) and return
/// the number of bytes that the entry in storage had beyond the offset or None if the storage entry
/// doesn't exist at all. Note that if the buffer is smaller than the storage entry length, the returned
/// number of bytes is not equal to the number of bytes written to the `value_out`.
pub fn read_storage(key: &[u8], value_out: &mut [u8], value_offset: usize) -> Option<usize> {
	ext::with(|ext| ext.storage(key).map(|value| {
		let value = &value[value_offset..];
		let written = ::std::cmp::min(value.len(), value_out.len());
		value_out[0..written].copy_from_slice(&value[0..written]);
		value.len()
	})).expect("read_storage cannot be called outside of an Externalities-provided environment.")
}

/// Set the storage of a key to some value.
pub fn set_storage(key: &[u8], value: &[u8]) {
	ext::with(|ext|
		ext.set_storage(key.to_vec(), value.to_vec())
	);
}

/// Clear the storage of a key.
pub fn clear_storage(key: &[u8]) {
	ext::with(|ext|
		ext.clear_storage(key)
	);
}

/// Check whether a given `key` exists in storage.
pub fn exists_storage(key: &[u8]) -> bool {
	ext::with(|ext|
		ext.exists_storage(key)
	).unwrap_or(false)
}

/// Clear the storage entries with a key that starts with the given prefix.
pub fn clear_prefix(prefix: &[u8]) {
	ext::with(|ext|
		ext.clear_prefix(prefix)
	);
}

/// The current relay chain identifier.
pub fn chain_id() -> u64 {
	ext::with(|ext|
		ext.chain_id()
	).unwrap_or(0)
}

/// "Commit" all existing operations and compute the resultant storage root.
pub fn storage_root() -> H256 {
	ext::with(|ext|
		ext.storage_root()
	).unwrap_or(H256::new())
}

/// "Commit" all existing operations and get the resultant storage change root.
pub fn storage_changes_root(block: u64) -> Option<H256> {
	ext::with(|ext|
		ext.storage_changes_root(block)
	).unwrap_or(None)
}

/// A trie root formed from the enumerated items.
pub fn enumerated_trie_root<H>(serialised_values: &[&[u8]]) -> H::Out
where
	H: Hasher,
	H::Out: Encodable + Ord,
{
	triehash::ordered_trie_root::<H, _, _>(serialised_values.iter().map(|s| s.to_vec()))
}

/// A trie root formed from the iterated items.
pub fn trie_root<H, I, A, B>(input: I) -> H::Out
where
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
	H: Hasher,
	<H as Hasher>::Out: Encodable + Ord,
{
	triehash::trie_root::<H, _, _, _>(input)
}

/// A trie root formed from the enumerated items.
pub fn ordered_trie_root<H, I, A>(input: I) -> H::Out
where
	I: IntoIterator<Item = A>,
	A: AsRef<[u8]>,
	H: Hasher,
	<H as Hasher>::Out: Encodable + Ord,
{
	triehash::ordered_trie_root::<H, _, _>(input)
}

/// Verify a ed25519 signature.
pub fn ed25519_verify<P: AsRef<[u8]>>(sig: &[u8; 64], msg: &[u8], pubkey: P) -> bool {
	ed25519::verify(sig, msg, pubkey)
}

/// Execute the given closure with global function available whose functionality routes into the
/// externalities `ext`. Forwards the value that the closure returns.
// NOTE: need a concrete hasher here due to limitations of the `environmental!` macro, otherwise a type param would have been fine I think.
pub fn with_externalities<R, F: FnOnce() -> R>(ext: &mut Externalities<Blake2Hasher>, f: F) -> R {
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
	( $( $new_name:ident $($nodecode:ident)* => $invoke: expr ),*) => {
		/// Dispatch logic for the native runtime.
		pub fn dispatch(method: &str, data: &[u8]) -> Option<Vec<u8>> {
			match method {
				$(
					stringify!($new_name) => { impl_stubs!(@METHOD data $new_name $($nodecode)* => $invoke) }
				)*
				_ => None,
			}
		}
	};
	(@METHOD $data: ident $new_name: ident NO_DECODE => $invoke:expr) => {
		Some($invoke($data))
	};
	(@METHOD $data: ident $new_name: ident => $invoke:expr) => {{
		let mut data = $data;
		let input = match $crate::codec::Decode::decode(&mut data) {
			Some(input) => input,
			None => panic!("Bad input data provided to {}", stringify!($new_name)),
		};

		let output = $invoke(input);
		Some($crate::codec::Encode::encode(&output))
	}}
}

#[cfg(test)]
mod std_tests {
	use super::*;

	#[test]
	fn storage_works() {
		let mut t = TestExternalities::<Blake2Hasher, RlpCodec>::default();
		assert!(with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), None);
			set_storage(b"hello", b"world");
			assert_eq!(storage(b"hello"), Some(b"world".to_vec()));
			assert_eq!(storage(b"foo"), None);
			set_storage(b"foo", &[1, 2, 3][..]);
			true
		}));

		t = TestExternalities::new(map![b"foo".to_vec() => b"bar".to_vec()]);

		assert!(!with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), None);
			assert_eq!(storage(b"foo"), Some(b"bar".to_vec()));
			false
		}));
	}

	#[test]
	fn read_storage_works() {
		let mut t = TestExternalities::<Blake2Hasher, RlpCodec>::new(map![
			b":test".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		]);

		with_externalities(&mut t, || {
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
		let mut t = TestExternalities::<Blake2Hasher, RlpCodec>::new(map![
			b":a".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abcd".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abc".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abdd".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		]);

		with_externalities(&mut t, || {
			clear_prefix(b":abc");

			assert!(storage(b":a").is_some());
			assert!(storage(b":abdd").is_some());
			assert!(storage(b":abcd").is_none());
			assert!(storage(b":abc").is_none());
		});
	}
}
