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
extern crate ed25519;

#[doc(hidden)]
pub extern crate substrate_codec as codec;
// re-export hashing functions.
pub use primitives::{blake2_256, twox_128, twox_256};

pub use substrate_state_machine::{Externalities, TestExternalities};
use primitives::hexdisplay::HexDisplay;
use prefix::{DELETED_SET_KEY_PREFIX, is_prefix_configured, add_prefix,
	strip_prefix, read_prefix_len, purge, schedule_purge};

// TODO: use the real error, not NoError.

environmental!(ext: trait Externalities);

/// Set storage values prefix.
pub fn set_storage_prefix(prefix: &[u8]) {
	ext::with(|ext| {
		// both branches in following match could be implemented later, but it will involve
		// upgrading the whole storage
		match read_prefix_len(ext) {
			// do nothing if we're not configured to work with prefix
			None => return,
			// check that new prefix length is the same as we configured for
			Some(existing_prefix_len) => assert_eq!(
				prefix.len(),
				existing_prefix_len as usize,
				"Change of prefix length is not currently supported"),
		};

		let mut prefixed_prefix = prefix.to_vec();
		prefixed_prefix.extend_from_slice(prefix);

		ext.set_storage(PREFIX_KEY.to_vec(), prefixed_prefix)
	});
}

/// Purge scheduled entries from the storage.
pub fn purge_storage<F: Fn(&[u8], Option<Vec<u8>>, Option<Vec<u8>>) -> PurgeFilterResult>(f: F) {
	ext::with(|ext| {
		if is_prefix_configured(ext) {
			purge(ext, f)
		}
	});
}

/// Get `key` from storage and return a `Vec`, empty if there's a problem.
pub fn storage(key: &[u8]) -> Option<Vec<u8>> {
	ext::with(|ext| ext.storage(key)
			.and_then(|v| strip_prefix(ext, v).1))
		.expect("storage cannot be called outside of an Externalities-provided environment.")
}

/// Get `key` prefix from storage and return a `Vec`, empty if storage prefix is not configured.
pub fn storage_prefix(key: &[u8]) -> Option<Vec<u8>> {
	ext::with(|ext| ext.storage(key)
			.and_then(|v| strip_prefix(ext, v).0))
		.expect("storage_prefix cannot be called outside of an Externalities-provided environment.")
}

/// Get `key` from storage, placing the value into `value_out` (as much as possible) and return
/// the number of bytes that the key in storage was beyond the offset or None if the storage entry
/// doesn't exist at all.
pub fn read_storage(key: &[u8], value_out: &mut [u8], value_offset: usize) -> Option<usize> {
	ext::with(|ext| ext.storage(key)
		.and_then(|v| strip_prefix(ext, v).1)
		.map(|value| {
			let value = &value[value_offset..];
			let written = ::std::cmp::min(value.len(), value_out.len());
			value_out[0..written].copy_from_slice(&value[0..written]);
			value.len()
		})).expect("read_storage cannot be called outside of an Externalities-provided environment.")
}

/// Set the storage of some particular key to Some value.
pub fn set_storage(key: &[u8], value: &[u8]) {
	ext::with(|ext| {
		let prefixed_value = add_prefix(ext, value);
		ext.set_storage(key.to_vec(), prefixed_value);
	});
}

/// Clear the storage of some particular key.
pub fn clear_storage(key: &[u8]) {
	ext::with(|ext| {
		let empty_value = add_prefix(ext, &[]);
		// if we do not use prefix OR value has been created + deleted in the same block => just remove
		if empty_value.is_empty() || !ext.exists_previous_storage(key) {
			ext.clear_storage(key)
		} else {
			schedule_purge(ext, key);
			ext.set_storage(key.to_vec(), empty_value)
		}
	});
}

/// Check whether a given `key` exists in storage.
pub fn exists_storage(key: &[u8]) -> bool {
	ext::with(|ext|
		if !is_prefix_configured(ext) {
			ext.exists_storage(key)
		} else {
			ext.storage(key)
				.map(|v| strip_prefix(ext, v).1.is_some())
				.unwrap_or(false)
		}

	).unwrap_or(false)
}

/// Clear the storage entries key of which starts with the given prefix.
pub fn clear_prefix(prefix: &[u8]) {
	ext::with(|ext| {
		let empty_value = add_prefix(ext, &[]);
		if empty_value.is_empty() {
			ext.clear_prefix(prefix)
		} else {
			ext.save_pefix_keys(false, prefix, DELETED_SET_KEY_PREFIX);
			ext.set_prefix(false, prefix, empty_value)
		}
	});
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

/// A trie root formed from the enumerated items.
pub fn enumerated_trie_root(serialised_values: &[&[u8]]) -> [u8; 32] {
	triehash::ordered_trie_root(serialised_values.iter().map(|s| s.to_vec())).0
}

/// A trie root formed from the iterated items.
pub fn trie_root<
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
>(input: I) -> [u8; 32] {
	triehash::trie_root(input).0
}

/// A trie root formed from the enumerated items.
pub fn ordered_trie_root<
	I: IntoIterator<Item = A>,
	A: AsRef<[u8]>
>(input: I) -> [u8; 32] {
	triehash::ordered_trie_root(input).0
}

/// Verify a ed25519 signature.
pub fn ed25519_verify<P: AsRef<[u8]>>(sig: &[u8; 64], msg: &[u8], pubkey: P) -> bool {
	ed25519::verify(sig, msg, pubkey)
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

pub(crate) mod raw {
	use substrate_state_machine::Externalities;

	/// Get raw `key` from storage and return a `Vec`, empty if there's a problem.
	pub fn storage(ext: &Externalities, key: &[u8]) -> Option<Vec<u8>> {
		ext.storage(key)
	}

	/// Get cached raw `key` from storage and return a `Vec`, empty if there's a problem.
	pub fn cached_storage(ext: &Externalities, key: &[u8]) -> Option<Vec<u8>> {
		ext.cached_storage(key)
	}

	/// Set the storage of some particular key to Some value.
	pub fn set_storage(ext: &mut Externalities, key: &[u8], value: &[u8]) {
		ext.set_storage(key.to_vec(), value.to_vec());
	}

	/// Clear the storage of some particular key.
	pub fn clear_storage(ext: &mut Externalities, key: &[u8]) {
		ext.clear_storage(key)
	}
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
		let mut t = TestExternalities::default();
		assert!(with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), None);
			set_storage(b"hello", b"world");
			assert_eq!(storage(b"hello"), Some(b"world".to_vec()));
			assert_eq!(storage(b"foo"), None);
			set_storage(b"foo", &[1, 2, 3][..]);
			true
		}));

		t = map![b"foo".to_vec() => b"bar".to_vec()];

		assert!(!with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), None);
			assert_eq!(storage(b"foo"), Some(b"bar".to_vec()));
			false
		}));
	}

	#[test]
	fn read_storage_works() {
		let mut t: TestExternalities = map![
			b":test".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		];

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
		let mut t: TestExternalities = map![
			b":a".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abcd".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abc".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abdd".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		];

		with_externalities(&mut t, || {
			clear_prefix(b":abc");

			assert!(storage(b":a").is_some());
			assert!(storage(b":abdd").is_some());
			assert!(storage(b":abcd").is_none());
			assert!(storage(b":abc").is_none());
		});
	}
}
