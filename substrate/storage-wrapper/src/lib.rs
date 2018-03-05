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

//! Strongly typed wrappers around values in storage.
//!
//! This crate exports a macro `storage_items!` and traits describing behavior of generated
//! structs.
//!
//! Three kinds of data types are currently supported:
//!   - values
//!   - maps
//!   - lists
//!
//! # Examples:
//!
//! ```rust
//! #[macro_use]
//! extern crate substrate_storage_wrapper;
//!
//! type AuthorityId = [u8; 32];
//! type Balance = u64;
//! pub type SessionKey = [u8; 32];
//!
//! storage_items! {
//!     // public value
//!     pub Value: b"stored_key" => SessionKey;
//!     // private map.
//!     Balances: b"private_map:" => map [AuthorityId => Balance];
//!     // private list.
//!     Authorities: b"auth:" => list [AuthorityId];
//! }
//!
//!# fn main() { }
//! ```

#[doc(hidden)]
pub extern crate substrate_codec as codec;

/// Abstraction around storage.
pub trait Storage {
	/// Load the bytes of a key from storage. Can panic if the type is incorrect.
	fn load<T: codec::Slicable>(&self, key: &[u8]) -> Option<T>;

	/// Put a value in under a key.
	fn store<T: codec::Slicable>(&self, key: &[u8], val: &T);

	/// Remove the bytes of a key from storage.
	fn kill(&self, key: &[u8]);

	/// Take a value from storage, deleting it after reading.
	fn take<T: codec::Slicable>(&self, key: &[u8]) -> Option<T> {
		let value = self.load(key);
		self.kill(key);
		value
	}
}

/// A strongly-typed value kept in storage.
pub trait StorageValue<T: codec::Slicable> {
	/// Get the storage key.
	fn key() -> &'static [u8];
	/// Load the value from the provided storage instance.
	fn load_from<S: Storage>(storage: &S) -> Option<T>;
	/// Store a value under this key into the provded storage instance.
	fn store_into<S: Storage>(val: &T, storage: &S);
	/// Clear the storage value.
	fn kill<S: Storage>(storage: &S);
}

/// A strongly-typed list in storage.
pub trait StorageList<T: codec::Slicable> {
	/// Get the prefix key in storage.
	fn prefix() -> &'static [u8];

	/// Get the key used to store the length field.
	fn len_key() -> Vec<u8>;

	/// Get the storage key used to fetch a value at a given index.
	fn key_for(index: u32) -> Vec<u8>;

	/// Read out all the items.
	fn items<S: Storage>(storage: &S) -> Vec<T>;

	/// Set the current set of items.
	fn set_items<S: Storage>(items: &[T], storage: &S);

	/// Set the item at the given index.
	fn set_item<S: Storage>(index: u32, item: &T, storage: &S);

	/// Load the value at given index. Returns `None` if the index is out-of-bounds.
	fn get<S: Storage>(index: u32, storage: &S) -> Option<T>;

	/// Load the length of the list
	fn len<S: Storage>(storage: &S) -> u32;

	/// Clear the list.
	fn clear<S: Storage>(storage: &S);
}

/// A strongly-typed map in storage.
pub trait StorageMap<K: codec::Slicable, V: codec::Slicable> {
	/// Get the prefix key in storage.
	fn prefix() -> &'static [u8];

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn key_for(x: &K) -> Vec<u8>;

	/// Load the value associated with the given key from the map.
	fn load_from<S: Storage>(key: &K, storage: &S) -> Option<V>;

	/// Store a value to be associated with the given key from the map.
	fn store_into<S: Storage>(key: &K, val: &V, storage: &S);
}

#[macro_export]
#[doc(hidden)]
macro_rules! __storage_items_internal {
	// generator for values.
	(($($vis:tt)*) $name: ident: $key: expr => $ty:ty) => {
		$($vis)* struct $name;

		#[allow(unused)]
		impl $name {
			/// Get the storage key.
			$($vis)* fn key() -> &'static [u8] {
				$key
			}

			/// Load the value from the provided storage instance.
			$($vis)* fn load_from<S: $crate::Storage>(storage: &S) -> Option<$ty> {
				storage.load($key)
			}

			/// Store a value under this key into the provded storage instance.
			$($vis)* fn store_into<S: $crate::Storage>(val: &$ty, storage: &S) {
				storage.store($key, val)
			}

			/// Kill the value.
			$($vis)* fn kill<S: $crate::Storage>(storage: &S) {
				storage.kill($key)
			}
		}

		impl $crate::StorageValue<$ty> for $name {
			fn key() -> &'static [u8] {
				$key
			}

			fn load_from<S: $crate::Storage>(storage: &S) -> Option<$ty> {
				$name::load_from(storage)
			}

			fn store_into<S: $crate::Storage>(val: &$ty, storage: &S) {
				$name::store_into(val, storage)
			}

			fn kill<S: $crate::Storage>(storage: &S) {
				$name::kill(storage)
			}
		}
	};
	// generator for maps.
	(($($vis:tt)*) $name: ident: $prefix: expr => map [$kty: ty => $ty:ty]) => {
		$($vis)* struct $name;

		#[allow(unused)]
		impl $name {
			/// Get the prefix key in storage.
			$($vis)* fn prefix() -> &'static [u8] {
				$prefix
			}

			/// Get the storage key used to fetch a value corresponding to a specific key.
			$($vis)* fn key_for(x: &$kty) -> Vec<u8> {
				let mut key = $prefix.to_vec();
				key.extend($crate::codec::Slicable::encode(x));
				key
			}

			/// Load the value associated with the given key from the map.
			$($vis)* fn load_from<S: $crate::Storage>(key: &$kty, storage: &S) -> Option<$ty> {
				let key = $name::key_for(key);
				storage.load(&key[..])
			}

			/// Store a value to be associated with the given key from the map.
			$($vis)* fn store_into<S: $crate::Storage>(key: &$kty, val: &$ty, storage: &S) {
				let key = $name::key_for(key);
				storage.store(&key[..], val);
			}
		}

		impl $crate::StorageMap<$kty, $ty> for $name {
			fn prefix() -> &'static [u8] {
				$prefix
			}

			fn key_for(x: &$kty) -> Vec<u8> {
				$name::key_for(x)
			}

			fn load_from<S: $crate::Storage>(key: &$kty, storage: &S) -> Option<$ty> {
				$name::load_from(key, storage)
			}

			fn store_into<S: $crate::Storage>(key: &$kty, val: &$ty, storage: &S) {
				$name::store_into(key, val, storage)
			}
		}
	};
	// generator for lists.
	(($($vis:tt)*) $name: ident: $prefix: expr => list [$ty:ty]) => {
		$($vis)* struct $name;

		#[allow(unused)]
		impl $name {
			/// Get the prefix key in storage.
			$($vis)* fn prefix() -> &'static [u8] {
				$prefix
			}

			/// Get the key used to store the length field.
			// TODO: concat macro should accept byte literals.
			$($vis)* fn len_key() -> Vec<u8> {
				let mut key = $prefix.to_vec();
				key.extend(b"len");
				key
			}

			/// Get the storage key used to fetch a value at a given index.
			$($vis)* fn key_for(index: u32) -> Vec<u8> {
				let mut key = $prefix.to_vec();
				key.extend($crate::codec::Slicable::encode(&index));
				key
			}

			/// Read out all the items.
			$($vis)* fn items<S: $crate::Storage>(storage: &S) -> Vec<$ty> {
				(0..$name::len(storage))
					.map(|i| $name::get(i, storage).expect("all items within length are set; qed"))
					.collect()
			}

			/// Set the current set of items.
			$($vis)* fn set_items<S: $crate::Storage>(items: &[$ty], storage: &S) {
				$name::set_len(items.len() as u32, storage);
				items.iter()
					.enumerate()
					.for_each(|(i, item)| $name::set_item(i as u32, item, storage));
			}

			$($vis)* fn set_item<S: $crate::Storage>(index: u32, item: &$ty, storage: &S) {
				if index < $name::len(storage) {
					storage.store(&$name::key_for(index)[..], item);
				}
			}

			/// Load the value at given index. Returns `None` if the index is out-of-bounds.
			$($vis)* fn get<S: $crate::Storage>(index: u32, storage: &S) -> Option<$ty> {
				storage.load(&$name::key_for(index)[..])
			}

			/// Load the length of the list.
			$($vis)* fn len<S: $crate::Storage>(storage: &S) -> u32 {
				storage.load(&$name::len_key()).unwrap_or_default()
			}

			/// Clear the list.
			$($vis)* fn clear<S: $crate::Storage>(storage: &S) {
				for i in 0..$name::len(storage) {
					$name::clear_item(i, storage);
				}

				storage.kill(&$name::len_key()[..])
			}

			fn clear_item<S: $crate::Storage>(index: u32, storage: &S) {
				if index < $name::len(storage) {
					storage.kill(&$name::key_for(index));
				}
			}

			fn set_len<S: $crate::Storage>(count: u32, storage: &S) {
				(count..$name::len(storage)).for_each(|i| $name::clear_item(i, storage));
				storage.store(&$name::len_key(), &count);
			}
		}

		impl $crate::StorageList<$ty> for $name {
			/// Get the prefix key in storage.
			fn prefix() -> &'static [u8] {
				$prefix
			}

			/// Get the key used to store the length field.
			// TODO: concat macro should accept byte literals.
			fn len_key() -> Vec<u8> {
				$name::len_key()
			}

			/// Get the storage key used to fetch a value at a given index.
			fn key_for(index: u32) -> Vec<u8> {
				$name::key_for(index)
			}

			/// Read out all the items.
			fn items<S: $crate::Storage>(storage: &S) -> Vec<$ty> {
				$name::items(storage)
			}

			/// Set the current set of items.
			fn set_items<S: $crate::Storage>(items: &[$ty], storage: &S) {
				$name::set_items(items, storage)
			}

			fn set_item<S: $crate::Storage>(index: u32, item: &$ty, storage: &S) {
				$name::set_item(index, item, storage)
			}

			/// Load the value at given index. Returns `None` if the index is out-of-bounds.
			fn get<S: $crate::Storage>(index: u32, storage: &S) -> Option<$ty> {
				$name::get(index, storage)
			}

			fn len<S: $crate::Storage>(storage: &S) -> u32 {
				$name::len(storage)
			}

			fn clear<S: $crate::Storage>(storage: &S) {
				$name::clear(storage)
			}
		}
	};
}

/// Declares strongly-typed wrappers around codec-compatible types in storage.
#[macro_export]
macro_rules! storage_items {
	// simple values
	($name: ident: $key: expr => $ty:ty; $($t:tt)*) => {
		__storage_items_internal!(() $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name: ident: $key: expr => $ty:ty; $($t:tt)*) => {
		__storage_items_internal!((pub) $name: $key => $ty);
		storage_items!($($t)*);
	};
	// maps
	($name: ident: $prefix: expr => map [$kty: ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!(() $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name: ident: $prefix: expr => map [$kty: ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!((pub) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	// lists
	($name: ident: $prefix: expr => list [$ty:ty]; $($t:tt)*) => {
		__storage_items_internal!(() $name: $prefix => list [$ty]);
		storage_items!($($t)*);
	};
	(pub $name: ident: $prefix: expr => list [$ty:ty]; $($t:tt)*) => {
		__storage_items_internal!((pub) $name: $prefix => list [$ty]);
		storage_items!($($t)*);
	};
	() => ()
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;
	use std::cell::RefCell;
	use codec::Slicable;
	use super::*;

	impl Storage for RefCell<HashMap<Vec<u8>, Vec<u8>>> {
		fn load<T: Slicable>(&self, key: &[u8]) -> Option<T> {
			self.borrow_mut().get(key).map(|v| T::decode(&mut &v[..]).unwrap())
		}

		fn store<T: Slicable>(&self, key: &[u8], val: &T) {
			self.borrow_mut().insert(key.to_owned(), val.encode());
		}

		fn kill(&self, key: &[u8]) {
			self.borrow_mut().remove(key);
		}
	}

	storage_items! {
		Value: b"a" => u32;
		List: b"b:" => list [u64];
	}

    #[test]
	fn value() {
		let storage = RefCell::new(HashMap::new());
		assert!(Value::load_from(&storage).is_none());
		Value::store_into(&100_000, &storage);
		assert_eq!(Value::load_from(&storage), Some(100_000));
		Value::kill(&storage);
		assert!(Value::load_from(&storage).is_none());
	}

	#[test]
	fn list() {
		let storage = RefCell::new(HashMap::new());
		assert_eq!(List::len(&storage), 0);
		assert!(List::items(&storage).is_empty());

		List::set_items(&[0, 2, 4, 6, 8], &storage);
		assert_eq!(List::items(&storage), &[0, 2, 4, 6, 8]);
		assert_eq!(List::len(&storage), 5);

		List::set_item(2, &10, &storage);
		assert_eq!(List::items(&storage), &[0, 2, 10, 6, 8]);
		assert_eq!(List::len(&storage), 5);

		List::clear(&storage);
		assert_eq!(List::len(&storage), 0);
		assert!(List::items(&storage).is_empty());
	}
}
