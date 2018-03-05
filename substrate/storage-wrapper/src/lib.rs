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
}

#[macro_export]
#[doc(hidden)]
macro_rules! __storage_items_internal {
	// generator for values.
	(($($vis:tt)*) $name: ident: $key: expr => $ty:ty) => {
		$($vis)* struct $name;

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
		}
	};
	// generator for maps.
	(($($vis:tt)*) $name: ident: $prefix: expr => map [$kty: ty => $ty:ty]) => {
		$($vis)* struct $name;

		impl $name {
			/// Get the prefix key in storage.
			$($vis)* fn prefix() -> &'static [u8] {
				$prefix
			}

			/// Get the storage key used to fetch a value corresponding to a specific key.
			$($vis)* fn key_for(x: &$kty) -> Vec<u8> {
				let mut key = $prefix.to_vec();
				key.extend($crate::codec::Slicable::encode(&index));
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
	};
	// generator for lists.
	(($($vis:tt)*) $name: ident: $prefix: expr => list [$ty:ty]) => {
		$($vis)* struct $name;

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

			$($vis)* fn clear_item<S: $crate::Storage>(index: u32, storage: &S) {
				if index < $name::len(storage) {
					storage.kill(&$name::key_for(index));
				}
			}

			/// Load the value at given index. Returns `None` if `len
			$($vis)* fn get<S: $crate::Storage>(index: u32, storage: &S) -> Option<$ty> {
				storage.load(&$name::key_for(index)[..])
			}

			$($vis)* fn len<S: $crate::Storage>(storage: &S) -> u32 {
				storage.load(&$name::len_key()).unwrap_or_default()
			}

			fn set_len<S: $crate::Storage>(count: u32, storage: &S) {
				(count..$name::len(storage)).for_each(|i| $name::clear_item(i, storage));
				storage.store(&$name::len_key(), &count);
			}
		}
	};
}

/// Declares wrappers around stored data.
///
/// storage_items! {
///     Authorities: ":auth:" => list [AuthorityId]; // list
///     Balances: ":bal:" => map [AccountId => Balance]; // map
///     Code: ":code" => Vec<u8>; // creates a single value. stored under that key.
///     ...
/// }
///
/// Authorities::len_key() -> &'static [u8];
/// Authorities::load_len(&Storage) -> u32
/// Authorities::key_for(n) -> Vec<u8>;
/// Authorities::load_from(&Storage, n) -> Option<AuthorityId>;
/// // ... KeyedVec-like API
///
/// Code::load_from(&Storage) -> Option<Vec<u8>>; // assumes a `Decodable` trait where the `<[u8] as Decodable>::Decoded = Vec<u8>`
/// Code::store_in(&mut Storage, &[u8]);
/// Code::key() -> &'static [u8]; // for low-level usage.
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
	use super::*;

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
