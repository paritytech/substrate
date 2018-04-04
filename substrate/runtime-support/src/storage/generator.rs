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
//! extern crate substrate_runtime_support;
//!
//! type AuthorityId = [u8; 32];
//! type Balance = u64;
//! pub type SessionKey = [u8; 32];
//!
//! storage_items! {
//!     // public value
//!     pub Value: b"putd_key" => SessionKey;
//!     // private map.
//!     Balances: b"private_map:" => map [AuthorityId => Balance];
//!     // private list.
//!     Authorities: b"auth:" => list [AuthorityId];
//! }
//!
//!# fn main() { }
//! ```

use codec;
use rstd::vec::Vec;
#[doc(hidden)]
pub use rstd::borrow::Borrow;
#[doc(hidden)]
pub use rstd::marker::PhantomData;

/// Abstraction around storage.
pub trait Storage {
	/// true if the key exists in storage.
	fn exists(&self, key: &[u8]) -> bool;

	/// Load the bytes of a key from storage. Can panic if the type is incorrect.
	fn get<T: codec::Slicable>(&self, key: &[u8]) -> Option<T>;

	/// Load the bytes of a key from storage. Can panic if the type is incorrect. Will panic if
	/// it's not there.
	fn require<T: codec::Slicable>(&self, key: &[u8]) -> T { self.get(key).expect("Required values must be in storage") }

	/// Load the bytes of a key from storage. Can panic if the type is incorrect. The type's
	/// default is returned if it's not there.
	fn get_or_default<T: codec::Slicable + Default>(&self, key: &[u8]) -> T { self.get(key).unwrap_or_default() }

	/// Put a value in under a key.
	fn put<T: codec::Slicable>(&self, key: &[u8], val: &T);

	/// Remove the bytes of a key from storage.
	fn kill(&self, key: &[u8]);

	/// Take a value from storage, deleting it after reading.
	fn take<T: codec::Slicable>(&self, key: &[u8]) -> Option<T> {
		let value = self.get(key);
		self.kill(key);
		value
	}

	/// Take a value from storage, deleting it after reading.
	fn take_or_panic<T: codec::Slicable>(&self, key: &[u8]) -> T { self.take(key).expect("Required values must be in storage") }

	/// Take a value from storage, deleting it after reading.
	fn take_or_default<T: codec::Slicable + Default>(&self, key: &[u8]) -> T { self.take(key).unwrap_or_default() }
}

/// A strongly-typed value kept in storage.
pub trait StorageValue<T: codec::Slicable> {
	/// The type that get/take returns.
	type Query;

	/// Get the storage key.
	fn key() -> &'static [u8];

	/// true if the value is defined in storage.
	fn exists<S: Storage>(storage: &S) -> bool {
		storage.exists(Self::key())
	}

	/// Load the value from the provided storage instance.
	fn get<S: Storage>(storage: &S) -> Self::Query;

	/// Take a value from storage, removing it afterwards.
	fn take<S: Storage>(storage: &S) -> Self::Query;

	/// Store a value under this key into the provded storage instance.
	fn put<S: Storage>(val: &T, storage: &S) {
		storage.put(Self::key(), val)
	}

	/// Clear the storage value.
	fn kill<S: Storage>(storage: &S) {
		storage.kill(Self::key())
	}
}

/// A strongly-typed list in storage.
pub trait StorageList<T: codec::Slicable> {
	/// Get the prefix key in storage.
	fn prefix() -> &'static [u8];

	/// Get the key used to put the length field.
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
	/// The type that get/take returns.
	type Query;

	/// Get the prefix key in storage.
	fn prefix() -> &'static [u8];

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn key_for(x: &K) -> Vec<u8>;

	/// true if the value is defined in storage.
	fn exists<S: Storage>(key: &K, storage: &S) -> bool {
		storage.exists(&Self::key_for(key)[..])
	}

	/// Load the value associated with the given key from the map.
	fn get<S: Storage>(key: &K, storage: &S) -> Self::Query;

	/// Take the value under a key.
	fn take<S: Storage>(key: &K, storage: &S) -> Self::Query;

	/// Store a value to be associated with the given key from the map.
	fn insert<S: Storage>(key: &K, val: &V, storage: &S) {
		storage.put(&Self::key_for(key)[..], val);
	}

	/// Remove the value under a key.
	fn remove<S: Storage>(key: &K, storage: &S) {
		storage.kill(&Self::key_for(key)[..]);
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __storage_items_internal {
	// generator for values.
	(($($vis:tt)*) ($get_fn:ident) ($gettype:ty) ($getter:ident) ($taker:ident) $name:ident : $key:expr => $ty:ty) => {
		__storage_items_internal!{ ($($vis)*) () ($gettype) ($getter) ($taker) $name : $key => $ty }
		pub fn $get_fn() -> $gettype { <$name as $crate::storage::generator::StorageValue<$ty>> :: get(&$crate::storage::RuntimeStorage) }
	};
	(($($vis:tt)*) () ($gettype:ty) ($getter:ident) ($taker:ident) $name:ident : $key:expr => $ty:ty) => {
		$($vis)* struct $name;

		impl $crate::storage::generator::StorageValue<$ty> for $name {
			type Query = $gettype;

			/// Get the storage key.
			fn key() -> &'static [u8] {
				$key
			}

			/// Load the value from the provided storage instance.
			fn get<S: $crate::GenericStorage>(storage: &S) -> Self::Query {
				storage.$getter($key)
			}

			/// Take a value from storage, removing it afterwards.
			fn take<S: $crate::GenericStorage>(storage: &S) -> Self::Query {
				storage.$taker($key)
			}
		}
	};
	// generator for maps.
	(($($vis:tt)*) ($get_fn:ident) ($gettype:ty) ($getter:ident) ($taker:ident) $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]) => {
		__storage_items_internal!{ ($($vis)*) () ($gettype) ($getter) ($taker) $name : $prefix => map [$kty => $ty] }
		pub fn $get_fn<K: $crate::storage::generator::Borrow<$kty>>(key: K) -> $gettype {
			<$name as $crate::storage::generator::StorageMap<$kty, $ty>> :: get(key.borrow(), &$crate::storage::RuntimeStorage)
		}
	};
	(($($vis:tt)*) () ($gettype:ty) ($getter:ident) ($taker:ident) $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]) => {
		$($vis)* struct $name;

		impl $crate::storage::generator::StorageMap<$kty, $ty> for $name {
			type Query = $gettype;

			/// Get the prefix key in storage.
			fn prefix() -> &'static [u8] {
				$prefix
			}

			/// Get the storage key used to fetch a value corresponding to a specific key.
			fn key_for(x: &$kty) -> Vec<u8> {
				let mut key = $prefix.to_vec();
				key.extend($crate::codec::Slicable::encode(x));
				key
			}

			/// Load the value associated with the given key from the map.
			fn get<S: $crate::GenericStorage>(key: &$kty, storage: &S) -> Self::Query {
				let key = <$name as $crate::storage::generator::StorageMap<$kty, $ty>>::key_for(key);
				storage.$getter(&key[..])
			}

			/// Take the value, reading and removing it.
			fn take<S: $crate::GenericStorage>(key: &$kty, storage: &S) -> Self::Query {
				let key = <$name as $crate::storage::generator::StorageMap<$kty, $ty>>::key_for(key);
				storage.$taker(&key[..])
			}
		}
	};
	// generator for lists.
	(($($vis:tt)*) $name:ident : $prefix:expr => list [$ty:ty]) => {
		$($vis)* struct $name;

		impl $name {
			fn clear_item<S: $crate::GenericStorage>(index: u32, storage: &S) {
				if index < <$name as $crate::storage::generator::StorageList<$ty>>::len(storage) {
					storage.kill(&<$name as $crate::storage::generator::StorageList<$ty>>::key_for(index));
				}
			}

			fn set_len<S: $crate::GenericStorage>(count: u32, storage: &S) {
				(count..<$name as $crate::storage::generator::StorageList<$ty>>::len(storage)).for_each(|i| $name::clear_item(i, storage));
				storage.put(&<$name as $crate::storage::generator::StorageList<$ty>>::len_key(), &count);
			}
		}

		impl $crate::storage::generator::StorageList<$ty> for $name {
			/// Get the prefix key in storage.
			fn prefix() -> &'static [u8] {
				$prefix
			}

			/// Get the key used to put the length field.
			// TODO: concat macro should accept byte literals.
			fn len_key() -> Vec<u8> {
				let mut key = $prefix.to_vec();
				key.extend(b"len");
				key
			}

			/// Get the storage key used to fetch a value at a given index.
			fn key_for(index: u32) -> Vec<u8> {
				let mut key = $prefix.to_vec();
				key.extend($crate::codec::Slicable::encode(&index));
				key
			}

			/// Read out all the items.
			fn items<S: $crate::GenericStorage>(storage: &S) -> Vec<$ty> {
				(0..<$name as $crate::storage::generator::StorageList<$ty>>::len(storage))
					.map(|i| <$name as $crate::storage::generator::StorageList<$ty>>::get(i, storage).expect("all items within length are set; qed"))
					.collect()
			}

			/// Set the current set of items.
			fn set_items<S: $crate::GenericStorage>(items: &[$ty], storage: &S) {
				$name::set_len(items.len() as u32, storage);
				items.iter()
					.enumerate()
					.for_each(|(i, item)| <$name as $crate::storage::generator::StorageList<$ty>>::set_item(i as u32, item, storage));
			}

			fn set_item<S: $crate::GenericStorage>(index: u32, item: &$ty, storage: &S) {
				if index < <$name as $crate::storage::generator::StorageList<$ty>>::len(storage) {
					storage.put(&<$name as $crate::storage::generator::StorageList<$ty>>::key_for(index)[..], item);
				}
			}

			/// Load the value at given index. Returns `None` if the index is out-of-bounds.
			fn get<S: $crate::GenericStorage>(index: u32, storage: &S) -> Option<$ty> {
				storage.get(&<$name as $crate::storage::generator::StorageList<$ty>>::key_for(index)[..])
			}

			/// Load the length of the list.
			fn len<S: $crate::GenericStorage>(storage: &S) -> u32 {
				storage.get(&<$name as $crate::storage::generator::StorageList<$ty>>::len_key()).unwrap_or_default()
			}

			/// Clear the list.
			fn clear<S: $crate::GenericStorage>(storage: &S) {
				for i in 0..<$name as $crate::storage::generator::StorageList<$ty>>::len(storage) {
					$name::clear_item(i, storage);
				}

				storage.kill(&<$name as $crate::storage::generator::StorageList<$ty>>::len_key()[..])
			}
		}
	};
}

/// Declares strongly-typed wrappers around codec-compatible types in storage.
#[macro_export]
macro_rules! storage_items {
	// simple values
	($name:ident : $key:expr => $ty:ty; $($t:tt)*) => {
		__storage_items_internal!(() () (Option<$ty>) (get) (take) $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name:ident : $key:expr => $ty:ty; $($t:tt)*) => {
		__storage_items_internal!((pub) () (Option<$ty>) (get) (take) $name: $key => $ty);
		storage_items!($($t)*);
	};
	($name:ident : $key:expr => default $ty:ty; $($t:tt)*) => {
		__storage_items_internal!(() () ($ty) (get_or_default) (take_or_default) $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name:ident : $key:expr => default $ty:ty; $($t:tt)*) => {
		__storage_items_internal!((pub) () ($ty) (get_or_default) (take_or_default) $name: $key => $ty);
		storage_items!($($t)*);
	};
	($name:ident : $key:expr => required $ty:ty; $($t:tt)*) => {
		__storage_items_internal!(() () ($ty) (require) (take_or_panic) $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name:ident : $key:expr => required $ty:ty; $($t:tt)*) => {
		__storage_items_internal!((pub) () ($ty) (require) (take_or_panic) $name: $key => $ty);
		storage_items!($($t)*);
	};

	($name:ident get($getfn:ident) : $key:expr => $ty:ty; $($t:tt)*) => {
		__storage_items_internal!(() ($getfn) (Option<$ty>) (get) (take) $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $key:expr => $ty:ty; $($t:tt)*) => {
		__storage_items_internal!((pub) ($getfn) (Option<$ty>) (get) (take) $name: $key => $ty);
		storage_items!($($t)*);
	};
	($name:ident get($getfn:ident) : $key:expr => default $ty:ty; $($t:tt)*) => {
		__storage_items_internal!(() ($getfn) ($ty) (get_or_default) (take_or_default) $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $key:expr => default $ty:ty; $($t:tt)*) => {
		__storage_items_internal!((pub) ($getfn) ($ty) (get_or_default) (take_or_default) $name: $key => $ty);
		storage_items!($($t)*);
	};
	($name:ident get($getfn:ident) : $key:expr => required $ty:ty; $($t:tt)*) => {
		__storage_items_internal!(() ($getfn) ($ty) (require) (take_or_panic) $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $key:expr => required $ty:ty; $($t:tt)*) => {
		__storage_items_internal!((pub) ($getfn) ($ty) (require) (take_or_panic) $name: $key => $ty);
		storage_items!($($t)*);
	};

	// maps
	($name:ident : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!(() () (Option<$ty>) (get) (take) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!((pub) () (Option<$ty>) (get) (take) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	($name:ident : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!(() () ($ty) (get_or_default) (take_or_default) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!((pub) () ($ty) (get_or_default) (take_or_default) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	($name:ident : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!(() () ($ty) (require) (take_or_panic) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!((pub) () ($ty) (require) (take_or_panic) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};

	($name:ident get($getfn:ident) : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!(() ($getfn) (Option<$ty>) (get) (take) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!((pub) ($getfn) (Option<$ty>) (get) (take) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	($name:ident get($getfn:ident) : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!(() ($getfn) ($ty) (get_or_default) (take_or_default) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!((pub) ($getfn) ($ty) (get_or_default) (take_or_default) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	($name:ident get($getfn:ident) : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!(() ($getfn) ($ty) (require) (take_or_panic) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__storage_items_internal!((pub) ($getfn) ($ty) (require) (take_or_panic) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};


	// lists
	($name:ident : $prefix:expr => list [$ty:ty]; $($t:tt)*) => {
		__storage_items_internal!(() $name: $prefix => list [$ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident : $prefix:expr => list [$ty:ty]; $($t:tt)*) => {
		__storage_items_internal!((pub) $name: $prefix => list [$ty]);
		storage_items!($($t)*);
	};
	() => ()
}

#[macro_export]
#[doc(hidden)]
macro_rules! __decl_storage_item {
	// generator for values.
	(($($vis:tt)*) ($traittype:ident as $traitinstance:ident) ($get_fn:ident) ($gettype:ty) ($getter:ident) ($taker:ident) $name:ident : $key:expr => $ty:ty) => {
		__decl_storage_item!{ ($($vis)*) ($traittype as $traitinstance) () ($gettype) ($getter) ($taker) $name : $key => $ty }
	};
	(($($vis:tt)*) ($traittype:ident as $traitinstance:ident) () ($gettype:ty) ($getter:ident) ($taker:ident) $name:ident : $key:expr => $ty:ty) => {
		$($vis)* struct $name<$traitinstance: $traittype>($crate::storage::generator::PhantomData<$traitinstance>);

		impl<$traitinstance: $traittype> $crate::storage::generator::StorageValue<$ty> for $name<$traitinstance> {
			type Query = $gettype;

			/// Get the storage key.
			fn key() -> &'static [u8] {
				$key
			}

			/// Load the value from the provided storage instance.
			fn get<S: $crate::GenericStorage>(storage: &S) -> Self::Query {
				storage.$getter($key)
			}

			/// Take a value from storage, removing it afterwards.
			fn take<S: $crate::GenericStorage>(storage: &S) -> Self::Query {
				storage.$taker($key)
			}
		}
	};
	// generator for maps.
	(($($vis:tt)*) ($traittype:ident as $traitinstance:ident) ($get_fn:ident) ($gettype:ty) ($getter:ident) ($taker:ident) $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]) => {
		__decl_storage_item!{ ($($vis)*) ($traittype as $traitinstance) () ($gettype) ($getter) ($taker) $name : $prefix => map [$kty => $ty] }
	};
	(($($vis:tt)*) ($traittype:ident as $traitinstance:ident) () ($gettype:ty) ($getter:ident) ($taker:ident) $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]) => {
		$($vis)* struct $name<$traitinstance: $traittype>($crate::storage::generator::PhantomData<$traitinstance>);

		impl<$traitinstance: $traittype> $crate::storage::generator::StorageMap<$kty, $ty> for $name<$traitinstance> {
			type Query = $gettype;

			/// Get the prefix key in storage.
			fn prefix() -> &'static [u8] {
				$prefix
			}

			/// Get the storage key used to fetch a value corresponding to a specific key.
			fn key_for(x: &$kty) -> Vec<u8> {
				let mut key = $prefix.to_vec();
				key.extend($crate::codec::Slicable::encode(x));
				key
			}

			/// Load the value associated with the given key from the map.
			fn get<S: $crate::GenericStorage>(key: &$kty, storage: &S) -> Self::Query {
				let key = <$name<$traitinstance> as $crate::storage::generator::StorageMap<$kty, $ty>>::key_for(key);
				storage.$getter(&key[..])
			}

			/// Take the value, reading and removing it.
			fn take<S: $crate::GenericStorage>(key: &$kty, storage: &S) -> Self::Query {
				let key = <$name<$traitinstance> as $crate::storage::generator::StorageMap<$kty, $ty>>::key_for(key);
				storage.$taker(&key[..])
			}
		}
	};
}

// TODO: revisit this idiom once we get `type`s in `impl`s.
/*impl<T: Trait> Module<T> {
	type Now = super::Now<T>;
}*/

/// Declares strongly-typed wrappers around codec-compatible types in storage.
///
/// For now we implement a convenience trait with pre-specialised associated types, one for each
/// storage item. This allows you to gain access to publicly visisible storage items from a
/// module type. Currently you must disambiguate by using `<Module as Store>::Item` rather than
/// the simpler `Module::Item`. Hopefully the rust guys with fix this soon.
#[macro_export]
macro_rules! decl_storage {
	(
		trait $storetype:ident for $modulename:ident<$traitinstance:ident: $traittype:ident>;
		$($t:tt)*
	) => {
		__decl_storage_items!($traittype $traitinstance $($t)*);
		trait $storetype {
			__decl_store_items!($($t)*);
		}
		impl<$traitinstance: $traittype> $storetype for $modulename<$traitinstance> {
			__impl_store_items!($traitinstance $($t)*);
		}
		impl<$traitinstance: $traittype> $modulename<$traitinstance> {
			__impl_store_fns!($traitinstance $($t)*);
		}
	};
	(
		pub trait $storetype:ident for $modulename:ident<$traitinstance:ident: $traittype:ident>;
		$($t:tt)*
	) => {
		__decl_storage_items!($traittype $traitinstance $($t)*);
		pub trait $storetype {
			__decl_store_items!($($t)*);
		}
		impl<$traitinstance: $traittype> $storetype for $modulename<$traitinstance> {
			__impl_store_items!($traitinstance $($t)*);
		}
		impl<$traitinstance: $traittype> $modulename<$traitinstance> {
			__impl_store_fns!($traitinstance $($t)*);
		}
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __decl_store_item {
	($name:ident) => { type $name; }
}

#[macro_export]
#[doc(hidden)]
macro_rules! __decl_store_items {
	// simple values
	($name:ident : $key:expr => $ty:ty; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	(pub $name:ident : $key:expr => $ty:ty; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	($name:ident : $key:expr => default $ty:ty; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	(pub $name:ident : $key:expr => default $ty:ty; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	($name:ident : $key:expr => required $ty:ty; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	(pub $name:ident : $key:expr => required $ty:ty; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};

	($name:ident get($getfn:ident) : $key:expr => $ty:ty; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $key:expr => $ty:ty; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	($name:ident get($getfn:ident) : $key:expr => default $ty:ty; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $key:expr => default $ty:ty; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	($name:ident get($getfn:ident) : $key:expr => required $ty:ty; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $key:expr => required $ty:ty; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};

	// maps
	($name:ident : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	(pub $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	($name:ident : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	(pub $name:ident : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	($name:ident : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	(pub $name:ident : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};

	($name:ident get($getfn:ident) : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	($name:ident get($getfn:ident) : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	($name:ident get($getfn:ident) : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_store_item!($name); __decl_store_items!($($t)*);
	};

	// exit
	() => ()
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_store_fn {
	($traitinstance:ident $name:ident $get_fn:ident ($gettype:ty) $key:expr => $ty:ty) => {
		pub fn $get_fn() -> $gettype {
			<$name<$traitinstance> as $crate::storage::generator::StorageValue<$ty>> :: get(&$crate::storage::RuntimeStorage)
		}
	};
	($traitinstance:ident $name:ident $get_fn:ident ($gettype:ty) $prefix:expr => map [$kty:ty => $ty:ty]) => {
		pub fn $get_fn<K: $crate::storage::generator::Borrow<$kty>>(key: K) -> $gettype {
			<$name<$traitinstance> as $crate::storage::generator::StorageMap<$kty, $ty>> :: get(key.borrow(), &$crate::storage::RuntimeStorage)
		}
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_store_fns {
	// simple values
	($traitinstance:ident $name:ident : $key:expr => $ty:ty; $($t:tt)*) => {
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident : $key:expr => $ty:ty; $($t:tt)*) => {
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident : $key:expr => default $ty:ty; $($t:tt)*) => {
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident : $key:expr => default $ty:ty; $($t:tt)*) => {
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident : $key:expr => required $ty:ty; $($t:tt)*) => {
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident : $key:expr => required $ty:ty; $($t:tt)*) => {
		__impl_store_fns!($traitinstance $($t)*);
	};

	($traitinstance:ident $name:ident get($getfn:ident) : $key:expr => $ty:ty; $($t:tt)*) => {
		__impl_store_fn!($traitinstance $name $getfn (Option<$ty>) $gettype $key => $ty);
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident get($getfn:ident) : $key:expr => $ty:ty; $($t:tt)*) => {
		__impl_store_fn!($traitinstance $name $getfn (Option<$ty>) $key => $ty);
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident get($getfn:ident) : $key:expr => default $ty:ty; $($t:tt)*) => {
		__impl_store_fn!($traitinstance $name $getfn ($ty) $key => $ty);
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident get($getfn:ident) : $key:expr => default $ty:ty; $($t:tt)*) => {
		__impl_store_fn!($traitinstance $name $getfn ($ty) $key => $ty);
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident get($getfn:ident) : $key:expr => required $ty:ty; $($t:tt)*) => {
		__impl_store_fn!($traitinstance $name $getfn ($ty) $key => $ty);
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident get($getfn:ident) : $key:expr => required $ty:ty; $($t:tt)*) => {
		__impl_store_fn!($traitinstance $name $getfn ($ty) $key => $ty);
		__impl_store_fns!($traitinstance $($t)*);
	};

	// maps
	($traitinstance:ident $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_fns!($traitinstance $($t)*);
	};

	($traitinstance:ident $name:ident get($getfn:ident) : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_fn!($traitinstance $name $getfn (Option<$ty>) $prefix:expr => map [$kty => $ty]);
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident get($getfn:ident) : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_fn!($traitinstance $name $getfn (Option<$ty>) $prefix:expr => map [$kty => $ty]);
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident get($getfn:ident) : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_fn!($traitinstance $name $getfn ($ty) $prefix:expr => map [$kty => $ty]);
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident get($getfn:ident) : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_fn!($traitinstance $name $getfn ($ty) $prefix:expr => map [$kty => $ty]);
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident get($getfn:ident) : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_fn!($traitinstance $name $getfn ($ty) $prefix:expr => map [$kty => $ty]);
		__impl_store_fns!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident get($getfn:ident) : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_fn!($traitinstance $name $getfn ($ty) $prefix:expr => map [$kty => $ty]);
		__impl_store_fns!($traitinstance $($t)*);
	};

	// exit
	($traitinstance:ident) => ()
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_store_item {
	($name:ident $traitinstance:ident) => { type $name = $name<$traitinstance>; }
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_store_items {
	// simple values
	($traitinstance:ident $name:ident : $key:expr => $ty:ty; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident : $key:expr => $ty:ty; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident : $key:expr => default $ty:ty; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident : $key:expr => default $ty:ty; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident : $key:expr => required $ty:ty; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident : $key:expr => required $ty:ty; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};

	($traitinstance:ident $name:ident get($getfn:ident) : $key:expr => $ty:ty; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident get($getfn:ident) : $key:expr => $ty:ty; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident get($getfn:ident) : $key:expr => default $ty:ty; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident get($getfn:ident) : $key:expr => default $ty:ty; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident get($getfn:ident) : $key:expr => required $ty:ty; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident get($getfn:ident) : $key:expr => required $ty:ty; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};

	// maps
	($traitinstance:ident $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};

	($traitinstance:ident $name:ident get($getfn:ident) : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident get($getfn:ident) : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident get($getfn:ident) : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident get($getfn:ident) : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident $name:ident get($getfn:ident) : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};
	($traitinstance:ident pub $name:ident get($getfn:ident) : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__impl_store_item!($name $traitinstance);
		__impl_store_items!($traitinstance $($t)*);
	};

	// exit
	($traitinstance:ident) => ()
}

#[macro_export]
#[doc(hidden)]
macro_rules! __decl_storage_items {
	// simple values
	($traittype:ident $traitinstance:ident $name:ident : $key:expr => $ty:ty; $($t:tt)*) => {
		__decl_storage_item!(() ($traittype as $traitinstance) () (Option<$ty>) (get) (take) $name: $key => $ty);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident pub $name:ident : $key:expr => $ty:ty; $($t:tt)*) => {
		__decl_storage_item!((pub) ($traittype as $traitinstance) () (Option<$ty>) (get) (take) $name: $key => $ty);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident $name:ident : $key:expr => default $ty:ty; $($t:tt)*) => {
		__decl_storage_item!(() ($traittype as $traitinstance) () ($ty) (get_or_default) (take_or_default) $name: $key => $ty);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident pub $name:ident : $key:expr => default $ty:ty; $($t:tt)*) => {
		__decl_storage_item!((pub) ($traittype as $traitinstance) () ($ty) (get_or_default) (take_or_default) $name: $key => $ty);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident $name:ident : $key:expr => required $ty:ty; $($t:tt)*) => {
		__decl_storage_item!(() ($traittype as $traitinstance) () ($ty) (require) (take_or_panic) $name: $key => $ty);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident pub $name:ident : $key:expr => required $ty:ty; $($t:tt)*) => {
		__decl_storage_item!((pub) ($traittype as $traitinstance) () ($ty) (require) (take_or_panic) $name: $key => $ty);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};

	($traittype:ident $traitinstance:ident $name:ident get($getfn:ident) : $key:expr => $ty:ty; $($t:tt)*) => {
		__decl_storage_item!(() ($traittype as $traitinstance) ($getfn) (Option<$ty>) (get) (take) $name: $key => $ty);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident pub $name:ident get($getfn:ident) : $key:expr => $ty:ty; $($t:tt)*) => {
		__decl_storage_item!((pub) ($traittype as $traitinstance) ($getfn) (Option<$ty>) (get) (take) $name: $key => $ty);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident $name:ident get($getfn:ident) : $key:expr => default $ty:ty; $($t:tt)*) => {
		__decl_storage_item!(() ($traittype as $traitinstance) ($getfn) ($ty) (get_or_default) (take_or_default) $name: $key => $ty);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident pub $name:ident get($getfn:ident) : $key:expr => default $ty:ty; $($t:tt)*) => {
		__decl_storage_item!((pub) ($traittype as $traitinstance) ($getfn) ($ty) (get_or_default) (take_or_default) $name: $key => $ty);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident $name:ident get($getfn:ident) : $key:expr => required $ty:ty; $($t:tt)*) => {
		__decl_storage_item!(() ($traittype as $traitinstance) ($getfn) ($ty) (require) (take_or_panic) $name: $key => $ty);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident pub $name:ident get($getfn:ident) : $key:expr => required $ty:ty; $($t:tt)*) => {
		__decl_storage_item!((pub) ($traittype as $traitinstance) ($getfn) ($ty) (require) (take_or_panic) $name: $key => $ty);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};

	// maps
	($traittype:ident $traitinstance:ident $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_storage_item!(() ($traittype as $traitinstance) () (Option<$ty>) (get) (take) $name: $prefix => map [$kty => $ty]);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident pub $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_storage_item!((pub) ($traittype as $traitinstance) () (Option<$ty>) (get) (take) $name: $prefix => map [$kty => $ty]);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident $name:ident : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_storage_item!(() ($traittype as $traitinstance) () ($ty) (get_or_default) (take_or_default) $name: $prefix => map [$kty => $ty]);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident pub $name:ident : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_storage_item!((pub) ($traittype as $traitinstance) () ($ty) (get_or_default) (take_or_default) $name: $prefix => map [$kty => $ty]);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident $name:ident : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_storage_item!(() ($traittype as $traitinstance) () ($ty) (require) (take_or_panic) $name: $prefix => map [$kty => $ty]);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident pub $name:ident : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_storage_item!((pub) ($traittype as $traitinstance) () ($ty) (require) (take_or_panic) $name: $prefix => map [$kty => $ty]);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};

	($traittype:ident $traitinstance:ident $name:ident get($getfn:ident) : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_storage_item!(() ($traittype as $traitinstance) ($getfn) (Option<$ty>) (get) (take) $name: $prefix => map [$kty => $ty]);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident pub $name:ident get($getfn:ident) : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_storage_item!((pub) ($traittype as $traitinstance) ($getfn) (Option<$ty>) (get) (take) $name: $prefix => map [$kty => $ty]);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident $name:ident get($getfn:ident) : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_storage_item!(() ($traittype as $traitinstance) ($getfn) ($ty) (get_or_default) (take_or_default) $name: $prefix => map [$kty => $ty]);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident pub $name:ident get($getfn:ident) : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_storage_item!((pub) ($traittype as $traitinstance) ($getfn) ($ty) (get_or_default) (take_or_default) $name: $prefix => map [$kty => $ty]);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident $name:ident get($getfn:ident) : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_storage_item!(() ($traittype as $traitinstance) ($getfn) ($ty) (require) (take_or_panic) $name: $prefix => map [$kty => $ty]);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};
	($traittype:ident $traitinstance:ident pub $name:ident get($getfn:ident) : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		__decl_storage_item!((pub) ($traittype as $traitinstance) ($getfn) ($ty) (require) (take_or_panic) $name: $prefix => map [$kty => $ty]);
		__decl_storage_items!($traittype $traitinstance $($t)*);
	};

	// exit
	($traittype:ident $traitinstance:ident) => ()
}

#[cfg(test)]
mod tests {
	use std::collections::HashMap;
	use std::cell::RefCell;
	use codec::Slicable;
	use super::*;

	impl Storage for RefCell<HashMap<Vec<u8>, Vec<u8>>> {
		fn exists(&self, key: &[u8]) -> bool {
			self.borrow_mut().get(key).is_some()
		}

		fn get<T: Slicable>(&self, key: &[u8]) -> Option<T> {
			self.borrow_mut().get(key).map(|v| T::decode(&mut &v[..]).unwrap())
		}

		fn put<T: Slicable>(&self, key: &[u8], val: &T) {
			self.borrow_mut().insert(key.to_owned(), val.encode());
		}

		fn kill(&self, key: &[u8]) {
			self.borrow_mut().remove(key);
		}
	}

	storage_items! {
		Value: b"a" => u32;
		List: b"b:" => list [u64];
		Map: b"c:" => map [u32 => [u8; 32]];
	}

	#[test]
	fn value() {
		let storage = RefCell::new(HashMap::new());
		assert!(Value::get(&storage).is_none());
		Value::put(&100_000, &storage);
		assert_eq!(Value::get(&storage), Some(100_000));
		Value::kill(&storage);
		assert!(Value::get(&storage).is_none());
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

	#[test]
	fn map() {
		let storage = RefCell::new(HashMap::new());
		assert!(Map::get(&5, &storage).is_none());
		Map::insert(&5, &[1; 32], &storage);
		assert_eq!(Map::get(&5, &storage), Some([1; 32]));
		assert_eq!(Map::take(&5, &storage), Some([1; 32]));
		assert!(Map::get(&5, &storage).is_none());
		assert!(Map::get(&999, &storage).is_none());
	}
}
