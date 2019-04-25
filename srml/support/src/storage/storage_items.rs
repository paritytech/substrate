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
//! extern crate srml_support;
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

#[doc(hidden)]
pub use crate::rstd::borrow::Borrow;
#[doc(hidden)]
pub use crate::rstd::marker::PhantomData;
#[doc(hidden)]
pub use crate::rstd::boxed::Box;

// FIXME #1466 Remove this in favor of `decl_storage` macro.
/// Declares strongly-typed wrappers around codec-compatible types in storage.
#[macro_export]
macro_rules! storage_items {
	// simple values
	($name:ident : $key:expr => $ty:ty; $($t:tt)*) => {
		$crate::__storage_items_internal!(() () (OPTION_TYPE Option<$ty>) (get) (take) $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name:ident : $key:expr => $ty:ty; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) () (OPTION_TYPE Option<$ty>) (get) (take) $name: $key => $ty);
		storage_items!($($t)*);
	};
	($name:ident : $key:expr => default $ty:ty; $($t:tt)*) => {
		$crate::__storage_items_internal!(() () (RAW_TYPE $ty) (get_or_default) (take_or_default) $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name:ident : $key:expr => default $ty:ty; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) () (RAW_TYPE $ty) (get_or_default) (take_or_default) $name: $key => $ty);
		storage_items!($($t)*);
	};
	($name:ident : $key:expr => required $ty:ty; $($t:tt)*) => {
		$crate::__storage_items_internal!(() () (RAW_TYPE $ty) (require) (take_or_panic) $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name:ident : $key:expr => required $ty:ty; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) () (RAW_TYPE $ty) (require) (take_or_panic) $name: $key => $ty);
		storage_items!($($t)*);
	};

	($name:ident get($getfn:ident) : $key:expr => $ty:ty; $($t:tt)*) => {
		$crate::__storage_items_internal!(() ($getfn) (OPTION_TYPE Option<$ty>) (get) (take) $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $key:expr => $ty:ty; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) ($getfn) (OPTION_TYPE Option<$ty>) (get) (take) $name: $key => $ty);
		storage_items!($($t)*);
	};
	($name:ident get($getfn:ident) : $key:expr => default $ty:ty; $($t:tt)*) => {
		$crate::__storage_items_internal!(() ($getfn) (RAW_TYPE $ty) (get_or_default) (take_or_default) $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $key:expr => default $ty:ty; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) ($getfn) (RAW_TYPE $ty) (get_or_default) (take_or_default) $name: $key => $ty);
		storage_items!($($t)*);
	};
	($name:ident get($getfn:ident) : $key:expr => required $ty:ty; $($t:tt)*) => {
		$crate::__storage_items_internal!(() ($getfn) (RAW_TYPE $ty) (require) (take_or_panic) $name: $key => $ty);
		storage_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $key:expr => required $ty:ty; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) ($getfn) (RAW_TYPE $ty) (require) (take_or_panic) $name: $key => $ty);
		storage_items!($($t)*);
	};

	// maps
	($name:ident : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!(() () (OPTION_TYPE Option<$ty>) (get) (take) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) () (OPTION_TYPE Option<$ty>) (get) (take) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	($name:ident : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!(() () (RAW_TYPE $ty) (get_or_default) (take_or_default) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) () (RAW_TYPE $ty) (get_or_default) (take_or_default) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	($name:ident : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!(() () (RAW_TYPE $ty) (require) (take_or_panic) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) () (RAW_TYPE $ty) (require) (take_or_panic) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};

	($name:ident get($getfn:ident) : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!(() ($getfn) (OPTION_TYPE Option<$ty>) (get) (take) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $prefix:expr => map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) ($getfn) (OPTION_TYPE Option<$ty>) (get) (take) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	($name:ident get($getfn:ident) : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!(() ($getfn) (RAW_TYPE $ty) (get_or_default) (take_or_default) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $prefix:expr => default map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) ($getfn) (RAW_TYPE $ty) (get_or_default) (take_or_default) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	($name:ident get($getfn:ident) : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!(() ($getfn) (RAW_TYPE $ty) (require) (take_or_panic) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident get($getfn:ident) : $prefix:expr => required map [$kty:ty => $ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) ($getfn) (RAW_TYPE $ty) (require) (take_or_panic) $name: $prefix => map [$kty => $ty]);
		storage_items!($($t)*);
	};


	// lists
	($name:ident : $prefix:expr => list [$ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!(() $name: $prefix => list [$ty]);
		storage_items!($($t)*);
	};
	(pub $name:ident : $prefix:expr => list [$ty:ty]; $($t:tt)*) => {
		$crate::__storage_items_internal!((pub) $name: $prefix => list [$ty]);
		storage_items!($($t)*);
	};
	() => ()
}

#[macro_export]
#[doc(hidden)]
macro_rules! __storage_items_internal {
	// generator for values.
	(($($vis:tt)*) ($get_fn:ident) ($wraptype:ident $gettype:ty) ($getter:ident) ($taker:ident) $name:ident : $key:expr => $ty:ty) => {
		$crate::__storage_items_internal!{ ($($vis)*) () ($wraptype $gettype) ($getter) ($taker) $name : $key => $ty }
		pub fn $get_fn() -> $gettype { <$name as $crate::storage::hashed::generator::StorageValue<$ty>> :: get(&$crate::storage::RuntimeStorage) }
	};
	(($($vis:tt)*) () ($wraptype:ident $gettype:ty) ($getter:ident) ($taker:ident) $name:ident : $key:expr => $ty:ty) => {
		$($vis)* struct $name;

		impl $crate::storage::hashed::generator::StorageValue<$ty> for $name {
			type Query = $gettype;

			/// Get the storage key.
			fn key() -> &'static [u8] {
				$key
			}

			/// Load the value from the provided storage instance.
			fn get<S: $crate::HashedStorage<$crate::Twox128>>(storage: &S) -> Self::Query {
				storage.$getter($key)
			}

			/// Take a value from storage, removing it afterwards.
			fn take<S: $crate::HashedStorage<$crate::Twox128>>(storage: &S) -> Self::Query {
				storage.$taker($key)
			}

			/// Mutate this value.
			fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: $crate::HashedStorage<$crate::Twox128>>(f: F, storage: &S) -> R {
				let mut val = <Self as $crate::storage::hashed::generator::StorageValue<$ty>>::get(storage);

				let ret = f(&mut val);

				$crate::__handle_wrap_internal!($wraptype {
					// raw type case
					<Self as $crate::storage::hashed::generator::StorageValue<$ty>>::put(&val, storage)
				} {
					// Option<> type case
					match val {
						Some(ref val) => <Self as $crate::storage::hashed::generator::StorageValue<$ty>>::put(&val, storage),
						None => <Self as $crate::storage::hashed::generator::StorageValue<$ty>>::kill(storage),
					}
				});

				ret
			}
		}
	};
	// generator for maps.
	(($($vis:tt)*) ($get_fn:ident) ($wraptype:ident $gettype:ty) ($getter:ident) ($taker:ident) $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]) => {
		$crate::__storage_items_internal!{ ($($vis)*) () ($wraptype $gettype) ($getter) ($taker) $name : $prefix => map [$kty => $ty] }
		pub fn $get_fn<K: $crate::storage::generator::Borrow<$kty>>(key: K) -> $gettype {
			<$name as $crate::storage::hashed::generator::StorageMap<$kty, $ty>> :: get(key.borrow(), &$crate::storage::RuntimeStorage)
		}
	};
	(($($vis:tt)*) () ($wraptype:ident $gettype:ty) ($getter:ident) ($taker:ident) $name:ident : $prefix:expr => map [$kty:ty => $ty:ty]) => {
		$($vis)* struct $name;

		impl $crate::storage::hashed::generator::StorageMap<$kty, $ty> for $name {
			type Query = $gettype;

			type Hasher = $crate::Blake2_256;

			/// Get the prefix key in storage.
			fn prefix() -> &'static [u8] {
				$prefix
			}

			/// Get the storage key used to fetch a value corresponding to a specific key.
			fn key_for(x: &$kty) -> $crate::rstd::vec::Vec<u8> {
				let mut key = $prefix.to_vec();
				$crate::codec::Encode::encode_to(x, &mut key);
				key
			}

			/// Load the value associated with the given key from the map.
			fn get<S: $crate::HashedStorage<Self::Hasher>>(key: &$kty, storage: &S) -> Self::Query {
				let key = <$name as $crate::storage::hashed::generator::StorageMap<$kty, $ty>>::key_for(key);
				storage.$getter(&key[..])
			}

			/// Take the value, reading and removing it.
			fn take<S: $crate::HashedStorage<Self::Hasher>>(key: &$kty, storage: &S) -> Self::Query {
				let key = <$name as $crate::storage::hashed::generator::StorageMap<$kty, $ty>>::key_for(key);
				storage.$taker(&key[..])
			}

			/// Mutate the value under a key.
			fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: $crate::HashedStorage<Self::Hasher>>(key: &$kty, f: F, storage: &S) -> R {
				let mut val = <Self as $crate::storage::hashed::generator::StorageMap<$kty, $ty>>::take(key, storage);

				let ret = f(&mut val);

				$crate::__handle_wrap_internal!($wraptype {
					// raw type case
					<Self as $crate::storage::hashed::generator::StorageMap<$kty, $ty>>::insert(key, &val, storage)
				} {
					// Option<> type case
					match val {
						Some(ref val) => <Self as $crate::storage::hashed::generator::StorageMap<$kty, $ty>>::insert(key, &val, storage),
						None => <Self as $crate::storage::hashed::generator::StorageMap<$kty, $ty>>::remove(key, storage),
					}
				});

				ret
			}
		}
	};
	// generator for lists.
	(($($vis:tt)*) $name:ident : $prefix:expr => list [$ty:ty]) => {
		$($vis)* struct $name;

		impl $name {
			fn clear_item<S: $crate::HashedStorage<$crate::Twox128>>(index: u32, storage: &S) {
				if index < <$name as $crate::storage::hashed::generator::StorageList<$ty>>::len(storage) {
					storage.kill(&<$name as $crate::storage::hashed::generator::StorageList<$ty>>::key_for(index));
				}
			}

			fn set_len<S: $crate::HashedStorage<$crate::Twox128>>(count: u32, storage: &S) {
				(count..<$name as $crate::storage::hashed::generator::StorageList<$ty>>::len(storage)).for_each(|i| $name::clear_item(i, storage));
				storage.put(&<$name as $crate::storage::hashed::generator::StorageList<$ty>>::len_key(), &count);
			}
		}

		impl $crate::storage::hashed::generator::StorageList<$ty> for $name {
			/// Get the prefix key in storage.
			fn prefix() -> &'static [u8] {
				$prefix
			}

			/// Get the key used to put the length field.
			fn len_key() -> $crate::rstd::vec::Vec<u8> {
				let mut key = $prefix.to_vec();
				key.extend(b"len");
				key
			}

			/// Get the storage key used to fetch a value at a given index.
			fn key_for(index: u32) -> $crate::rstd::vec::Vec<u8> {
				let mut key = $prefix.to_vec();
				$crate::codec::Encode::encode_to(&index, &mut key);
				key
			}

			/// Read out all the items.
			fn items<S: $crate::HashedStorage<$crate::Twox128>>(storage: &S) -> $crate::rstd::vec::Vec<$ty> {
				(0..<$name as $crate::storage::hashed::generator::StorageList<$ty>>::len(storage))
					.map(|i| <$name as $crate::storage::hashed::generator::StorageList<$ty>>::get(i, storage).expect("all items within length are set; qed"))
					.collect()
			}

			/// Set the current set of items.
			fn set_items<S: $crate::HashedStorage<$crate::Twox128>>(items: &[$ty], storage: &S) {
				$name::set_len(items.len() as u32, storage);
				items.iter()
					.enumerate()
					.for_each(|(i, item)| <$name as $crate::storage::hashed::generator::StorageList<$ty>>::set_item(i as u32, item, storage));
			}

			fn set_item<S: $crate::HashedStorage<$crate::Twox128>>(index: u32, item: &$ty, storage: &S) {
				if index < <$name as $crate::storage::hashed::generator::StorageList<$ty>>::len(storage) {
					storage.put(&<$name as $crate::storage::hashed::generator::StorageList<$ty>>::key_for(index)[..], item);
				}
			}

			/// Load the value at given index. Returns `None` if the index is out-of-bounds.
			fn get<S: $crate::HashedStorage<$crate::Twox128>>(index: u32, storage: &S) -> Option<$ty> {
				storage.get(&<$name as $crate::storage::hashed::generator::StorageList<$ty>>::key_for(index)[..])
			}

			/// Load the length of the list.
			fn len<S: $crate::HashedStorage<$crate::Twox128>>(storage: &S) -> u32 {
				storage.get(&<$name as $crate::storage::hashed::generator::StorageList<$ty>>::len_key()).unwrap_or_default()
			}

			/// Clear the list.
			fn clear<S: $crate::HashedStorage<$crate::Twox128>>(storage: &S) {
				for i in 0..<$name as $crate::storage::hashed::generator::StorageList<$ty>>::len(storage) {
					$name::clear_item(i, storage);
				}

				storage.kill(&<$name as $crate::storage::hashed::generator::StorageList<$ty>>::len_key()[..])
			}
		}
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __handle_wrap_internal {
	(RAW_TYPE { $($raw:tt)* } { $($option:tt)* }) => {
		$($raw)*;
	};
	(OPTION_TYPE { $($raw:tt)* } { $($option:tt)* }) => {
		$($option)*;
	};
}

// FIXME: revisit this idiom once we get `type`s in `impl`s.
/*impl<T: Trait> Module<T> {
	type Now = super::Now<T>;
}*/

#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
mod tests {
	use std::collections::HashMap;
	use std::cell::RefCell;
	use super::*;
	use crate::metadata::*;
	use crate::metadata::StorageHasher;
	use crate::rstd::marker::PhantomData;
	use crate::storage::hashed::generator::*;

	storage_items! {
		Value: b"a" => u32;
		List: b"b:" => list [u64];
		Map: b"c:" => map [u32 => [u8; 32]];
	}

	#[test]
	fn value() {
		let mut overlay = HashMap::new();
		let storage = RefCell::new(&mut overlay);
		assert!(Value::get(&storage).is_none());
		Value::put(&100_000, &storage);
		assert_eq!(Value::get(&storage), Some(100_000));
		Value::kill(&storage);
		assert!(Value::get(&storage).is_none());
	}

	#[test]
	fn list() {
		let mut overlay = HashMap::new();
		let storage = RefCell::new(&mut overlay);
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
		let mut overlay = HashMap::new();
		let storage = RefCell::new(&mut overlay);
		assert!(Map::get(&5, &storage).is_none());
		Map::insert(&5, &[1; 32], &storage);
		assert_eq!(Map::get(&5, &storage), Some([1; 32]));
		assert_eq!(Map::take(&5, &storage), Some([1; 32]));
		assert!(Map::get(&5, &storage).is_none());
		assert!(Map::get(&999, &storage).is_none());
	}

	pub trait Trait {
		type Origin: crate::codec::Encode + crate::codec::Decode + ::std::default::Default;
		type BlockNumber;
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
	}

	crate::decl_storage! {
		trait Store for Module<T: Trait> as TestStorage {
			// non-getters: pub / $default

			/// Hello, this is doc!
			U32 : Option<u32> = Some(3);
			pub PUBU32 : Option<u32>;
			U32MYDEF : Option<u32> = None;
			pub PUBU32MYDEF : Option<u32> = Some(3);

			// getters: pub / $default
			// we need at least one type which uses T, otherwise GenesisConfig will complain.
			GETU32 get(u32_getter): T::Origin;
			pub PUBGETU32 get(pub_u32_getter) build(|config: &GenesisConfig<T>| config.u32_getter_with_config): u32;
			GETU32WITHCONFIG get(u32_getter_with_config) config(): u32;
			pub PUBGETU32WITHCONFIG get(pub_u32_getter_with_config) config(): u32;
			GETU32MYDEF get(u32_getter_mydef): Option<u32> = Some(4);
			pub PUBGETU32MYDEF get(pub_u32_getter_mydef) config(): u32 = 3;
			GETU32WITHCONFIGMYDEF get(u32_getter_with_config_mydef) config(): u32 = 2;
			pub PUBGETU32WITHCONFIGMYDEF get(pub_u32_getter_with_config_mydef) config(): u32 = 1;
			PUBGETU32WITHCONFIGMYDEFOPT get(pub_u32_getter_with_config_mydef_opt) config(): Option<u32> = Some(100);

			// map non-getters: pub / $default
			MAPU32 : map u32 => Option<String>;
			pub PUBMAPU32 : map u32 => Option<String>;
			MAPU32MYDEF : map u32 => Option<String> = None;
			pub PUBMAPU32MYDEF : map u32 => Option<String> = Some("hello".into());

			// map getters: pub / $default
			GETMAPU32 get(map_u32_getter): map u32 => String;
			pub PUBGETMAPU32 get(pub_map_u32_getter): map u32 => String;

			GETMAPU32MYDEF get(map_u32_getter_mydef): map u32 => String = "map".into();
			pub PUBGETMAPU32MYDEF get(pub_map_u32_getter_mydef): map u32 => String = "pubmap".into();

			// linked map
			LINKEDMAPU32 : linked_map u32 => Option<String>;
			pub PUBLINKEDMAPU32MYDEF : linked_map u32 => Option<String> = Some("hello".into());
			GETLINKEDMAPU32 get(linked_map_u32_getter): linked_map u32 => String;
			pub PUBGETLINKEDMAPU32MYDEF get(pub_linked_map_u32_getter_mydef): linked_map u32 => String = "pubmap".into();

			COMPLEXTYPE1: ::std::vec::Vec<<T as Trait>::Origin>;
			COMPLEXTYPE2: (Vec<Vec<(u16,Box<(  )>)>>, u32);
			COMPLEXTYPE3: ([u32;25]);
		}
		add_extra_genesis {
			build(|_, _, _| {});
		}
	}

	struct TraitImpl {}

	impl Trait for TraitImpl {
		type Origin = u32;
		type BlockNumber = u32;
	}

	const EXPECTED_METADATA: StorageMetadata = StorageMetadata {
		functions: DecodeDifferent::Encode(&[
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("U32"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructU32(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[ " Hello, this is doc!" ]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBU32"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBU32(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("U32MYDEF"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructU32MYDEF(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBU32MYDEF"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBU32MYDEF(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("GETU32"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("T::Origin")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructGETU32(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBGETU32"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBGETU32(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("GETU32WITHCONFIG"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructGETU32WITHCONFIG(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBGETU32WITHCONFIG"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBGETU32WITHCONFIG(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("GETU32MYDEF"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructGETU32MYDEF(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBGETU32MYDEF"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBGETU32MYDEF(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("GETU32WITHCONFIGMYDEF"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructGETU32WITHCONFIGMYDEF(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBGETU32WITHCONFIGMYDEF"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBGETU32WITHCONFIGMYDEF(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBGETU32WITHCONFIGMYDEFOPT"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBGETU32WITHCONFIGMYDEFOPT(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},

			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("MAPU32"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Map {
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("String"),
					is_linked: false,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructMAPU32(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBMAPU32"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Map {
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("String"),
					is_linked: false,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBMAPU32(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("MAPU32MYDEF"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Map {
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("String"),
					is_linked: false,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructMAPU32MYDEF(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBMAPU32MYDEF"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Map {
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("String"),
					is_linked: false,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBMAPU32MYDEF(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("GETMAPU32"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Map {
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("String"),
					is_linked: false,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructGETMAPU32(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBGETMAPU32"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Map {
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("String"),
					is_linked: false,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBGETMAPU32(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("GETMAPU32MYDEF"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Map {
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("String"),
					is_linked: false,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructGETMAPU32MYDEF(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBGETMAPU32MYDEF"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Map {
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("String"),
					is_linked: false,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBGETMAPU32MYDEF(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("LINKEDMAPU32"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Map {
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("String"),
					is_linked: true,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructLINKEDMAPU32(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBLINKEDMAPU32MYDEF"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Map {
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("String"),
					is_linked: true,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBLINKEDMAPU32MYDEF(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("GETLINKEDMAPU32"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Map {
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("String"),
					is_linked: true,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructGETLINKEDMAPU32(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("PUBGETLINKEDMAPU32MYDEF"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Map {
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("String"),
					is_linked: true,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructPUBGETLINKEDMAPU32MYDEF(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("COMPLEXTYPE1"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("::std::vec::Vec<<T as Trait>::Origin>")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructCOMPLEXTYPE1(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("COMPLEXTYPE2"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("(Vec<Vec<(u16, Box<()>)>>, u32)")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructCOMPLEXTYPE2(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("COMPLEXTYPE3"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Plain(DecodeDifferent::Encode("([u32; 25])")),
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructCOMPLEXTYPE3(PhantomData::<TraitImpl>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
		])
	};

	#[test]
	fn store_metadata() {
		let metadata = Module::<TraitImpl>::store_metadata();
		assert_eq!(EXPECTED_METADATA, metadata);
	}

	#[test]
	fn check_genesis_config() {
		let config = GenesisConfig::<TraitImpl>::default();
		assert_eq!(config.u32_getter_with_config, 0u32);
		assert_eq!(config.pub_u32_getter_with_config, 0u32);

		assert_eq!(config.pub_u32_getter_mydef, 3u32);
		assert_eq!(config.u32_getter_with_config_mydef, 2u32);
		assert_eq!(config.pub_u32_getter_with_config_mydef, 1u32);
		assert_eq!(config.pub_u32_getter_with_config_mydef_opt, 100u32);
	}

}

#[cfg(test)]
#[allow(dead_code)]
mod test2 {
	pub trait Trait {
		type Origin;
		type BlockNumber;
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
	}

	type PairOf<T> = (T, T);

	crate::decl_storage! {
		trait Store for Module<T: Trait> as TestStorage {
			SingleDef : u32;
			PairDef : PairOf<u32>;
			Single : Option<u32>;
			Pair : (u32, u32);
		}
		add_extra_genesis {
			config(_marker) : ::std::marker::PhantomData<T>;
			config(extra_field) : u32 = 32;
			build(|_, _, _| {});
		}
	}

	struct TraitImpl {}

	impl Trait for TraitImpl {
		type Origin = u32;
		type BlockNumber = u32;
	}
}

#[cfg(test)]
#[allow(dead_code)]
mod test3 {
	pub trait Trait {
		type Origin;
		type BlockNumber;
	}
	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
	}
	crate::decl_storage! {
		trait Store for Module<T: Trait> as Test {
			Foo get(foo) config(initial_foo): u32;
		}
	}

	type PairOf<T> = (T, T);

	struct TraitImpl {}

	impl Trait for TraitImpl {
		type Origin = u32;
		type BlockNumber = u32;
	}
}
