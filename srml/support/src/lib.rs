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

//! Support code for the runtime.

#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
extern crate bitmask;

#[cfg(feature = "std")]
pub use serde;
#[doc(hidden)]
pub use sr_std as rstd;
#[doc(hidden)]
pub use codec;
#[cfg(feature = "std")]
#[doc(hidden)]
pub use once_cell;
#[doc(hidden)]
pub use paste;
pub use sr_primitives as runtime_primitives;

pub use self::storage::hashed::generator::{HashedStorage, Twox256, Twox128, Blake2_256, Blake2_128, Twox64Concat};
pub use self::storage::unhashed::generator::UnhashedStorage;

#[macro_use]
pub mod dispatch;
#[macro_use]
pub mod storage;
mod hashable;
#[macro_use]
pub mod event;
#[macro_use]
mod origin;
#[macro_use]
pub mod metadata;
#[macro_use]
mod runtime;
#[macro_use]
pub mod inherent;
#[macro_use]
pub mod unsigned;
mod double_map;
pub mod traits;

pub use self::storage::{
	StorageValue, StorageMap, EnumerableStorageMap, StorageDoubleMap, AppendableStorageMap
};
pub use self::hashable::Hashable;
pub use self::dispatch::{Parameter, Dispatchable, Callable, IsSubType};
pub use self::double_map::StorageDoubleMapWithHasher;
pub use runtime_io::{print, storage_root};

/// Macro for easily creating a new implementation of the `Get` trait. Use similarly to
/// how you would declare a `const`:
///
/// ```no_compile
/// parameter_types! {
///   pub const Argument: u64 = 42;
/// }
/// trait Config {
///   type Parameter: Get<u64>;
/// }
/// struct Runtime;
/// impl Config for Runtime {
///   type Parameter = Argument;
/// }
/// ```
#[macro_export]
macro_rules! parameter_types {
	(pub const $name:ident: $type:ty = $value:expr; $( $rest:tt )*) => (
		pub struct $name;
		$crate::parameter_types!{IMPL $name , $type , $value}
		$crate::parameter_types!{ $( $rest )* }
	);
	(const $name:ident: $type:ty = $value:expr; $( $rest:tt )*) => (
		struct $name;
		$crate::parameter_types!{IMPL $name , $type , $value}
		$crate::parameter_types!{ $( $rest )* }
	);
	() => ();
	(IMPL $name:ident , $type:ty , $value:expr) => {
		impl $crate::traits::Get<$type> for $name { fn get() -> $type { $value } }
	}
}

#[doc(inline)]
pub use srml_support_procedural::decl_storage;

/// Return Err of the expression: `return Err($expression);`.
///
/// Used as `fail!(expression)`.
#[macro_export]
macro_rules! fail {
	( $y:expr ) => {{
		return Err($y);
	}}
}

/// Evaluate `$x:expr` and if not true return `Err($y:expr)`.
///
/// Used as `ensure!(expression_to_ensure, expression_to_return_on_false)`.
#[macro_export]
macro_rules! ensure {
	( $x:expr, $y:expr ) => {{
		if !$x {
			$crate::fail!($y);
		}
	}}
}

/// Evaluate an expression, assert it returns an expected `Err` value and that
/// runtime storage has not been mutated (i.e. expression is a no-operation).
///
/// Used as `assert_noop(expression_to_assert, expected_error_expression)`.
#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_noop {
	( $x:expr , $y:expr ) => {
		let h = $crate::storage_root();
		$crate::assert_err!($x, $y);
		assert_eq!(h, $crate::storage_root());
	}
}

/// Panic if an expression doesn't evaluate to an `Err`.
///
/// Used as `assert_err!(expression_to_assert, expected_err_expression)`.

/// Assert an expression returns an error specified.
///
/// Used as `assert_err!(expression_to_assert, expected_error_expression)`
#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_err {
	( $x:expr , $y:expr ) => {
		assert_eq!($x, Err($y));
	}
}

/// Panic if an expression doesn't evaluate to `Ok`.
///
/// Used as `assert_ok!(expression_to_assert, expected_ok_expression)`,
/// or `assert_ok!(expression_to_assert)` which would assert against `Ok(())`.
#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_ok {
	( $x:expr ) => {
		assert_eq!($x, Ok(()));
	};
	( $x:expr, $y:expr ) => {
		assert_eq!($x, Ok($y));
	}
}

/// Panic when the vectors are different, without taking the order into account.
///
/// # Examples
///
/// ```rust
/// #[macro_use]
/// # extern crate srml_support;
/// # use srml_support::{assert_eq_uvec};
/// # fn main() {
/// assert_eq_uvec!(vec![1,2], vec![2,1]);
/// # }
/// ```
///
/// ```rust,should_panic
/// #[macro_use]
/// # extern crate srml_support;
/// # use srml_support::{assert_eq_uvec};
/// # fn main() {
/// assert_eq_uvec!(vec![1,2,3], vec![2,1]);
/// # }
/// ```
#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_eq_uvec {
	( $x:expr, $y:expr ) => {
		$crate::__assert_eq_uvec!($x, $y);
		$crate::__assert_eq_uvec!($y, $x);
	}
}

#[macro_export]
#[doc(hidden)]
#[cfg(feature = "std")]
macro_rules! __assert_eq_uvec {
	( $x:expr, $y:expr ) => {
		$x.iter().for_each(|e| {
			if !$y.contains(e) { panic!(format!("vectors not equal: {:?} != {:?}", $x, $y)); }
		});
	}
}

/// The void type - it cannot exist.
// Oh rust, you crack me up...
#[derive(Clone, Eq, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Void {}

#[cfg(feature = "std")]
#[doc(hidden)]
pub use serde::{Serialize, Deserialize};

/// Programatically create derivations for tuples of up to 19 elements. You provide a second macro
/// which is called once per tuple size, along with a number of identifiers, one for each element
/// of the tuple.
#[macro_export]
macro_rules! for_each_tuple {
	($m:ident) => {
		for_each_tuple! { @IMPL $m !! A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, }
	};
	(@IMPL $m:ident !!) => { $m! { } };
	(@IMPL $m:ident !! $h:ident, $($t:ident,)*) => {
		$m! { $h $($t)* }
		for_each_tuple! { @IMPL $m !! $($t,)* }
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::Codec;
	use runtime_io::{with_externalities, Blake2Hasher};
	use runtime_primitives::BuildStorage;
	pub use srml_metadata::{
		DecodeDifferent, StorageMetadata, StorageFunctionMetadata,
		StorageFunctionType, StorageFunctionModifier,
		DefaultByte, DefaultByteGetter, StorageHasher
	};
	pub use rstd::marker::PhantomData;

	pub trait Trait {
		type BlockNumber: Codec + Default;
		type Origin;
	}

	mod module {
		#![allow(dead_code)]

		use super::Trait;

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {

			}
		}
	}
	use self::module::Module;

	decl_storage! {
		trait Store for Module<T: Trait> as Example {
			pub Data get(data) build(|_| vec![(15u32, 42u64)]): linked_map hasher(twox_64_concat) u32 => u64;
			pub GenericData get(generic_data): linked_map hasher(twox_128) T::BlockNumber => T::BlockNumber;
			pub GenericData2 get(generic_data2): linked_map T::BlockNumber => Option<T::BlockNumber>;

			pub DataDM config(test_config) build(|_| vec![(15u32, 16u32, 42u64)]):
				double_map hasher(twox_64_concat) u32, blake2_256(u32) => u64;
			pub GenericDataDM: double_map T::BlockNumber, twox_128(T::BlockNumber) => T::BlockNumber;
			pub GenericData2DM: double_map T::BlockNumber, twox_256(T::BlockNumber) => Option<T::BlockNumber>;
			pub AppendableDM: double_map u32, blake2_256(T::BlockNumber) => Vec<u32>;
		}
	}

	struct Test;
	impl Trait for Test {
		type BlockNumber = u32;
		type Origin = u32;
	}

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		GenesisConfig::<Test>::default().build_storage().unwrap().0.into()
	}

	type Map = Data<Test>;

	#[test]
	fn linked_map_basic_insert_remove_should_work() {
		with_externalities(&mut new_test_ext(), || {
			// initialized during genesis
			assert_eq!(Map::get(&15u32), 42u64);

			// get / insert / take
			let key = 17u32;
			assert_eq!(Map::get(&key), 0u64);
			Map::insert(key, 4u64);
			assert_eq!(Map::get(&key), 4u64);
			assert_eq!(Map::take(&key), 4u64);
			assert_eq!(Map::get(&key), 0u64);

			// mutate
			Map::mutate(&key, |val| {
				*val = 15;
			});
			assert_eq!(Map::get(&key), 15u64);

			// remove
			Map::remove(&key);
			assert_eq!(Map::get(&key), 0u64);
		});
	}

	#[test]
	fn linked_map_enumeration_and_head_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Map::head(), Some(15));
			assert_eq!(Map::enumerate().collect::<Vec<_>>(), vec![(15, 42)]);
			// insert / remove
			let key = 17u32;
			Map::insert(key, 4u64);
			assert_eq!(Map::head(), Some(key));
			assert_eq!(Map::enumerate().collect::<Vec<_>>(), vec![(key, 4), (15, 42)]);
			assert_eq!(Map::take(&15), 42u64);
			assert_eq!(Map::take(&key), 4u64);
			assert_eq!(Map::head(), None);
			assert_eq!(Map::enumerate().collect::<Vec<_>>(), vec![]);

			// Add couple of more elements
			Map::insert(key, 42u64);
			assert_eq!(Map::head(), Some(key));
			assert_eq!(Map::enumerate().collect::<Vec<_>>(), vec![(key, 42)]);
			Map::insert(key + 1, 43u64);
			assert_eq!(Map::head(), Some(key + 1));
			assert_eq!(Map::enumerate().collect::<Vec<_>>(), vec![(key + 1, 43), (key, 42)]);

			// mutate
			let key = key + 2;
			Map::mutate(&key, |val| {
				*val = 15;
			});
			assert_eq!(Map::enumerate().collect::<Vec<_>>(), vec![(key, 15), (key - 1, 43), (key - 2, 42)]);
			assert_eq!(Map::head(), Some(key));
			Map::mutate(&key, |val| {
				*val = 17;
			});
			assert_eq!(Map::enumerate().collect::<Vec<_>>(), vec![(key, 17), (key - 1, 43), (key - 2, 42)]);

			// remove first
			Map::remove(&key);
			assert_eq!(Map::head(), Some(key - 1));
			assert_eq!(Map::enumerate().collect::<Vec<_>>(), vec![(key - 1, 43), (key - 2, 42)]);

			// remove last from the list
			Map::remove(&(key - 2));
			assert_eq!(Map::head(), Some(key - 1));
			assert_eq!(Map::enumerate().collect::<Vec<_>>(), vec![(key - 1, 43)]);

			// remove the last element
			Map::remove(&(key - 1));
			assert_eq!(Map::head(), None);
			assert_eq!(Map::enumerate().collect::<Vec<_>>(), vec![]);
		});
	}

	#[test]
	fn double_map_basic_insert_remove_remove_prefix_should_work() {
		with_externalities(&mut new_test_ext(), || {
			type DoubleMap = DataDM<Test>;
			// initialized during genesis
			assert_eq!(DoubleMap::get(&15u32, &16u32), 42u64);

			// get / insert / take
			let key1 = 17u32;
			let key2 = 18u32;
			assert_eq!(DoubleMap::get(key1, key2), 0u64);
			DoubleMap::insert(key1, key2, 4u64);
			assert_eq!(DoubleMap::get(key1, key2), 4u64);
			assert_eq!(DoubleMap::take(key1, key2), 4u64);
			assert_eq!(DoubleMap::get(key1, key2), 0u64);

			// mutate
			DoubleMap::mutate(key1, key2, |val| {
				*val = 15;
			});
			assert_eq!(DoubleMap::get(key1, key2), 15u64);

			// remove
			DoubleMap::remove(key1, key2);
			assert_eq!(DoubleMap::get(key1, key2), 0u64);

			// remove prefix
			DoubleMap::insert(key1, key2, 4u64);
			DoubleMap::insert(key1, key2+1, 4u64);
			DoubleMap::insert(key1+1, key2, 4u64);
			DoubleMap::insert(key1+1, key2+1, 4u64);
			DoubleMap::remove_prefix(key1);
			assert_eq!(DoubleMap::get(key1, key2), 0u64);
			assert_eq!(DoubleMap::get(key1, key2+1), 0u64);
			assert_eq!(DoubleMap::get(key1+1, key2), 4u64);
			assert_eq!(DoubleMap::get(key1+1, key2+1), 4u64);

		});
	}

	#[test]
	fn double_map_append_should_work() {
		with_externalities(&mut new_test_ext(), || {
			type DoubleMap = AppendableDM<Test>;

			let key1 = 17u32;
			let key2 = 18u32;

			DoubleMap::insert(key1, key2, vec![1]);
			DoubleMap::append(key1, key2, &[2, 3]).unwrap();
			assert_eq!(DoubleMap::get(key1, key2), vec![1, 2, 3]);
		});
	}

	const EXPECTED_METADATA: StorageMetadata = StorageMetadata {
		functions: DecodeDifferent::Encode(&[
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("Data"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Map{
					hasher: StorageHasher::Twox64Concat,
					key: DecodeDifferent::Encode("u32"), value: DecodeDifferent::Encode("u64"), is_linked: true
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructData(PhantomData::<Test>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("GenericData"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::Map{
					hasher: StorageHasher::Twox128,
					key: DecodeDifferent::Encode("T::BlockNumber"),
					value: DecodeDifferent::Encode("T::BlockNumber"),
					is_linked: true
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructGenericData(PhantomData::<Test>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("GenericData2"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::Map{
					hasher: StorageHasher::Blake2_256,
					key: DecodeDifferent::Encode("T::BlockNumber"),
					value: DecodeDifferent::Encode("T::BlockNumber"),
					is_linked: true
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructGenericData2(PhantomData::<Test>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("DataDM"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::DoubleMap{
					hasher: StorageHasher::Twox64Concat,
					key1: DecodeDifferent::Encode("u32"),
					key2: DecodeDifferent::Encode("u32"),
					value: DecodeDifferent::Encode("u64"),
					key2_hasher: StorageHasher::Blake2_256,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructDataDM(PhantomData::<Test>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("GenericDataDM"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::DoubleMap{
					hasher: StorageHasher::Blake2_256,
					key1: DecodeDifferent::Encode("T::BlockNumber"),
					key2: DecodeDifferent::Encode("T::BlockNumber"),
					value: DecodeDifferent::Encode("T::BlockNumber"),
					key2_hasher: StorageHasher::Twox128,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructGenericDataDM(PhantomData::<Test>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("GenericData2DM"),
				modifier: StorageFunctionModifier::Optional,
				ty: StorageFunctionType::DoubleMap{
					hasher: StorageHasher::Blake2_256,
					key1: DecodeDifferent::Encode("T::BlockNumber"),
					key2: DecodeDifferent::Encode("T::BlockNumber"),
					value: DecodeDifferent::Encode("T::BlockNumber"),
					key2_hasher: StorageHasher::Twox256,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructGenericData2DM(PhantomData::<Test>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
			StorageFunctionMetadata {
				name: DecodeDifferent::Encode("AppendableDM"),
				modifier: StorageFunctionModifier::Default,
				ty: StorageFunctionType::DoubleMap{
					hasher: StorageHasher::Blake2_256,
					key1: DecodeDifferent::Encode("u32"),
					key2: DecodeDifferent::Encode("T::BlockNumber"),
					value: DecodeDifferent::Encode("Vec<u32>"),
					key2_hasher: StorageHasher::Blake2_256,
				},
				default: DecodeDifferent::Encode(
					DefaultByteGetter(&__GetByteStructGenericData2DM(PhantomData::<Test>))
				),
				documentation: DecodeDifferent::Encode(&[]),
			},
		])
	};

	#[test]
	fn store_metadata() {
		let metadata = Module::<Test>::store_metadata();
		assert_eq!(EXPECTED_METADATA, metadata);
	}
}
