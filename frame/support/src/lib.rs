// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Support code for the runtime.

#![cfg_attr(not(feature = "std"), no_std)]

/// Export ourself as `frame_support` to make tests happy.
extern crate self as frame_support;

#[macro_use]
extern crate bitmask;

#[doc(hidden)]
pub use sp_tracing;

#[cfg(feature = "std")]
pub use serde;
pub use sp_core::Void;
#[doc(hidden)]
pub use sp_std;
#[doc(hidden)]
pub use codec;
#[cfg(feature = "std")]
#[doc(hidden)]
pub use once_cell;
#[doc(hidden)]
pub use paste;
#[cfg(feature = "std")]
#[doc(hidden)]
pub use sp_state_machine::BasicExternalities;
#[doc(hidden)]
pub use sp_io::{storage::root as storage_root, self};
#[doc(hidden)]
pub use sp_runtime::RuntimeDebug;

#[macro_use]
pub mod debug;
#[macro_use]
mod origin;
#[macro_use]
pub mod dispatch;
pub mod storage;
mod hash;
#[macro_use]
pub mod event;
#[macro_use]
pub mod metadata;
#[macro_use]
pub mod inherent;
#[macro_use]
pub mod unsigned;
#[macro_use]
pub mod error;
pub mod traits;
pub mod weights;

pub use self::hash::{
	Twox256, Twox128, Blake2_256, Blake2_128, Identity, Twox64Concat, Blake2_128Concat, Hashable,
	StorageHasher, ReversibleStorageHasher
};
pub use self::storage::{
	StorageValue, StorageMap, StorageDoubleMap, StoragePrefixedMap, IterableStorageMap,
	IterableStorageDoubleMap, migration
};
pub use self::dispatch::{Parameter, Callable, IsSubType};
pub use sp_runtime::{self, ConsensusEngineId, print, traits::Printable};

/// A type that cannot be instantiated.
#[derive(Debug)]
pub enum Never {}

/// Create new implementations of the [`Get`](crate::traits::Get) trait.
///
/// The so-called parameter type can be created in three different ways:
///
/// - Using `const` to create a parameter type that provides a `const` getter.
///   It is required that the `value` is const.
///
/// - Declare the parameter type without `const` to have more freedom when creating the value.
///
/// - Using `storage` to create a storage parameter type. This type is special as it tries to
///   load the value from the storage under a fixed key. If the value could not be found in the
///   storage, the given default value will be returned. It is required that the value implements
///   [`Encode`](codec::Encode) and [`Decode`](codec::Decode). The key for looking up the value
///   in the storage is built using the following formular:
///
///   `twox_128(":" ++ NAME ++ ":")` where `NAME` is the name that is passed as type name.
///
/// # Examples
///
/// ```
/// # use frame_support::traits::Get;
/// # use frame_support::parameter_types;
/// // This function cannot be used in a const context.
/// fn non_const_expression() -> u64 { 99 }
///
/// const FIXED_VALUE: u64 = 10;
/// parameter_types! {
///    pub const Argument: u64 = 42 + FIXED_VALUE;
///    /// Visibility of the type is optional
///    OtherArgument: u64 = non_const_expression();
///    pub storage StorageArgument: u64 = 5;
/// }
///
/// trait Config {
///    type Parameter: Get<u64>;
///    type OtherParameter: Get<u64>;
///    type StorageParameter: Get<u64>;
/// }
///
/// struct Runtime;
/// impl Config for Runtime {
///    type Parameter = Argument;
///    type OtherParameter = OtherArgument;
///    type StorageParameter = StorageArgument;
/// }
/// ```
///
/// # Invalid example:
///
/// ```compile_fail
/// # use frame_support::traits::Get;
/// # use frame_support::parameter_types;
/// // This function cannot be used in a const context.
/// fn non_const_expression() -> u64 { 99 }
///
/// parameter_types! {
///    pub const Argument: u64 = non_const_expression();
/// }
/// ```

#[macro_export]
macro_rules! parameter_types {
	(
		$( #[ $attr:meta ] )*
		$vis:vis const $name:ident: $type:ty = $value:expr;
		$( $rest:tt )*
	) => (
		$( #[ $attr ] )*
		$vis struct $name;
		$crate::parameter_types!(IMPL_CONST $name , $type , $value);
		$crate::parameter_types!( $( $rest )* );
	);
	(
		$( #[ $attr:meta ] )*
		$vis:vis $name:ident: $type:ty = $value:expr;
		$( $rest:tt )*
	) => (
		$( #[ $attr ] )*
		$vis struct $name;
		$crate::parameter_types!(IMPL $name, $type, $value);
		$crate::parameter_types!( $( $rest )* );
	);
	(
		$( #[ $attr:meta ] )*
		$vis:vis storage $name:ident: $type:ty = $value:expr;
		$( $rest:tt )*
	) => (
		$( #[ $attr ] )*
		$vis struct $name;
		$crate::parameter_types!(IMPL_STORAGE $name, $type, $value);
		$crate::parameter_types!( $( $rest )* );
	);
	() => ();
	(IMPL_CONST $name:ident, $type:ty, $value:expr) => {
		impl $name {
			/// Returns the value of this parameter type.
			pub const fn get() -> $type {
				$value
			}
		}

		impl<I: From<$type>> $crate::traits::Get<I> for $name {
			fn get() -> I {
				I::from($value)
			}
		}
	};
	(IMPL $name:ident, $type:ty, $value:expr) => {
		impl $name {
			/// Returns the value of this parameter type.
			pub fn get() -> $type {
				$value
			}
		}

		impl<I: From<$type>> $crate::traits::Get<I> for $name {
			fn get() -> I {
				I::from($value)
			}
		}
	};
	(IMPL_STORAGE $name:ident, $type:ty, $value:expr) => {
		impl $name {
			/// Returns the key for this parameter type.
			pub fn key() -> [u8; 16] {
				$crate::sp_io::hashing::twox_128(
					concat!(":", stringify!($name), ":").as_bytes()
				)
			}

			/// Set the value of this parameter type in the storage.
			///
			/// This needs to be executed in an externalities provided
			/// environment.
			pub fn set(value: &$type) {
				$crate::storage::unhashed::put(&Self::key(), value);
			}

			/// Returns the value of this parameter type.
			///
			/// This needs to be executed in an externalities provided
			/// environment.
			pub fn get() -> $type {
				$crate::storage::unhashed::get(&Self::key()).unwrap_or_else(|| $value)
			}
		}

		impl<I: From<$type>> $crate::traits::Get<I> for $name {
			fn get() -> I {
				I::from(Self::get())
			}
		}
	}
}

/// Macro for easily creating a new implementation of both the `Get` and `Contains` traits. Use
/// exactly as with `parameter_types`, only the type must be `Ord`.
#[macro_export]
macro_rules! ord_parameter_types {
	(
		$( #[ $attr:meta ] )*
		$vis:vis const $name:ident: $type:ty = $value:expr;
		$( $rest:tt )*
	) => (
		$( #[ $attr ] )*
		$vis struct $name;
		$crate::parameter_types!{IMPL $name , $type , $value}
		$crate::ord_parameter_types!{IMPL $name , $type , $value}
		$crate::ord_parameter_types!{ $( $rest )* }
	);
	() => ();
	(IMPL $name:ident , $type:ty , $value:expr) => {
		impl $crate::traits::Contains<$type> for $name {
			fn contains(t: &$type) -> bool { &$value == t }
			fn sorted_members() -> $crate::sp_std::prelude::Vec<$type> { vec![$value] }
			fn count() -> usize { 1 }
			#[cfg(feature = "runtime-benchmarks")]
			fn add(_: &$type) {}
		}
	}
}

#[doc(inline)]
pub use frame_support_procedural::{decl_storage, construct_runtime, transactional};

/// Return Err of the expression: `return Err($expression);`.
///
/// Used as `fail!(expression)`.
#[macro_export]
macro_rules! fail {
	( $y:expr ) => {{
		return Err($y.into());
	}}
}

/// Evaluate `$x:expr` and if not true return `Err($y:expr)`.
///
/// Used as `ensure!(expression_to_ensure, expression_to_return_on_false)`.
#[macro_export]
macro_rules! ensure {
	( $x:expr, $y:expr $(,)? ) => {{
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
	(
		$x:expr,
		$y:expr $(,)?
	) => {
		let h = $crate::storage_root();
		$crate::assert_err!($x, $y);
		assert_eq!(h, $crate::storage_root());
	}
}

/// Assert an expression returns an error specified.
///
/// Used as `assert_err!(expression_to_assert, expected_error_expression)`
#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_err {
	( $x:expr , $y:expr $(,)? ) => {
		assert_eq!($x, Err($y.into()));
	}
}

/// Assert an expression returns an error specified.
///
/// This can be used on`DispatchResultWithPostInfo` when the post info should
/// be ignored.
#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_err_ignore_postinfo {
	( $x:expr , $y:expr $(,)? ) => {
		$crate::assert_err!($x.map(|_| ()).map_err(|e| e.error), $y);
	}
}

/// Assert an expression returns error with the given weight.
#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_err_with_weight {
	($call:expr, $err:expr, $weight:expr $(,)? ) => {
		if let Err(dispatch_err_with_post) = $call {
			$crate::assert_err!($call.map(|_| ()).map_err(|e| e.error), $err);
			assert_eq!(dispatch_err_with_post.post_info.actual_weight, $weight.into());
		} else {
			panic!("expected Err(_), got Ok(_).")
		}
	}
}

/// Panic if an expression doesn't evaluate to `Ok`.
///
/// Used as `assert_ok!(expression_to_assert, expected_ok_expression)`,
/// or `assert_ok!(expression_to_assert)` which would assert against `Ok(())`.
#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_ok {
	( $x:expr $(,)? ) => {
		let is = $x;
		match is {
			Ok(_) => (),
			_ => assert!(false, "Expected Ok(_). Got {:#?}", is),
		}
	};
	( $x:expr, $y:expr $(,)? ) => {
		assert_eq!($x, Ok($y));
	}
}

#[cfg(feature = "std")]
#[doc(hidden)]
pub use serde::{Serialize, Deserialize};

#[cfg(test)]
mod tests {
	use super::*;
	use codec::{Codec, EncodeLike};
	use frame_metadata::{
		DecodeDifferent, StorageEntryMetadata, StorageMetadata, StorageEntryType,
		StorageEntryModifier, DefaultByteGetter, StorageHasher,
	};
	use sp_std::{marker::PhantomData, result};
	use sp_io::TestExternalities;

	pub trait Trait {
		type BlockNumber: Codec + EncodeLike + Default;
		type Origin;
	}

	mod module {
		#![allow(dead_code)]

		use super::Trait;

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
		}
	}
	use self::module::Module;

	decl_storage! {
		trait Store for Module<T: Trait> as Test {
			pub Data get(fn data) build(|_| vec![(15u32, 42u64)]):
				map hasher(twox_64_concat) u32 => u64;
			pub OptionLinkedMap: map hasher(blake2_128_concat) u32 => Option<u32>;
			pub GenericData get(fn generic_data):
				map hasher(identity) T::BlockNumber => T::BlockNumber;
			pub GenericData2 get(fn generic_data2):
				map hasher(blake2_128_concat) T::BlockNumber => Option<T::BlockNumber>;
			pub DataDM config(test_config) build(|_| vec![(15u32, 16u32, 42u64)]):
				double_map hasher(twox_64_concat) u32, hasher(blake2_128_concat) u32 => u64;
			pub GenericDataDM:
				double_map hasher(blake2_128_concat) T::BlockNumber, hasher(identity) T::BlockNumber
				=> T::BlockNumber;
			pub GenericData2DM:
				double_map hasher(blake2_128_concat) T::BlockNumber, hasher(twox_64_concat) T::BlockNumber
				=> Option<T::BlockNumber>;
			pub AppendableDM:
				double_map hasher(blake2_128_concat) u32, hasher(blake2_128_concat) T::BlockNumber => Vec<u32>;
		}
	}

	struct Test;
	impl Trait for Test {
		type BlockNumber = u32;
		type Origin = u32;
	}

	fn new_test_ext() -> TestExternalities {
		GenesisConfig::default().build_storage().unwrap().into()
	}

	type Map = Data;

	trait Sorted { fn sorted(self) -> Self; }
	impl<T: Ord> Sorted for Vec<T> {
		fn sorted(mut self) -> Self {
			self.sort();
			self
		}
	}

	#[test]
	fn map_issue_3318() {
		new_test_ext().execute_with(|| {
			OptionLinkedMap::insert(1, 1);
			assert_eq!(OptionLinkedMap::get(1), Some(1));
			OptionLinkedMap::insert(1, 2);
			assert_eq!(OptionLinkedMap::get(1), Some(2));
		});
	}

	#[test]
	fn map_swap_works() {
		new_test_ext().execute_with(|| {
			OptionLinkedMap::insert(0, 0);
			OptionLinkedMap::insert(1, 1);
			OptionLinkedMap::insert(2, 2);
			OptionLinkedMap::insert(3, 3);

			let collect = || OptionLinkedMap::iter().collect::<Vec<_>>().sorted();
			assert_eq!(collect(), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);

			// Two existing
			OptionLinkedMap::swap(1, 2);
			assert_eq!(collect(), vec![(0, 0), (1, 2), (2, 1), (3, 3)]);

			// Back to normal
			OptionLinkedMap::swap(2, 1);
			assert_eq!(collect(), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);

			// Left existing
			OptionLinkedMap::swap(2, 5);
			assert_eq!(collect(), vec![(0, 0), (1, 1), (3, 3), (5, 2)]);

			// Right existing
			OptionLinkedMap::swap(5, 2);
			assert_eq!(collect(), vec![(0, 0), (1, 1), (2, 2), (3, 3)]);
		});
	}

	#[test]
	fn double_map_swap_works() {
		new_test_ext().execute_with(|| {
			DataDM::insert(0, 1, 1);
			DataDM::insert(1, 0, 2);
			DataDM::insert(1, 1, 3);

			let get_all = || vec![
				DataDM::get(0, 1),
				DataDM::get(1, 0),
				DataDM::get(1, 1),
				DataDM::get(2, 0),
				DataDM::get(2, 1),
			];
			assert_eq!(get_all(), vec![1, 2, 3, 0, 0]);

			// Two existing
			DataDM::swap(0, 1, 1, 0);
			assert_eq!(get_all(), vec![2, 1, 3, 0, 0]);

			// Left existing
			DataDM::swap(1, 0, 2, 0);
			assert_eq!(get_all(), vec![2, 0, 3, 1, 0]);

			// Right existing
			DataDM::swap(2, 1, 1, 1);
			assert_eq!(get_all(), vec![2, 0, 0, 1, 3]);
		});
	}

	#[test]
	fn map_basic_insert_remove_should_work() {
		new_test_ext().execute_with(|| {
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
	fn map_iteration_should_work() {
		new_test_ext().execute_with(|| {
			assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(15, 42)]);
			// insert / remove
			let key = 17u32;
			Map::insert(key, 4u64);
			assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(15, 42), (key, 4)]);
			assert_eq!(Map::take(&15), 42u64);
			assert_eq!(Map::take(&key), 4u64);
			assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![]);

			// Add couple of more elements
			Map::insert(key, 42u64);
			assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(key, 42)]);
			Map::insert(key + 1, 43u64);
			assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(key, 42), (key + 1, 43)]);

			// mutate
			let key = key + 2;
			Map::mutate(&key, |val| {
				*val = 15;
			});
			assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(key - 2, 42), (key - 1, 43), (key, 15)]);
			Map::mutate(&key, |val| {
				*val = 17;
			});
			assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(key - 2, 42), (key - 1, 43), (key, 17)]);

			// remove first
			Map::remove(&key);
			assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(key - 2, 42), (key - 1, 43)]);

			// remove last from the list
			Map::remove(&(key - 2));
			assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![(key - 1, 43)]);

			// remove the last element
			Map::remove(&(key - 1));
			assert_eq!(Map::iter().collect::<Vec<_>>().sorted(), vec![]);
		});
	}

	#[test]
	fn double_map_basic_insert_remove_remove_prefix_should_work() {
		new_test_ext().execute_with(|| {
			type DoubleMap = DataDM;
			// initialized during genesis
			assert_eq!(DoubleMap::get(&15u32, &16u32), 42u64);

			// get / insert / take
			let key1 = 17u32;
			let key2 = 18u32;
			assert_eq!(DoubleMap::get(&key1, &key2), 0u64);
			DoubleMap::insert(&key1, &key2, &4u64);
			assert_eq!(DoubleMap::get(&key1, &key2), 4u64);
			assert_eq!(DoubleMap::take(&key1, &key2), 4u64);
			assert_eq!(DoubleMap::get(&key1, &key2), 0u64);

			// mutate
			DoubleMap::mutate(&key1, &key2, |val| {
				*val = 15;
			});
			assert_eq!(DoubleMap::get(&key1, &key2), 15u64);

			// remove
			DoubleMap::remove(&key1, &key2);
			assert_eq!(DoubleMap::get(&key1, &key2), 0u64);

			// remove prefix
			DoubleMap::insert(&key1, &key2, &4u64);
			DoubleMap::insert(&key1, &(key2 + 1), &4u64);
			DoubleMap::insert(&(key1 + 1), &key2, &4u64);
			DoubleMap::insert(&(key1 + 1), &(key2 + 1), &4u64);
			DoubleMap::remove_prefix(&key1);
			assert_eq!(DoubleMap::get(&key1, &key2), 0u64);
			assert_eq!(DoubleMap::get(&key1, &(key2 + 1)), 0u64);
			assert_eq!(DoubleMap::get(&(key1 + 1), &key2), 4u64);
			assert_eq!(DoubleMap::get(&(key1 + 1), &(key2 + 1)), 4u64);

		});
	}

	#[test]
	fn double_map_append_should_work() {
		new_test_ext().execute_with(|| {
			type DoubleMap = AppendableDM<Test>;

			let key1 = 17u32;
			let key2 = 18u32;

			DoubleMap::insert(&key1, &key2, &vec![1]);
			DoubleMap::append(&key1, &key2, 2);
			assert_eq!(DoubleMap::get(&key1, &key2), &[1, 2]);
		});
	}

	#[test]
	fn double_map_mutate_exists_should_work() {
		new_test_ext().execute_with(|| {
			type DoubleMap = DataDM;

			let (key1, key2) = (11, 13);

			// mutated
			DoubleMap::mutate_exists(key1, key2, |v| *v = Some(1));
			assert_eq!(DoubleMap::get(&key1, key2), 1);

			// removed if mutated to `None`
			DoubleMap::mutate_exists(key1, key2, |v| *v = None);
			assert!(!DoubleMap::contains_key(&key1, key2));
		});
	}

	#[test]
	fn double_map_try_mutate_exists_should_work() {
		new_test_ext().execute_with(|| {
			type DoubleMap = DataDM;
			type TestResult = result::Result<(), &'static str>;

			let (key1, key2) = (11, 13);

			// mutated if `Ok`
			assert_ok!(DoubleMap::try_mutate_exists(key1, key2, |v| -> TestResult {
				*v = Some(1);
				Ok(())
			}));
			assert_eq!(DoubleMap::get(&key1, key2), 1);

			// no-op if `Err`
			assert_noop!(DoubleMap::try_mutate_exists(key1, key2, |v| -> TestResult {
				*v = Some(2);
				Err("nah")
			}), "nah");

			// removed if mutated to`None`
			assert_ok!(DoubleMap::try_mutate_exists(key1, key2, |v| -> TestResult {
				*v = None;
				Ok(())
			}));
			assert!(!DoubleMap::contains_key(&key1, key2));
		});
	}

	const EXPECTED_METADATA: StorageMetadata = StorageMetadata {
		prefix: DecodeDifferent::Encode("Test"),
		entries: DecodeDifferent::Encode(
			&[
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("Data"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Map{
						hasher: StorageHasher::Twox64Concat,
						key: DecodeDifferent::Encode("u32"),
						value: DecodeDifferent::Encode("u64"),
						unused: false,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructData(PhantomData::<Test>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("OptionLinkedMap"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map {
						hasher: StorageHasher::Blake2_128Concat,
						key: DecodeDifferent::Encode("u32"),
						value: DecodeDifferent::Encode("u32"),
						unused: false,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructOptionLinkedMap(PhantomData::<Test>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GenericData"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::Map{
						hasher: StorageHasher::Identity,
						key: DecodeDifferent::Encode("T::BlockNumber"),
						value: DecodeDifferent::Encode("T::BlockNumber"),
						unused: false
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGenericData(PhantomData::<Test>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GenericData2"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::Map{
						hasher: StorageHasher::Blake2_128Concat,
						key: DecodeDifferent::Encode("T::BlockNumber"),
						value: DecodeDifferent::Encode("T::BlockNumber"),
						unused: false
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGenericData2(PhantomData::<Test>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("DataDM"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::DoubleMap{
						hasher: StorageHasher::Twox64Concat,
						key1: DecodeDifferent::Encode("u32"),
						key2: DecodeDifferent::Encode("u32"),
						value: DecodeDifferent::Encode("u64"),
						key2_hasher: StorageHasher::Blake2_128Concat,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructDataDM(PhantomData::<Test>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GenericDataDM"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::DoubleMap{
						hasher: StorageHasher::Blake2_128Concat,
						key1: DecodeDifferent::Encode("T::BlockNumber"),
						key2: DecodeDifferent::Encode("T::BlockNumber"),
						value: DecodeDifferent::Encode("T::BlockNumber"),
						key2_hasher: StorageHasher::Identity,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGenericDataDM(PhantomData::<Test>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("GenericData2DM"),
					modifier: StorageEntryModifier::Optional,
					ty: StorageEntryType::DoubleMap{
						hasher: StorageHasher::Blake2_128Concat,
						key1: DecodeDifferent::Encode("T::BlockNumber"),
						key2: DecodeDifferent::Encode("T::BlockNumber"),
						value: DecodeDifferent::Encode("T::BlockNumber"),
						key2_hasher: StorageHasher::Twox64Concat,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGenericData2DM(PhantomData::<Test>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
				StorageEntryMetadata {
					name: DecodeDifferent::Encode("AppendableDM"),
					modifier: StorageEntryModifier::Default,
					ty: StorageEntryType::DoubleMap{
						hasher: StorageHasher::Blake2_128Concat,
						key1: DecodeDifferent::Encode("u32"),
						key2: DecodeDifferent::Encode("T::BlockNumber"),
						value: DecodeDifferent::Encode("Vec<u32>"),
						key2_hasher: StorageHasher::Blake2_128Concat,
					},
					default: DecodeDifferent::Encode(
						DefaultByteGetter(&__GetByteStructGenericData2DM(PhantomData::<Test>))
					),
					documentation: DecodeDifferent::Encode(&[]),
				},
			]
		),
	};

	#[test]
	fn store_metadata() {
		let metadata = Module::<Test>::storage_metadata();
		pretty_assertions::assert_eq!(EXPECTED_METADATA, metadata);
	}

	parameter_types! {
		storage StorageParameter: u64 = 10;
	}

	#[test]
	fn check_storage_parameter_type_works() {
		TestExternalities::default().execute_with(|| {
			assert_eq!(sp_io::hashing::twox_128(b":StorageParameter:"), StorageParameter::key());

			assert_eq!(10, StorageParameter::get());

			StorageParameter::set(&300);
			assert_eq!(300, StorageParameter::get());
		})
	}
}
