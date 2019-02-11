// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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
#![cfg_attr(not(feature = "std"), feature(alloc))]

#[cfg(feature = "std")]
pub use serde;
#[doc(hidden)]
pub use sr_std as rstd;
#[doc(hidden)]
pub use parity_codec as codec;
#[doc(hidden)]
pub use parity_codec_derive;
#[cfg(feature = "std")]
#[doc(hidden)]
pub use once_cell;
#[doc(hidden)]
pub use paste;
pub use sr_primitives as runtime_primitives;

pub use self::storage::generator::Storage as GenericStorage;

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
mod double_map;
pub mod traits;

pub use self::storage::{StorageVec, StorageList, StorageValue, StorageMap, EnumerableStorageMap};
pub use self::hashable::Hashable;
pub use self::dispatch::{Parameter, Dispatchable, Callable, IsSubType};
pub use self::double_map::StorageDoubleMap;
pub use runtime_io::print;

#[doc(inline)]
pub use srml_support_procedural::decl_storage;

#[macro_export]
macro_rules! fail {
	( $y:expr ) => {{
		return Err($y);
	}}
}

#[macro_export]
macro_rules! ensure {
	( $x:expr, $y:expr ) => {{
		if !$x {
			$crate::fail!($y);
		}
	}}
}

#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_noop {
	( $x:expr , $y:expr ) => {
		let h = runtime_io::storage_root();
		$crate::assert_err!($x, $y);
		assert_eq!(h, runtime_io::storage_root());
	}
}

#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_err {
	( $x:expr , $y:expr ) => {
		assert_eq!($x, Err($y));
	}
}

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

/// The void type - it cannot exist.
// Oh rust, you crack me up...
#[derive(Clone, Eq, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Void {}

#[cfg(feature = "std")]
#[doc(hidden)]
pub use serde_derive::*;

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
	use runtime_io::{with_externalities, Blake2Hasher};
	use runtime_primitives::BuildStorage;

	pub trait Trait {
		type BlockNumber;
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
			pub Data get(data) build(|_| vec![(15u32, 42u64)]): linked_map u32 => u64;
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
	fn basic_insert_remove_should_work() {
		with_externalities(&mut new_test_ext(), || {
			// initialised during genesis
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
	fn enumeration_and_head_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Map::head(), None);
			assert_eq!(Map::enumerate().collect::<Vec<_>>(), vec![]);
			// insert / remove
			let key = 17u32;
			Map::insert(key, 4u64);
			assert_eq!(Map::head(), Some(key));
			assert_eq!(Map::enumerate().collect::<Vec<_>>(), vec![(key, 4)]);
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

}
